package nl.tue.parkinglot;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import org.eclipse.leshan.core.model.ObjectLoader;
import org.eclipse.leshan.core.model.ObjectModel;
import org.eclipse.leshan.core.observation.Observation;
import org.eclipse.leshan.core.request.ObserveRequest;
import org.eclipse.leshan.core.request.ReadRequest;
import org.eclipse.leshan.core.response.ObserveResponse;
import org.eclipse.leshan.core.response.ReadResponse;
import org.eclipse.leshan.core.response.WriteResponse;
import org.eclipse.leshan.server.californium.LeshanServer;
import org.eclipse.leshan.server.californium.LeshanServerBuilder;
import org.eclipse.leshan.server.model.LwM2mModelProvider;
import org.eclipse.leshan.server.model.VersionedModelProvider;
import org.eclipse.leshan.server.observation.ObservationListener;
import org.eclipse.leshan.server.registration.Registration;
import org.eclipse.leshan.server.registration.RegistrationListener;
import org.eclipse.leshan.server.registration.RegistrationUpdate;
import org.eclipse.leshan.core.node.LwM2mObjectInstance;
import org.eclipse.leshan.core.request.ContentFormat;
import org.eclipse.leshan.core.request.WriteRequest;

public class LwM2MServer {
  ConcurrentHashMap<String, String> regToParkingId = new ConcurrentHashMap<>();
  ConcurrentHashMap<String, String> regToVehicleCounterId = new ConcurrentHashMap<>();

  ConcurrentHashMap<String, ParkingSpot> parkingSpots = new ConcurrentHashMap<>();
  ConcurrentHashMap<String, VehicleCounter> vehicleCounters = new ConcurrentHashMap<>();

  final String parkingLotName;
  final LeshanServer server;

  public LwM2MServer(String parkingLotName) {
    this.parkingLotName = parkingLotName;
    this.server = buildServer();
  }

  public void start() {
    this.server.start();
  }

  public Collection<ParkingSpot> getParkingSpots() {
    return parkingSpots.values();
  }

  public Collection<VehicleCounter> getVehicleCounters() {
    return vehicleCounters.values();
  }

  private LeshanServer buildServer() {
    LeshanServerBuilder builder = new LeshanServerBuilder();

    List<ObjectModel> models = ObjectLoader.loadDefault();
    models.addAll(
        ObjectLoader.loadDdfResources("/models/", new String[] { "32800.xml", "32801.xml" }));

    LwM2mModelProvider modelProvider = new VersionedModelProvider(models);
    builder.setObjectModelProvider(modelProvider);

    final LeshanServer server = builder.build();

    server.getRegistrationService().addListener(registrationListener);
    server.getObservationService().addListener(observationListener);

    return server;
  }

  private final RegistrationListener registrationListener = new RegistrationListener() {
    public void registered(Registration registration, Registration previousReg,
        Collection<Observation> previousObsersations) {
      Map<Integer, String> supportedObjects = registration.getSupportedObject();

      if (supportedObjects.containsKey(32800)) {
        addParkingSpotRegistration(registration);
      }

      if (supportedObjects.containsKey(32801)) {
        addVehicleCounterRegistration(registration);
      }
    }

    public void updated(RegistrationUpdate update, Registration updatedReg, Registration previousReg) {
      String prevRegId = previousReg.getId();
      String regId = updatedReg.getId();

      if (!regId.equals(prevRegId)) {
        // TODO: do something?
        System.out.println("Registration changed ID from " + prevRegId + " to " + regId);
        System.out.println(update.getAdditionalAttributes());
      }
    }

    public void unregistered(Registration registration, Collection<Observation> observations, boolean expired,
        Registration newReg) {
      // NOTE: observations are passively canceled.

      String regId = registration.getId();

      ParkingSpot ps = getParkingSpot(registration);
      if (ps != null) {
        regToParkingId.remove(regId);
        parkingSpots.remove(ps.getId());
        System.out.println("Removed parking spot from " + registration.getEndpoint() + ": " + ps.getId());
      }

      VehicleCounter vc = getVehicleCounter(registration);
      if (vc != null) {
        regToVehicleCounterId.remove(regId);
        vehicleCounters.remove(vc.getId());
        System.out.println("Removed vehicle counter from " + registration.getEndpoint() + ": " + vc.getId());
      }
    }
  };

  private final ObservationListener observationListener = new ObservationListener() {
    public void newObservation(Observation observation, Registration registration) {
      // Do nothing.
    }

    public void cancelled(Observation observation) {
      // Do nothing.
    }

    public void onResponse(Observation observation, Registration registration, ObserveResponse response) {
      String path = observation.getPath().toString();

      if (path.startsWith("/32800/")) {
        updateParkingSpot(registration, response);
      } else if (path.startsWith("/32801/")) {
        updateVehicleRegistration(registration, response);
      }
    }

    public void onError(Observation observation, Registration registration, Exception error) {
      System.out.println("Unable to process observation");
      error.printStackTrace();
    }
  };

  private void addParkingSpotRegistration(Registration reg) {
    ReadResponse res;

    try {
      res = server.send(reg, new ReadRequest(32800, 0));

      if (!res.isSuccess()) {
        System.out.println("Read request was not successfull");
        return;
      }

      LwM2mObjectInstance i = (LwM2mObjectInstance) res.getContent();

      String id = (String) i.getResource(32700).getValue();
      String state = (String) i.getResource(32701).getValue();
      String vehicle = (String) i.getResource(32702).getValue();

      ParkingSpot ps = new ParkingSpot(id);
      ps.setState(state);
      ps.setVehicle(vehicle);

      parkingSpots.put(ps.getId(), ps);
      regToParkingId.put(reg.getId(), ps.getId());

      System.out.println("Added parking spot from " + reg.getEndpoint() + ": " + ps.getId());

      ObserveResponse ores = server.send(reg, new ObserveRequest(32800, 0));
      if (!ores.isSuccess()) {
        System.out.println("Starting observations not successfull.");
      }

      WriteResponse wres = server.send(reg, new WriteRequest(ContentFormat.TEXT, 32800, 0, 32706, parkingLotName));
      if (!wres.isSuccess()) {
        System.out.println("Writing parking lot name request was not successfull.");
      }
    } catch (InterruptedException e) {
      System.out.println("Read request was not successfull.");
      e.printStackTrace();
    }
  }

  private ParkingSpot getParkingSpot(Registration reg) {
    String regId = reg.getId();
    String psId = regToParkingId.get(regId);
    if (psId == null) {
      return null;
    }

    return parkingSpots.get(psId);
  }

  private void updateParkingSpot(Registration reg, ObserveResponse response) {
    // TODO: investigate which fields we actually need and add observations only for
    // those.
    LwM2mObjectInstance i = (LwM2mObjectInstance) response.getContent();

    String state = (String) i.getResource(32701).getValue();
    String vehicle = (String) i.getResource(32702).getValue();

    ParkingSpot ps = getParkingSpot(reg);
    if (ps == null) {
      System.out.println("Parking spot not found for observation.");
      return;
    }

    ps.setState(state);
    ps.setVehicle(vehicle);
  }

  private void addVehicleCounterRegistration(Registration reg) {
    ReadResponse res;

    try {
      res = server.send(reg, new ReadRequest(32801, 0));

      if (!res.isSuccess()) {
        System.out.println("Read request was not successfull");
        return;
      }

      LwM2mObjectInstance i = (LwM2mObjectInstance) res.getContent();

      String id = (String) i.getResource(32700).getValue();
      Long counter = (Long) i.getResource(32703).getValue();
      String lastPlate = (String) i.getResource(32704).getValue();
      Long direction = (Long) i.getResource(32705).getValue();

      VehicleCounter vc = new VehicleCounter(id);
      vc.setCounter(counter);
      vc.setLastPlate(lastPlate);
      vc.setDirection(direction);

      vehicleCounters.put(vc.getId(), vc);
      regToVehicleCounterId.put(reg.getId(), vc.getId());

      System.out.println("Added vehicle counter from " + reg.getEndpoint() + ": " + vc.getId());

      ObserveResponse ores = server.send(reg, new ObserveRequest(32801, 0));
      if (!ores.isSuccess()) {
        System.out.println("Starting observations not successfull.");
      }

      WriteResponse wres = server.send(reg, new WriteRequest(ContentFormat.TEXT, 32801, 0, 32706, parkingLotName));
      if (!wres.isSuccess()) {
        System.out.println("Writing parking lot name request was not successfull.");
      }
    } catch (InterruptedException e) {
      System.out.println("Read request was not successfull.");
      e.printStackTrace();
    }
  }

  private VehicleCounter getVehicleCounter(Registration reg) {
    String regId = reg.getId();
    String vcId = regToVehicleCounterId.get(regId);
    if (vcId == null) {
      return null;
    }

    return vehicleCounters.get(vcId);
  }

  private void updateVehicleRegistration(Registration reg, ObserveResponse response) {
    // TODO: investigate which fields we actually need and add observations only for
    // those.
    LwM2mObjectInstance i = (LwM2mObjectInstance) response.getContent();

    Long counter = (Long) i.getResource(32703).getValue();
    String lastPlate = (String) i.getResource(32704).getValue();
    Long direction = (Long) i.getResource(32705).getValue();

    VehicleCounter vc = getVehicleCounter(reg);
    if (vc == null) {
      System.out.println("Vehicle counter not found for observation.");
      return;
    }

    vc.setCounter(counter);
    vc.setLastPlate(lastPlate);
    vc.setDirection(direction);
  }
}
