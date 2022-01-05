package nl.tue.parkinglot;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import org.eclipse.leshan.core.model.ObjectLoader;
import org.eclipse.leshan.core.model.ObjectModel;
import org.eclipse.leshan.core.observation.Observation;
import org.eclipse.leshan.core.request.exception.InvalidRequestException;
import org.eclipse.leshan.server.californium.LeshanServer;
import org.eclipse.leshan.server.californium.LeshanServerBuilder;
import org.eclipse.leshan.server.model.LwM2mModelProvider;
import org.eclipse.leshan.server.model.VersionedModelProvider;
import org.eclipse.leshan.server.registration.Registration;
import org.eclipse.leshan.server.registration.RegistrationListener;
import org.eclipse.leshan.server.registration.RegistrationUpdate;

public class LwM2MServer {
  ConcurrentHashMap<Registration, ParkingSpot> parkingSpots = new ConcurrentHashMap<>();
  ConcurrentHashMap<Registration, VehicleCounter> vehicleCounters = new ConcurrentHashMap<>();

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

  private LeshanServer buildServer() {
    LeshanServerBuilder builder = new LeshanServerBuilder();

    List<ObjectModel> models = ObjectLoader.loadDefault();
    models.addAll(
        ObjectLoader.loadDdfResources("/models/", new String[] { "32800.xml", "32801.xml" }));

    LwM2mModelProvider modelProvider = new VersionedModelProvider(models);
    builder.setObjectModelProvider(modelProvider);

    final LeshanServer server = builder.build();

    server.getRegistrationService().addListener(new RegistrationListener() {
      public void registered(Registration registration, Registration previousReg,
          Collection<Observation> previousObsersations) {

        Map<Integer, String> supportedObjects = registration.getSupportedObject();

        if (supportedObjects.containsKey(32800)) {
          addParkingSpot(registration);
        }

        if (supportedObjects.containsKey(32801)) {
          addVehicleCounter(registration);
        }
      }

      public void updated(RegistrationUpdate update, Registration updatedReg, Registration previousReg) {
        Map<Integer, String> supportedObjects = updatedReg.getSupportedObject();

        if (supportedObjects.containsKey(32800)) {
          updateParkingSpot(updatedReg, previousReg);
        }

        if (supportedObjects.containsKey(32801)) {
          updateVehicleCounter(updatedReg, previousReg);
        }
      }

      public void unregistered(Registration registration, Collection<Observation> observations, boolean expired,
          Registration newReg) {
        Map<Integer, String> supportedObjects = registration.getSupportedObject();

        if (supportedObjects.containsKey(32800)) {
          parkingSpots.remove(registration);
          System.out.println("Removed parking spot from " + registration.getEndpoint());
        }

        if (supportedObjects.containsKey(32801)) {
          vehicleCounters.remove(registration);
          System.out.println("Removed vehicle counter from " + registration.getEndpoint());
        }
      }
    });

    return server;
  }

  private void addParkingSpot(Registration reg) {
    ParkingSpot ps;
    try {
      ps = new ParkingSpot(reg, server, parkingLotName);
      parkingSpots.put(reg, ps);
      System.out.println("Added parking spot from " + reg.getEndpoint() + ": " + ps.getId());
    } catch (InvalidRequestException | InterruptedException e) {
      e.printStackTrace();
    }
  }

  private void addVehicleCounter(Registration reg) {
    VehicleCounter vc;
    try {
      vc = new VehicleCounter(reg, server, parkingLotName);
      vehicleCounters.put(reg, vc);
      System.out.println("Added vehicle counter from " + reg.getEndpoint() + ": " + vc.getId());
    } catch (InvalidRequestException | InterruptedException e) {
      e.printStackTrace();
    }
  }

  private void updateParkingSpot(Registration updatedReg, Registration previousReg) {
    ParkingSpot ps = parkingSpots.get(previousReg);
    if (ps != null) {
      if (updatedReg != previousReg) {
        parkingSpots.remove(previousReg);
        parkingSpots.put(updatedReg, ps);
      }

      try {
        ps.refresh(updatedReg);
      } catch (InterruptedException e) {
        e.printStackTrace();
      }
      System.out.println("Updated parking spot from " + updatedReg.getEndpoint() + ": " + ps.getId());
    } else {
      System.out.println("Non-existing parking spot from " + updatedReg.getEndpoint());
    }
  }

  private void updateVehicleCounter(Registration updatedReg, Registration previousReg) {
    VehicleCounter vc = vehicleCounters.get(previousReg);
    if (vc != null) {
      if (updatedReg != previousReg) {
        vehicleCounters.remove(previousReg);
        vehicleCounters.put(updatedReg, vc);
      }

      try {
        vc.refresh(updatedReg);
      } catch (InterruptedException e) {
        e.printStackTrace();
      }
      System.out.println("Updated vehicle counter from " + updatedReg.getEndpoint() + ": " + vc.getId());
    } else {
      System.out.println("Non-existing vehicle counter from " + updatedReg.getEndpoint());
    }
  }

}
