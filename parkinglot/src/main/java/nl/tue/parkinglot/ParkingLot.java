package nl.tue.parkinglot;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.ConcurrentHashMap;

import org.eclipse.leshan.core.model.ObjectLoader;
import org.eclipse.leshan.core.model.ObjectModel;
import org.eclipse.leshan.core.observation.Observation;
import org.eclipse.leshan.server.californium.LeshanServer;
import org.eclipse.leshan.server.californium.LeshanServerBuilder;
import org.eclipse.leshan.server.model.LwM2mModelProvider;
import org.eclipse.leshan.server.model.VersionedModelProvider;
import org.eclipse.leshan.server.registration.Registration;
import org.eclipse.leshan.server.registration.RegistrationListener;
import org.eclipse.leshan.server.registration.RegistrationUpdate;

public class ParkingLot {
  final String id, name;
  final double rate;
  final LeshanServer server;

  ConcurrentHashMap<Registration, ParkingSpot> parkingSpots = new ConcurrentHashMap<>();
  ConcurrentHashMap<Registration, VehicleCounter> vehicleCounters = new ConcurrentHashMap<>();

  public ParkingLot(String name, double rate) {
    String id;
    try {
      id = InetAddress.getLocalHost().getHostName() + "-lot";
    } catch (UnknownHostException e) {
      id = "unknown-device-lot";
    }

    this.id = id;
    this.name = name;
    this.rate = rate;

    this.server = this.buildServer();
  };

  public String getId() {
    return id;
  }

  public String getName() {
    return name;
  }

  public int getCapacity() {
    return parkingSpots.size();
  }

  public int getReservations() {
    int reservations = 0;

    for (Registration i : parkingSpots.keySet()) {
      ParkingSpot ps = parkingSpots.getOrDefault(i, null);
      if (ps != null) {
        try {
          if (ps.getState() == "Reserved") {
            reservations++;
          }
        } catch (InterruptedException e) {
          e.printStackTrace();
        }
      }
    }

    return reservations;
  }

  public int getVehicles() {
    int occupations = 0;

    for (Registration i : parkingSpots.keySet()) {
      ParkingSpot ps = parkingSpots.getOrDefault(i, null);
      if (ps != null) {
        try {
          if (ps.getState() == "Occupied") {
            occupations++;
          }
        } catch (InterruptedException e) {
          e.printStackTrace();
        }
      }
    }

    return occupations;
  }

  public int getFree() {
    return this.getCapacity() - this.getReservations() - this.getVehicles();
  }

  public double getRate() {
    return rate;
  }

  public String status() {
    return "Parking Lot Status:\n"
        + "\tID: " + getId() + "\n"
        + "\tName: " + getName() + "\n"
        + "\tCapacity: " + getCapacity() + "\n"
        + "\tReservations: " + getReservations() + "\n"
        + "\tVehicles: " + getVehicles();
  }

  private LeshanServer buildServer() {
    LeshanServerBuilder builder = new LeshanServerBuilder();

    List<ObjectModel> models = ObjectLoader.loadDefault();
    models.addAll(
        ObjectLoader.loadDdfResources("/models/", new String[] { "32800.xml", "32801.xml" }));

    LwM2mModelProvider modelProvider = new VersionedModelProvider(models);
    builder.setObjectModelProvider(modelProvider);

    return builder.build();
  }

  public void start() {
    server.getRegistrationService().addListener(new RegistrationListener() {
      public void registered(Registration registration, Registration previousReg,
          Collection<Observation> previousObsersations) {

        // Each new device (aka. Client) provides both a Parking Spot and a Vehicle
        // Counter.

        ParkingSpot ps = new ParkingSpot(registration, server);
        parkingSpots.put(registration, ps);

        VehicleCounter vc = new VehicleCounter(registration, server);
        vehicleCounters.put(registration, vc);
      }

      public void updated(RegistrationUpdate update, Registration updatedReg, Registration previousReg) {
        System.out.println("device is still here: " + updatedReg.getEndpoint());
      }

      public void unregistered(Registration registration, Collection<Observation> observations, boolean expired,
          Registration newReg) {
        parkingSpots.remove(registration);
      }
    });

    server.start();
  }
}
