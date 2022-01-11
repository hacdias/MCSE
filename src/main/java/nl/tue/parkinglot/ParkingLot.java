package nl.tue.parkinglot;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Map;

public class ParkingLot {
  final String id, name;
  final double rate;
  final LwM2MServer server;

  public Map<String, ParkingSpot> getParkingSpots() {
    return server.getParkingSpotsAsMap();
  }

  public ParkingLot(String name, double rate, Database db) {
    String id;
    try {
      id = InetAddress.getLocalHost().getHostName() + "-lot";
    } catch (UnknownHostException e) {
      id = name.toLowerCase() + "-lot";
    }

    this.id = id;
    this.name = name;
    this.rate = rate;

    this.server = new LwM2MServer(id, name, db);
  };

  public String getId() {
    return id;
  }

  public String getName() {
    return name;
  }

  public int getCapacity() {
    return server.getParkingSpots().size();
  }

  public int getReservations() {
    int reservations = 0;

    for (ParkingSpot ps : server.getParkingSpots()) {
      if (ps.getState().equals("Reserved")) {
        reservations++;
      }
    }

    return reservations;
  }

  public int getVehicles() {
    int occupations = 0;
    for (ParkingSpot ps : server.getParkingSpots()) {
      if (ps.getState().equals("Occupied")) {
        occupations++;
      }
    }

    int carsInPark = 0;
    for (VehicleCounter vh : server.getVehicleCounters()) {
      if (vh.getDirection() == 0) {
        carsInPark -= vh.getCounter();
      } else {
        carsInPark += vh.getCounter();
      }
    }

    // Get the max of occupied parking spots and cars inside the park. That'll give
    // the number of occupied spots.
    return Math.max(occupations, carsInPark);
  }

  public double getRate() {
    return rate;
  }

  public ParkingLotStatus getStatus() {
    return new ParkingLotStatus(getId(), getName(), getRate(), getCapacity(), getReservations(), getVehicles(),
        server.getParkingSpots(), server.getVehicleCounters());
  }

  public void reserveParkingSpot(String plate, String parkingSpot) {
    this.server.reserveParkingSpot(plate, parkingSpot);
  }

  public void start() {
    server.start();
  }
}
