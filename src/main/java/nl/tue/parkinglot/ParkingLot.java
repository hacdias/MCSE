package nl.tue.parkinglot;

import java.net.InetAddress;
import java.net.UnknownHostException;

public class ParkingLot {
  final String id, name;
  final double rate;
  final LwM2MServer server;

  public ParkingLot(String name, double rate) {
    String id;
    try {
      id = InetAddress.getLocalHost().getHostName() + "-lot";
    } catch (UnknownHostException e) {
      id = name.toLowerCase() + "-lot";
    }

    this.id = id;
    this.name = name;
    this.rate = rate;

    this.server = new LwM2MServer(name);
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

    return occupations;
  }

  public double getRate() {
    return rate;
  }

  public ParkingLotStatus getStatus() {
    return new ParkingLotStatus(getId(), getName(), getRate(), getCapacity(), getReservations(), getVehicles(),
        server.getParkingSpots());
  }

  public void start() {
    server.start();
  }
}
