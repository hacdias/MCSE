package nl.tue.parkinglot;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import nl.tue.parkinglot.webserver.WebServer;

public class ParkingSystem {
  final Map<String, ParkingLot> parkingLots = new HashMap<>();
  final WebServer server;

  public ParkingSystem(String hostname, Integer port) {
    this.server = new WebServer(this, hostname, port);
  }

  public void addParkingLot(ParkingLot pl) {
    parkingLots.put(pl.getId(), pl);
  }

  public ParkingLot getParkingLot(String id) {
    return parkingLots.get(id);
  }

  public Collection<ParkingLot> getParkingLots() {
    return parkingLots.values();
  }

  public Collection<ParkingLotStatus> getStatuses() {
    ArrayList<ParkingLotStatus> statuses = new ArrayList<>();

    for (ParkingLot pl : getParkingLots()) {
      statuses.add(pl.getStatus());
    }

    return statuses;
  }

  public void reserveParkingSpot(String parkingLot, String plate, String parkingSpot) {
    ParkingLot pl = this.getParkingLot(parkingLot);
    pl.reserveParkingSpot(plate, parkingSpot);
  }

  public void start() throws Exception {
    server.start();
  }
}
