package nl.tue.parkinglot;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import nl.tue.parkinglot.webserver.WebServer;

public class ParkingSystem {
  final Map<String, ParkingLot> parkingLots = new HashMap<>();
  final WebServer server;

  public ParkingSystem() {
    this.server = new WebServer(this, "127.0.0.1", 8080);
  }

  public void addParkingLot(String name, ParkingLot pl) {
    parkingLots.put(name, pl);
  }

  public ParkingLot getParkingLot(String name) {
    return parkingLots.get(name);
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

  public void start() throws Exception {
    server.start();
  }
}
