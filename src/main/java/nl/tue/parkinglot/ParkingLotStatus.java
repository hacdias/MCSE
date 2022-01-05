package nl.tue.parkinglot;

import java.util.Collection;

public class ParkingLotStatus {
  private String id, name;
  private double rate;
  private int capacity, reservations, vehicles;
  private Collection<ParkingSpot> parkingSpots;

  public ParkingLotStatus(String id, String name, double rate, int capacity, int reservations, int vehicles, Collection<ParkingSpot> parkingSpots) {
    this.id = id;
    this.name = name;
    this.rate = rate;
    this.capacity = capacity;
    this.reservations = reservations;
    this.vehicles = vehicles;
    this.parkingSpots = parkingSpots;
  }

  public String getId() {
    return id;
  }

  public String getName() {
    return name;
  }

  public double getRate() {
    return rate;
  }

  public int getCapacity() {
    return capacity;
  }

  public int getReservations() {
    return reservations;
  }

  public int getVehicles() {
    return vehicles;
  }

  public Collection<ParkingSpot> getParkingSpots() {
    return parkingSpots;
  }
}
