package nl.tue.parkinglot;

import java.util.Collection;
import com.google.gson.annotations.Expose;

public class ParkingLotStatus {
  @Expose
  private String id, name;

  @Expose
  private double rate;

  @Expose
  private int capacity, reservations, vehicles, free;

  @Expose
  private Collection<ParkingSpot> parkingSpots;

  @Expose
  private Collection<VehicleCounter> vehicleCounters;

  public ParkingLotStatus(String id, String name, double rate, int capacity, int reservations, int vehicles,
      Collection<ParkingSpot> parkingSpots, Collection<VehicleCounter> vehicleCounters) {
    this.id = id;
    this.name = name;
    this.rate = rate;
    this.capacity = capacity;
    this.reservations = reservations;
    this.vehicles = vehicles;
    this.parkingSpots = parkingSpots;
    this.vehicleCounters = vehicleCounters;
    this.free = capacity - reservations - vehicles;
    if (this.free < 0) {
      // This accounts for the situation where some car entered the park (via vehicle
      // counters), but the park is all occupied.
      this.free = 0;
    }
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

  public Collection<VehicleCounter> getVehicleCounters() {
    return vehicleCounters;
  }
}
