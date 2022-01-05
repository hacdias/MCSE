package nl.tue.parkinglot;

public class ParkingSpot {
  private final String id;
  private String state, vehicle;

  public ParkingSpot(String id) {
    this.id = id;
  }

  public String getId() {
    return id;
  }

  public String getState() {
    return state;
  }

  public void setState(String state) {
    this.state = state;
  }

  public String getVehicle() {
    return vehicle;
  }

  public void setVehicle(String vehicle) {
    this.vehicle = vehicle;
  }
}
