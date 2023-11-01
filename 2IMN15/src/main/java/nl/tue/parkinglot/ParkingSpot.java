package nl.tue.parkinglot;

import com.google.gson.annotations.Expose;

import org.eclipse.leshan.server.registration.Registration;

public class ParkingSpot {
  private Registration registration;

  @Expose
  private final String id;

  @Expose
  private String state, vehicle;

  @Expose
  private Double x, y;

  public ParkingSpot(String id, Registration registration) {
    this.id = id;
    this.registration = registration;
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

  public Double getX() {
    return x;
  }

  public void setX(Double x) {
    this.x = x;
  }

  public Double getY() {
    return y;
  }

  public void setY(Double y) {
    this.y = y;
  }

  public Registration getRegistration() {
    return registration;
  }

  public void setRegistration(Registration registration) {
    this.registration = registration;
  }
}
