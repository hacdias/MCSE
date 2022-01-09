package nl.tue.parkinglot;

import com.google.gson.annotations.Expose;

import org.eclipse.leshan.server.registration.Registration;

public class VehicleCounter {
  private Registration registration;

  @Expose
  private final String id;

  @Expose
  private String lastPlate;

  @Expose
  private Long counter, direction;

  @Expose
  private Double x, y;

  public VehicleCounter(String id, Registration registration) {
    this.id = id;
    this.registration = registration;
  }

  public String getId() {
    return id;
  }

  public String getLastPlate() {
    return lastPlate;
  }

  public void setLastPlate(String lastPlate) {
    this.lastPlate = lastPlate;
  }

  public Long getDirection() {
    return direction;
  }

  public void setDirection(Long direction) {
    this.direction = direction;
  }

  public Long getCounter() {
    return counter;
  }

  public void setCounter(Long counter) {
    this.counter = counter;
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
