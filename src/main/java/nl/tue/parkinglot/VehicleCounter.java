package nl.tue.parkinglot;

public class VehicleCounter {
  private final String id;

  private String lastPlate;
  private Long counter, direction;
  private Double x, y;

  public VehicleCounter(String id) {
    this.id = id;
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
}
