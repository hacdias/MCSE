package nl.tue.parkinglot;

public class ParkingLotException extends Exception {
  public ParkingLotException(String message) {
    super(message);
  }

  public ParkingLotException(Throwable e) {
    super(e);
  }

  public ParkingLotException(String message, Throwable e) {
    super(message, e);
  }
}
