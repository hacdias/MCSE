package nl.tue.parkinglot;

import org.eclipse.leshan.server.californium.LeshanServer;
import org.eclipse.leshan.server.registration.Registration;

public class VehicleCounter {
  final Registration registration;
  final LeshanServer server;

  public VehicleCounter(Registration registration, LeshanServer server) {
    this.registration = registration;
    this.server = server;
  }
}
