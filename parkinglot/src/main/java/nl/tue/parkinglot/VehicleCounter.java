package nl.tue.parkinglot;

import org.eclipse.leshan.core.node.LwM2mObjectInstance;
import org.eclipse.leshan.core.node.LwM2mResource;
import org.eclipse.leshan.core.request.ContentFormat;
import org.eclipse.leshan.core.request.ReadRequest;
import org.eclipse.leshan.core.request.WriteRequest;
import org.eclipse.leshan.core.request.exception.InvalidRequestException;
import org.eclipse.leshan.core.response.ReadResponse;
import org.eclipse.leshan.server.californium.LeshanServer;
import org.eclipse.leshan.server.registration.Registration;

public class VehicleCounter {
  private final LeshanServer server;
  private final String id;

  private String lastPlate;
  private Long counter, direction;

  public VehicleCounter(Registration reg, LeshanServer server, String parkingLot) throws InvalidRequestException, InterruptedException {
    // Set final server.
    this.server = server;

    // Fetch the ID.
    ReadResponse response = server.send(reg, new ReadRequest(32801, 0, 32700));
    this.id = (String) ((LwM2mResource) response.getContent()).getValue();

    // Update the parking lot name on the vehicle counter.
    server.send(reg, new WriteRequest(ContentFormat.TEXT, 32801, 0, 32706, parkingLot));

    // Fetch the data.
    this.refresh(reg);
  }

  public String getId() {
    return id;
  }

  public String getLastPlate() {
    return lastPlate;
  }

  public Long getDirection() {
    return direction;
  }

  public Long getCounter() {
    return counter;
  }

  public void refresh(Registration registration) throws InterruptedException {
    ReadResponse response = server.send(registration, new ReadRequest(32801, 0));

    if (response.isSuccess()) {
      LwM2mObjectInstance i = (LwM2mObjectInstance) response.getContent();
      counter = (Long) i.getResource(32703).getValue();
      lastPlate = (String) i.getResource(32704).getValue();
      direction = (Long) i.getResource(32705).getValue();
    }
  }
}
