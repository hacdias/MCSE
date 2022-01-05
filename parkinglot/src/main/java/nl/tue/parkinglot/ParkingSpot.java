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

public class ParkingSpot {
  private final LeshanServer server;
  private final String id;

  private String state, vehicle;

  public ParkingSpot(Registration reg, LeshanServer server, String parkingLot) throws InvalidRequestException, InterruptedException {
    // Set final server.
    this.server = server;
    
    // Fetch the ID.
    ReadResponse response = server.send(reg, new ReadRequest(32800, 0, 32700));
    this.id = (String) ((LwM2mResource) response.getContent()).getValue();
    
    // Update the parking lot name on the parking spot.
    server.send(reg, new WriteRequest(ContentFormat.TEXT, 32800, 0, 32706, parkingLot));

    // Fetch the data.
    this.refresh(reg);
  }

  public String getId() {
    return id;
  }

  public String getState() {
    return state;
  }

  public String getVehicle() {
    return vehicle;
  }

  public void refresh(Registration registration) throws InterruptedException {
    ReadResponse response = server.send(registration, new ReadRequest(32800, 0));
  
    if (response.isSuccess()) {
      LwM2mObjectInstance i = (LwM2mObjectInstance) response.getContent();
      state = (String) i.getResource(32701).getValue();
      vehicle = (String) i.getResource(32702).getValue();
    }
  }
}
