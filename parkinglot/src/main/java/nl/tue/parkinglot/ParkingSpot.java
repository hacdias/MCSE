package nl.tue.parkinglot;

import java.util.List;

import org.eclipse.leshan.core.model.ObjectLoader;
import org.eclipse.leshan.core.model.ObjectModel;
import org.eclipse.leshan.core.node.LwM2mResource;
import org.eclipse.leshan.core.request.ReadRequest;
import org.eclipse.leshan.core.response.ReadResponse;
import org.eclipse.leshan.server.californium.LeshanServer;
import org.eclipse.leshan.server.californium.LeshanServerBuilder;
import org.eclipse.leshan.server.model.LwM2mModelProvider;
import org.eclipse.leshan.server.model.VersionedModelProvider;
import org.eclipse.leshan.server.registration.Registration;

public class ParkingSpot {
  Registration registration;
  LeshanServer server;

  public ParkingSpot(Registration reg, LeshanServer srv) {
    registration = reg;
    server = srv;
  }

  public String getId() throws InterruptedException {
    ReadResponse response = server.send(registration, new ReadRequest(32800, 0, 32700));

    if (response.isSuccess()) {
      return (String) ((LwM2mResource) response.getContent()).getValue();
    } else {
      return "";
    }
  }

  public String getState() throws InterruptedException {
    ReadResponse response = server.send(registration, new ReadRequest(32800, 0, 32701));

    if (response.isSuccess()) {
      return (String) ((LwM2mResource) response.getContent()).getValue();
    } else {
      return "";
    }
  }
}

// <Item ID="32702">
// <Name>Vehicle ID</Name>
// <Operations>RW</Operations>
// <MultipleInstances>Single</MultipleInstances>
// <Mandatory>Mandatory</Mandatory>
// <Type>String</Type>
// <RangeEnumeration></RangeEnumeration>
// <Units></Units>
// <Description>The ID of the vehicle that reserved the spot.</Description>
// </Item>
// <Item ID="32706">
// <Name>Lot name</Name>
// <Operations>RW</Operations>
// <MultipleInstances>Single</MultipleInstances>
// <Mandatory>Mandatory</Mandatory>
// <Type>String</Type>
// <RangeEnumeration></RangeEnumeration>
// <Units></Units>
// <Description>The name of the parking lot where the parking spot belongs to.
// The value should be non-volatile, such that after a restart, it will connect
// to the matching parking lot server</Description>
// </Item>