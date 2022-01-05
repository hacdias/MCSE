package nl.tue.parkinglot;

import java.net.InetSocketAddress;

import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.webapp.WebAppContext;

public class WebServer {
  final ParkingLot parkingLot;
  final Server server;

  public WebServer(ParkingLot parkingLot, String hostname, int port) {
    InetSocketAddress addr = new InetSocketAddress(hostname, port);

    this.server = new Server(addr);
    this.parkingLot = parkingLot;

    WebAppContext root = new WebAppContext();
    root.setContextPath("/");
    root.setResourceBase(App.class.getClassLoader().getResource("webapp").toExternalForm());
    root.setParentLoaderPriority(true);
  }

  public void start () throws Exception {
    this.server.start();
  }
}
