package nl.tue.parkinglot;

import java.net.InetSocketAddress;

import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.server.handler.ContextHandler;
import org.eclipse.jetty.server.handler.HandlerCollection;
import org.eclipse.jetty.webapp.WebAppContext;

import nl.tue.parkinglot.handlers.StatusHandler;

public class WebServer {
  final ParkingLot parkingLot;
  final Server server;

  // TODO: support multiple parking lots.
  // final Collection<ParkingLot> parkingLots = new ArrayList<>();

  public WebServer(ParkingLot parkingLot, String hostname, int port) {
    InetSocketAddress addr = new InetSocketAddress(hostname, port);

    this.server = new Server(addr);
    this.parkingLot = parkingLot;

    WebAppContext staticFiles = new WebAppContext();
    staticFiles.setContextPath("/");
    staticFiles.setResourceBase(App.class.getClassLoader().getResource("webapp").toExternalForm());
    staticFiles.setParentLoaderPriority(true);

    ContextHandler status = new ContextHandler("/status");
    status.setHandler(new StatusHandler(parkingLot));

    HandlerCollection handlers = new HandlerCollection();
    handlers.addHandler(status);
    handlers.addHandler(staticFiles);

    this.server.setHandler(handlers);
  }

  public void start() throws Exception {
    this.server.start();
  }
}
