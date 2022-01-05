package nl.tue.parkinglot.webserver;

import java.net.InetSocketAddress;

import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.server.handler.ContextHandler;
import org.eclipse.jetty.server.handler.HandlerCollection;
import org.eclipse.jetty.webapp.WebAppContext;

import nl.tue.parkinglot.App;
import nl.tue.parkinglot.ParkingSystem;

public class WebServer {
  final ParkingSystem parkingSystem;
  final Server server;

  public WebServer(ParkingSystem parkingSystem, String hostname, int port) {
    InetSocketAddress addr = new InetSocketAddress(hostname, port);

    this.server = new Server(addr);
    this.parkingSystem = parkingSystem;

    WebAppContext staticFiles = new WebAppContext();
    staticFiles.setContextPath("/");
    staticFiles.setResourceBase(App.class.getClassLoader().getResource("webapp").toExternalForm());
    staticFiles.setParentLoaderPriority(true);

    ContextHandler status = new ContextHandler("/status");
    status.setHandler(new StatusHandler(parkingSystem));

    HandlerCollection handlers = new HandlerCollection();
    handlers.addHandler(status);
    handlers.addHandler(staticFiles);

    this.server.setHandler(handlers);
  }

  public void start() throws Exception {
    this.server.start();
  }
}
