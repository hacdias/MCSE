package nl.tue.parkinglot.webserver;

import java.io.IOException;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;

import org.eclipse.jetty.server.Request;
import org.eclipse.jetty.server.handler.AbstractHandler;

import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import nl.tue.parkinglot.ParkingSystem;

public class StatusHandler extends AbstractHandler {
  final ParkingSystem parkingSystem;

  final Gson gson = new GsonBuilder()
      .excludeFieldsWithoutExposeAnnotation()
      .create();

  public StatusHandler(ParkingSystem parkingSystem) {
    this.parkingSystem = parkingSystem;
  }

  public void handle(String target, Request baseRequest, HttpServletRequest request, HttpServletResponse response)
      throws IOException, ServletException {

  String statusJsonString = gson.toJson(parkingSystem.getStatuses());

    response.setContentType("application/json; charset=utf-8");
    response.setStatus(HttpServletResponse.SC_OK);
    baseRequest.setHandled(true);
    response.getWriter().println(statusJsonString);
  }
}