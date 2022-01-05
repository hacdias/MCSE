package nl.tue.parkinglot.handlers;

import java.io.IOException;

import com.google.gson.Gson;

import org.eclipse.jetty.server.Request;
import org.eclipse.jetty.server.handler.AbstractHandler;

import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import nl.tue.parkinglot.ParkingLot;

public class StatusHandler extends AbstractHandler {
  final ParkingLot parkingLot;

  public StatusHandler(ParkingLot parkingLot) {
    this.parkingLot = parkingLot;
  }

  public void handle(String target, Request baseRequest, HttpServletRequest request, HttpServletResponse response)
      throws IOException, ServletException {

    String statusJsonString = new Gson().toJson(parkingLot.getStatus());

    response.setContentType("application/json; charset=utf-8");
    response.setStatus(HttpServletResponse.SC_OK);
    baseRequest.setHandled(true);
    response.getWriter().println(statusJsonString);
  }
}