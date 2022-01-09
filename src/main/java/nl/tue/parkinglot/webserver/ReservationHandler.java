package nl.tue.parkinglot.webserver;

import java.io.IOException;
import java.lang.reflect.Type;

import org.eclipse.jetty.server.Request;
import org.eclipse.jetty.server.handler.AbstractHandler;

import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import nl.tue.parkinglot.ParkingSystem;
import java.util.Map;
import java.util.stream.*;
import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;
import nl.tue.parkinglot.ParkingLot;

public class ReservationHandler extends AbstractHandler {
  final ParkingSystem parkingSystem;
  private final Gson gson;
  private final Type mapType = new TypeToken<Map<String, String>>() {}.getType();

  public ReservationHandler(ParkingSystem parkingSystem) {
    this.parkingSystem = parkingSystem;
    gson = new Gson();
  }

  public void handle(String target, Request baseRequest, HttpServletRequest request, HttpServletResponse response)
      throws IOException, ServletException {

    if ("POST".equalsIgnoreCase(request.getMethod())) {
      String reservationJSON = request.getReader().lines().collect(Collectors.joining(System.lineSeparator()));
      Map<String, String> reservationMap = gson.fromJson(reservationJSON, mapType);

      for (ParkingLot e : parkingSystem.getParkingLots()) {
        System.out.println(e.getId());
      }

      parkingSystem.reserveParkingSpot(
          reservationMap.get("parkingLot"),
          reservationMap.get("plate"),
          reservationMap.get("parkingSpot"));
    }

    response.setContentType("application/json; charset=utf-8");
    response.setStatus(HttpServletResponse.SC_OK);
    baseRequest.setHandled(true);
    response.getWriter().println("");
  }
}