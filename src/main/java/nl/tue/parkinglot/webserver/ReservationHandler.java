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
import java.util.Collection;

import nl.tue.parkinglot.ParkingLot;
import nl.tue.parkinglot.ParkingSpot;

public class ReservationHandler extends AbstractHandler {
  final ParkingSystem parkingSystem;
  private final Gson gson;

  public ReservationHandler(ParkingSystem parkingSystem) {
    this.parkingSystem = parkingSystem;
    gson = new Gson();
  }

  public void handle(String target, Request baseRequest, HttpServletRequest request, HttpServletResponse response)
      throws IOException, ServletException {
    
    //parkingSystem.getParkingLot("name").getParkingSpots()
    if ("POST".equalsIgnoreCase(request.getMethod())) 
    {  
        String reservationJSON = request.getReader().lines().collect(Collectors.joining(System.lineSeparator()));
        Type mapType = new TypeToken<Map<String, String>>(){}.getType();
        Map<String, String> reservationMap = gson.fromJson(reservationJSON, mapType);

        for (ParkingLot e : parkingSystem.getParkingLots()) {
            System.out.println(e.getId());
        }

        ParkingSpot parkingSpot =  parkingSystem
            .getParkingLot(reservationMap.get("parkingLot"))
            .getParkingSpots()
            .get(reservationMap.get("parkingSpot"));
        
        parkingSpot.setState("Reserved");
        parkingSpot.setVehicle(reservationMap.get("plate"));
    }
      
    response.setContentType("application/json; charset=utf-8");
    response.setStatus(HttpServletResponse.SC_OK);
    baseRequest.setHandled(true);
    response.getWriter().println("");

  }
}