package nl.tue.parkinglot;

public class App {
    public static void main(String[] args) {
        ParkingSystem parkingSystem = new ParkingSystem();

        parkingSystem.addParkingLot("P1", new ParkingLot("P1", 5.0));

        for (ParkingLot pl : parkingSystem.getParkingLots()) {
            // Start LwM2M servers for each parking lot.
            pl.start();
        }

        try {
            // Start parking system web server.
            parkingSystem.start();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
