package nl.tue.parkinglot;

import java.sql.SQLException;

public class App {
    public static void main(String[] args) {
        // TODO: make this customizable via CLI arguments.
        String hostname = "127.0.0.1";
        Integer port = 8080;
        String databasePath = "./database.db";

        Database db = null;
        try {
            db = new Database(databasePath);

            ParkingSystem parkingSystem = new ParkingSystem(hostname, port, db);

            // Add one parking lot to the system. Theoretically, the system
            // supports multiple parking lots.
            parkingSystem.addParkingLot(new ParkingLot("P1", 5.0, db));

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
        } catch (SQLException e) {
            e.printStackTrace();
        } finally {
            if (db != null) {
                db.close();
            }
        }
    }
}
