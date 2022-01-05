package nl.tue.parkinglot;

public class App {
    public static void main(String[] args) {
        String name = "P1";
        double rate = 5.00;

        ParkingLot lot = new ParkingLot(name, rate);

        try {
            lot.start();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
