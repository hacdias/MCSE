package nl.tue.parkinglot;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.sql.Statement;

public class Database {
  final Connection conn;

  public Database(String path) throws SQLException {
    this.conn = DriverManager.getConnection("jdbc:sqlite:" + path);
    initialize();

    insertParkAtLot("lt1", "AA-BB-CC");
  }

  private void initialize() throws SQLException {
    String sqlPS = "CREATE TABLE IF NOT EXISTS parking_spots (\n"
        + "	id integer PRIMARY KEY,\n"
        + "	lot_id text NOT NULL,\n"
        + "	spot_id text NOT NULL,\n"
        + "	vehicle_id text NOT NULL,\n"
        + "	timestamp integer NOT NULL\n"
        + ");";

    String sqlPL = "CREATE TABLE IF NOT EXISTS parking_lots (\n"
        + "	id integer PRIMARY KEY,\n"
        + "	lot_id text NOT NULL,\n"
        + "	vehicle_id text NOT NULL,\n"
        + "	timestamp integer NOT NULL\n"
        + ");";

    Statement stmt = conn.createStatement();
    stmt.execute(sqlPS);
    stmt.execute(sqlPL);
  }

  public void insertParkAtSpot(String lotID, String spotID, String vehicleID) throws SQLException {
    long unixTime = System.currentTimeMillis() / 1000L;
    String sql = "INSERT INTO parking_spots(lot_id, spot_id, vehicle_id, timestamp) VALUES(?, ?, ?, ?)";

    PreparedStatement pstmt = conn.prepareStatement(sql);
    pstmt.setString(1, lotID);
    pstmt.setString(2, spotID);
    pstmt.setString(3, vehicleID);
    pstmt.setLong(4, unixTime);
    pstmt.executeUpdate();
  }

  public void insertParkAtLot(String lotID, String vehicleID) throws SQLException {
    long unixTime = System.currentTimeMillis() / 1000L;
    String sql = "INSERT INTO parking_lots(lot_id, vehicle_id, timestamp) VALUES(?, ?, ?)";

    PreparedStatement pstmt = conn.prepareStatement(sql);
    pstmt.setString(1, lotID);
    pstmt.setString(2, vehicleID);
    pstmt.setLong(3, unixTime);
    pstmt.executeUpdate();
  }

  public void close() {
    try {
      conn.close();
    } catch (SQLException e) {
      e.printStackTrace();
    }
  }
}
