package nl.tue.parkinglot;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.sql.Statement;

public class Database {
  final String database;

  public Database(String path) throws SQLException {
    this.database = "jdbc:sqlite:" + path;
    initialize();
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

    Connection conn = DriverManager.getConnection(this.database);
    Statement stmt = conn.createStatement();
    stmt.execute(sqlPS);
    stmt.execute(sqlPL);

    conn.close();
  }

  public void insertParkAtSpot(String lotID, String spotID, String vehicleID) throws SQLException {
    long unixTime = System.currentTimeMillis() / 1000L;
    String sql = "INSERT INTO parking_spots(lot_id, spot_id, vehicle_id, timestamp) VALUES(?, ?, ?, ?)";

    Connection conn = DriverManager.getConnection(this.database);
    PreparedStatement pstmt = conn.prepareStatement(sql);
    pstmt.setString(1, lotID);
    pstmt.setString(2, spotID);
    pstmt.setString(3, vehicleID);
    pstmt.setLong(4, unixTime);
    pstmt.executeUpdate();

    conn.close();
  }

  public void insertParkAtLot(String lotID, String vehicleID) throws SQLException {
    long unixTime = System.currentTimeMillis() / 1000L;
    String sql = "INSERT INTO parking_lots(lot_id, vehicle_id, timestamp) VALUES(?, ?, ?)";

    Connection conn = DriverManager.getConnection(this.database);
    PreparedStatement pstmt = conn.prepareStatement(sql);
    pstmt.setString(1, lotID);
    pstmt.setString(2, vehicleID);
    pstmt.setLong(3, unixTime);
    pstmt.executeUpdate();

    conn.close();
  }
}
