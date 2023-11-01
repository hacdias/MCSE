# 2IMN15 - IoT Parking System

The files in [diagrams](diagrams/) and [lwm2m-client.jar](lwm2m-client.jar) are provided by the lecturers.

## Server

```bash
# Build the server
mvn clean install

# Run the server
java -jar target/parkinglot-1.0-SNAPSHOT-jar-with-dependencies.jar
```

A web server will be available at http://localhost:8080.

## Client

LwM2M client implementation based on Leshan client demo. To start it, use a command line like:

```bash
java -jar lwm2m-client.jar -u 127.0.0.1:5683 -pos "3.0:4.0" -parkingspot -vehiclecounter -n [endpoint-name]
```

To run multiple clients, a different `endpoint-name` is required for each client.

## Frontend Development

Node.js application in `webapp/`. Requires [Node.js](https://nodejs.org/) to be installed.

```bash
# Install dependencies
npm install

# Start development server
npm start
```
