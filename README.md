# 2IMN15 - IoT Parking System

The files in [diagrams](diagrams/) and [objects](objects/), as well as [lwm2m-client.jar](lwm2m-client.jar) are provided by the lecturers.

## Server

```
cd server
mvn clean install (-DskipTests)
java -jar leshan-server-demo/target/leshan-server-demo-2.0.0-SNAPSHOT-jar-with-dependencies.jar
```

## Runnning the Client

LwM2M client implementation based on Leshan client demo. To start it, use a command line like:

```
java -jar lwm2m-client.jar -u 127.0.0.1:5683 -pos "3.0:4.0" -parkingspot -vehiclecounter
```

By running the standard leshan-server-demo application on the
same machine, the client will connect to that server and you
can interact with the client through the provided website (on http://127.0.0.1:8080/ )

The lwm2m-client applications opens a number of windows, one for each
object, which can be used to adjust resource values to test your
server modifications. Some resource values within an object are
updated together, for example, changing 'Last Plate' also increments
'Vehicle Counter'.
