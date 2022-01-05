import React from 'react'
import ParkingLot from './ParkingLot'
export default class App extends React.Component {
  intervalId = null;

  constructor(props) {
    super(props);
    this.state = {
      parkingLots: [
        {
          "id": "example-parking-lot",
          "name": "P1",
          "rate": 5.24,
          "capacity": 3,
          "reservations": 1,
          "vehicles": 1,
          "parkingSpots": [
            {
              "id": "ps-1",
              "state": "Occupied",
              "vehicle": "AA-BB-11"
            },
            {
              "id": "ps-2",
              "state": "Free",
              "vehicle": ""
            },
            {
              "id": "ps-3",
              "state": "Occupied",
              "vehicle": ""
            }
          ]
        }
      ]
    };
  }

  fetchData = async () => {
    const url = "/status/";
    const response = await fetch(url);
    const parkingLots = await response.json();
    this.setState({ parkingLots });
  }

  async componentDidMount() {
    await this.fetchData();

    this.intervalId = setInterval(() => {
      this.fetchData();
    }, 1000)
  }

  componentWillUnmount() {
    clearInterval(this.intervalId)
  }

  render() {
    return (
      <div className='pa2 mw7 center'>
        <h1>Parking System</h1>

        {this.state.parkingLots.map(pl => <ParkingLot key={pl.id} {...pl} />)}
      </div>
    )
  }
}
