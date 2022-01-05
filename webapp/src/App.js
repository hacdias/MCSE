import React from 'react'

function StatusIndicator({ title, text }) {
  return <div className='bg-near-white ba b--gray tc mr2'>
    <p className='ma0 pa2 b'>{title}</p>
    <p className='ma0 pa2 bt b--gray'>{text}</p>
  </div>
}

function ParkingLot({ name, id, capacity, vehicles, reservations, rate }) {
  return (
    <div className='pa2 ba b--gray'>
      <header>
        <h2 className='mt0'>Parking Lot {name} (<code>{id}</code>)</h2>
      </header>

      <div className='flex'>
        <StatusIndicator title="Capacity" text={capacity} />
        <StatusIndicator title="Reservations" text={reservations} />
        <StatusIndicator title="Vehicles" text={vehicles} />
        <StatusIndicator title="Free Spots" text={capacity - reservations - vehicles} />
        <StatusIndicator title="Rate" text={`${parseFloat(rate).toFixed(2)} € per hour`} />
      </div>
    </div>
  )
}

export default class App extends React.Component {
  intervalId = null;

  constructor(props) {
    super(props);
    this.state = {
      parkingLots: [
        {
          name: 'Unknown',
          id: 'Unknown',
          capacity: 0,
          reservations: 0,
          vehicles: 0,
          rate: 0.0
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
      <div className='pa2'>
        <h1>Parking System</h1>

        {this.state.parkingLots.map(pl => <ParkingLot key={pl.id} {...pl} />)}
      </div>
    )
  }
}
