import React from 'react'

function StatusIndicator ({ title, text }) {
  return <div className='bg-near-white ba b--gray tc mr2'>
    <p className='ma0 pa2 b'>{title}</p>
    <p className='ma0 pa2 bt b--gray'>{text}</p>
  </div>
}

export default class App extends React.Component {
  intervalId = null;

  constructor(props) {
    super(props);
    this.state = {
      name: 'Unknown',
      id: 'Unknown',
      capacity: 0,
      reservations: 0,
      vehicles: 0,
      rate: 0.0
    };
  }

  fetchData = async () => {
    const url = "/status/";
    const response = await fetch(url);
    const data = await response.json();
    this.setState(data);
  }

  async componentDidMount(){
   await this.fetchData();

   this.intervalId = setInterval(() => {
      this.fetchData();
   }, 1000)
  }

  componentWillUnmount() {
    clearInterval(this.intervalId)
  }

  render() {
    return <div className='pa2'>
      <header>
        <h1>Parking Lot {this.state.name}</h1>
        <p>id: <code>{this.state.id}</code></p>
      </header>

      <div className='flex'>
        <StatusIndicator title="Capacity" text={this.state.capacity}/>
        <StatusIndicator title="Reservations" text={this.state.reservations}/>
        <StatusIndicator title="Vehicles" text={this.state.vehicles}/>
        <StatusIndicator title="Rate" text={`${this.state.rate} € per hour`}/>
      </div>
    </div>
  }
}
