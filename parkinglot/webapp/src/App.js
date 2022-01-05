import React from 'react'

function StatusIndicator ({ title, text }) {
  return <div className='bg-near-white ba b--gray tc mr2'>
    <p className='ma0 pa2 b'>{title}</p>
    <p className='ma0 pa2 bt b--gray'>{text}</p>
  </div>
}

export default class App extends React.Component {
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

  render() {
    return <div className='pa2'>
      <header>
        <h1>Parking Lot {this.state.name} (<code>{this.state.id}</code>)</h1>
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
