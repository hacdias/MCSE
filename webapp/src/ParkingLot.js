import React from 'react'
import ParkingSpot from './ParkingSpot'

function StatusIndicator({ title, text }) {
  return <div className='bg-near-white ba b--gray tc mr2'>
    <p className='ma0 pa2 b'>{title}</p>
    <p className='ma0 pa2 bt b--gray'>{text}</p>
  </div>
}

export default function ParkingLot({ name, id, capacity, vehicles, reservations, rate, parkingSpots }) {
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

      <h3>Parking Spots</h3>

      {parkingSpots.map(ps => <ParkingSpot key={ps.id} {...ps} />)}
    </div>
  )
}
