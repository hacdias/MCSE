import React from 'react'
import VehicleCounters from './VehicleCounters'
import ParkingSpots from './ParkingSpots'

function StatusIndicator ({ title, text }) {
  return (
    <div className='5 ba b--moon-gray tc mr2'>
      <p className='ma0 pa2 b bg-light-gray'>{title}</p>
      <p className='ma0 pa2 bt b--black-10'>{text}</p>
    </div>
  )
}

export default function ParkingLot ({ name, id, capacity, vehicles, reservations, free, rate, parkingSpots, vehicleCounters }) {
  return (
    <div className='pa2 ba b--silver'>
      <header>
        <h2 className='mt0'>Parking Lot {name} (<code>{id}</code>)</h2>
      </header>

      <div className='flex'>
        <StatusIndicator title='Capacity' text={capacity} />
        <StatusIndicator title='Reservations' text={reservations} />
        <StatusIndicator title='Vehicles' text={vehicles} />
        <StatusIndicator title='Free Spots' text={free} />
        <StatusIndicator title='Rate' text={`${parseFloat(rate).toFixed(2)} € per hour`} />
      </div>

      <h3>Parking Spots</h3>

      <ParkingSpots parkingSpots={parkingSpots} />

      <h3>Vehicle Counters</h3>

      <VehicleCounters vehicleCounters={vehicleCounters} />
    </div>
  )
}
