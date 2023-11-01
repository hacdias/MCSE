import React from 'react'
import ParkingLot from './ParkingLot'

export default function ParkingLots ({ parkingLots }) {
  return (
    <>
      <h1>Dashboard</h1>
      {parkingLots.map(pl => <ParkingLot key={pl.id} {...pl} />)}
    </>
  )
}
