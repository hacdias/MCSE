import React from 'react'
import Coordinates from './Coordinates'
import { Table, DataCell, HeaderCell, Row } from './Table'

function ParkingSpot ({ id, state, vehicle, x, y }) {
  let color = 'green'
  if (state === 'Occupied') color = 'red'
  if (state === 'Reserved') color = 'orange'

  return (
    <Row>
      <DataCell><span className={`w1 h1 mr1 dib bg-${color} br-100 v-mid`} alt={state} title={state} /></DataCell>
      <DataCell><code>{id}</code></DataCell>
      <DataCell><Coordinates x={x} y={y} /></DataCell>
      <DataCell>{vehicle && color !== 'green' ? vehicle : null}</DataCell>
    </Row>
  )
}

export default function ParkingSpots ({ parkingSpots }) {
  return (
    <Table>
      <Row>
        <HeaderCell className='w1' />
        <HeaderCell>ID</HeaderCell>
        <HeaderCell>Position</HeaderCell>
        <HeaderCell>Vehicle</HeaderCell>
      </Row>
      {parkingSpots.map(ps => <ParkingSpot key={ps.id} {...ps} />)}
    </Table>
  )
}
