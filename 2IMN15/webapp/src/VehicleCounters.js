import React from 'react'
import Coordinates from './Coordinates'
import { Table, DataCell, HeaderCell, Row } from './Table'

function VehicleCounter ({ id, lastPlate, counter, direction, x, y }) {
  return (
    <Row>
      <DataCell><span className='h1 mr1 w2 tc b dib bg-black-10 br2 pa1' title='Counter'>{counter}</span></DataCell>
      <DataCell><code>{id}</code></DataCell>
      <DataCell><Coordinates x={x} y={y} /></DataCell>
      <DataCell>{direction === 0 ? 'exit' : 'enter'}</DataCell>
      <DataCell>{lastPlate}</DataCell>
    </Row>
  )
}

export default function VehicleCounters ({ vehicleCounters }) {
  return (
    <Table>
      <Row>
        <HeaderCell>Counter</HeaderCell>
        <HeaderCell>ID</HeaderCell>
        <HeaderCell>Position</HeaderCell>
        <HeaderCell>Direction</HeaderCell>
        <HeaderCell>Vehicle</HeaderCell>
      </Row>
      {vehicleCounters.map(vc => <VehicleCounter key={vc.id} {...vc} />)}
    </Table>
  )
}
