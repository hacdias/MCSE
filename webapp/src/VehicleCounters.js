import React from 'react'
import Coordinates from './Coordinates'

const tdClass = 'pv2 ph3 tl'

function VehicleCounter({ id, lastPlate, counter, direction, x, y }) {
  return (
    <tr className='striped--light-gray '>
      <td className={tdClass}><span className={`h1 mr1 w2 tc b dib bg-black-10 br2 pa1`} title='Counter'>{counter}</span></td>
      <td className={tdClass}><code>{id}</code></td>
      <td className={tdClass}><Coordinates x={x} y={y} /></td>
      <td className={tdClass}>{direction === 0 ? 'exit' : 'enter'}</td>
      <td className={tdClass}>{lastPlate}</td>
    </tr>
  )
}

export default function VehicleCounters({ vehicleCounters }) {
  return (
    <table className='collapse ba b--moon-gray w-100'>
      <tbody>
        <tr className='striped--light-gray '>
          <th className={tdClass}>Counter</th>
          <th className={tdClass}>ID</th>
          <th className={tdClass}>Position</th>
          <th className={tdClass}>Direction</th>
          <th className={tdClass}>Vehicle</th>
        </tr>
        {vehicleCounters.map(vc => <VehicleCounter key={vc.id} {...vc} />)}
      </tbody>
    </table>
  )
}
