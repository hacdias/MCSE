import React from 'react'
import Coordinates from './Coordinates'

const tdClass = 'pv2 ph3 tl'

function ParkingSpot({ id, state, vehicle, x, y }) {
  let color = 'green'
  if (state === 'Occupied') color = 'red'
  if (state === 'Reserved') color = 'orange'

  return (
    <tr className='striped--light-gray '>
      <td className={tdClass}><span className={`w1 h1 mr1 dib bg-${color} br-100 v-mid`} alt={state} title={state}></span></td>
      <td className={tdClass}><code>{id}</code></td>
      <td className={tdClass}><Coordinates x={x} y={y} /></td>
      <td className={tdClass}>{vehicle && color !== 'green' ? vehicle : null}</td>
    </tr>
  )
}

export default function ParkingSpots({ parkingSpots }) {
  return (
    <table className='collapse ba b--moon-gray w-100'>
      <tbody>
        <tr className='striped--light-gray '>
          <th className={`${tdClass} w1`}></th>
          <th className={tdClass}>ID</th>
          <th className={tdClass}>Position</th>
          <th className={tdClass}>Vehicle</th>
        </tr>
        {parkingSpots.map(ps => <ParkingSpot key={ps.id} {...ps} />)}
      </tbody>
    </table>
  )
}