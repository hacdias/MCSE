import React from 'react'

export default function ParkingSpot({ id, state, vehicle }) {
  let color = 'green'
  if (state === 'Occupied') color = 'red'
  if (state === 'Reserved') color = 'orange'

  return (
    <div className={`pa2 ba b--${color} mt2`}>
      <span className={`w1 h1 mr1 dib bg-${color} br-100 v-mid`} alt={state} title={state}></span>
      id: <code>{id}</code>
      {vehicle && color !== 'green' ? ` [${vehicle}]` : null}
    </div>
  )
}
