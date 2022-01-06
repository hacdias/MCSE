import React from 'react'

export default function VehicleCounter({ id, lastPlate, counter, direction }) {
  return <div className='pa2 ba b--gray mt2'>
    <span className={`h1 mr1 w2 tc b dib bg-light-gray br2 pa1`} title='Counter'>{counter}</span>
    id: <code>{id}</code> · {direction === 0 ? 'exit' : 'enter'}

    { lastPlate ? ` [last plate: ${lastPlate}]`: null}
  </div>
}