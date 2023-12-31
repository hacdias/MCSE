import React, { useState } from 'react'
import Coordinates from './Coordinates'
import { Table, DataCell, HeaderCell, Row } from './Table'

function Button ({ children, disabled = false, className, color = 'blue', ...props }) {
  return <button disabled={disabled} className={`ba b--${color} link ph3 pv2 dib white bg-${color} b0 ${disabled ? 'o-50' : 'dim pointer'} ${className}`} {...props}>{children}</button>
}

function ChooseParkingLot ({ parkingLots, onParkingLot }) {
  return (
    <Table>
      <Row>
        <HeaderCell>Parking Lot</HeaderCell>
        <HeaderCell>Free Spots</HeaderCell>
        <HeaderCell className='w1' />
      </Row>
      {parkingLots.map(pl => (
        <Row key={pl.id}>
          <DataCell>{pl.name}</DataCell>
          <DataCell>{pl.free}</DataCell>
          <DataCell><Button disabled={pl.free === 0} onClick={() => onParkingLot(pl)}>Reserve</Button></DataCell>
        </Row>
      ))}
    </Table>
  )
}

function ChooseParkingSpot ({ parkingSpots, onParkingSpot }) {
  const [x, setX] = useState(null)
  const [y, setY] = useState(null)

  const reset = () => {
    setX(null)
    setY(null)
  }

  const updateFilter = (event) => {
    let val = event.target.value
    if (!val) {
      reset()
      return
    }

    val = val.replace('(', '')
    val = val.replace(')', '')
    const xy = val.split(',')

    if (xy.length !== 2) {
      reset()
      return
    }

    const x = parseFloat(xy[0])
    const y = parseFloat(xy[1])

    if (isNaN(x) || isNaN(y)) {
      reset()
      return
    }

    setX(x)
    setY(y)
  }

  const filteredSpots = () => {
    if (x === null || y === null) {
      return parkingSpots
    }

    return parkingSpots.filter(ps => {
      // 1 meters of distance
      return Math.hypot(ps.x - x, ps.y - y) <= 1
    })
  }

  return (
    <>
      <input className='ba b--moon-gray pa2 w-100 mb2' type='text' onChange={updateFilter} placeholder='Filter by coordinates: format is (x, y)' />

      <Table>
        <Row>
          <HeaderCell>ID</HeaderCell>
          <HeaderCell>Position</HeaderCell>
          <HeaderCell />
        </Row>
        {filteredSpots().map(ps => ps.state === 'Free' && (
          <Row key={ps.id}>
            <DataCell>{ps.id}</DataCell>
            <DataCell><Coordinates x={ps.x} y={ps.y} /></DataCell>
            <DataCell><Button onClick={() => onParkingSpot(ps)}>Reserve</Button></DataCell>
          </Row>
        ))}
      </Table>
    </>
  )
}

export default function Reservations ({ parkingLots }) {
  console.log(parkingLots)

  const [vehiclePlate, setVehiclePlate] = useState('')
  const [parkingLot, setParkingLot] = useState(null)
  const [parkingSpot, setParkingSpot] = useState(null)
  const [success, setSuccess] = useState(null)

  const updateVehiclePlate = (event) => {
    setVehiclePlate(event.target.value)
  }

  const reset = () => {
    setVehiclePlate('')
    setParkingLot(null)
    setParkingSpot(null)
    setSuccess(null)
  }

  const reserve = async () => {
    const plate = vehiclePlate
    const pl = parkingLot.id
    const ps = parkingSpot ? parkingSpot.id : null

    const data = { plate: plate, parkingLot: pl, parkingSpot: ps }

    try {
      const res = await window.fetch('/reservations/', {
        body: JSON.stringify(data),
        headers: {
          'content-type': 'application/json'
        },
        method: 'POST',
        mode: 'cors',
        redirect: 'follow',
        referrer: 'no-referrer'
      })

      setSuccess(res.status === 200)
      if (res.status !== 200) {
        console.error('unexpected status: ' + res.statusText)
      }
    } catch (e) {
      setSuccess(false)
      console.error(e)
    }
  }

  return (
    <>
      <h1>Reservations</h1>

      {success === null &&
        <>
          <h2>1. Insert Your Vehicle Plate</h2>

          <input className='ba b--moon-gray pa2' type='text' value={vehiclePlate} onChange={updateVehiclePlate} placeholder='AA-11-BB' />

          <h2>2. Choose a Parking Lot</h2>

          {vehiclePlate && !parkingLot && <ChooseParkingLot parkingLots={parkingLots} onParkingLot={setParkingLot} />}

          {vehiclePlate && parkingLot && <p>Parking lot: {parkingLot.name}</p>}

          <h2>3. Choose a Parking Spot (Optional)</h2>

          {parkingLot && !parkingSpot &&
            <>
              <p>The parking lot provides vehicle counters at the entrances and exits. Thus, it is optional to choose a specific parking lot.</p>
              <ChooseParkingSpot {...parkingLot} onParkingSpot={setParkingSpot} />
            </>}

          {parkingSpot && <p>Parking spot: {parkingSpot.id}</p>}
        </>}

      {success === true && <p className='pa2 bg-green white'>Reservation was successfull.</p>}

      {success === false && <p className='pa2 bg-red white'>Reservation failed. Please check the developer's console for more details.</p>}

      <div className='mt3'>
        {success === null && parkingLot && <Button className='mr2' onClick={reserve}>Confirm Reservation</Button>}

        <Button onClick={reset} color='red'>Start Over</Button>
      </div>
    </>
  )
}
