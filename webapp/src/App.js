import React from 'react'
import { HashRouter as Router, Routes, Route, Link } from 'react-router-dom'
import ParkingLots from './Dashboard'
// import Reservations from './Reservations'

// This data is only used for the demo while in development mode.
import exampleData from './example-data'

export default class App extends React.Component {
  constructor (props) {
    super(props)
    this.state = exampleData
    this.intervalId = null
  }

  async fetchData () {
    const url = '/status/'
    const response = await window.fetch(url)
    const parkingLots = await response.json()
    this.setState({ parkingLots })
  }

  async componentDidMount () {
    await this.fetchData()

    this.intervalId = setInterval(() => {
      this.fetchData()
    }, 1000)
  }

  componentWillUnmount () {
    clearInterval(this.intervalId)
  }

  render () {
    return (
      <div className='pa2 mw7 center'>
        <Router>
          <nav>
            <ul>
              <li>
                <Link to='/'>Dashboard</Link>
              </li>
              <li>
                <Link to='/reservations'>Reservations</Link>
              </li>
            </ul>
          </nav>

          <Routes>
            <Route path='/' element={<ParkingLots parkingLots={this.state.parkingLots} />} />
            {/* <Route path='/reservations' element={<Reservations parkingLots={this.state.parkingLots} />} /> */}
          </Routes>
        </Router>
      </div>
    )
  }
}
