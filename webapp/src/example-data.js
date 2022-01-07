const exampleData = {
  parkingLots: [
    {
      id: 'example-parking-lot',
      name: 'P1',
      rate: 5.24,
      capacity: 3,
      reservations: 1,
      vehicles: 1,
      parkingSpots: [
        {
          id: 'ps-1',
          state: 'Occupied',
          vehicle: 'AA-BB-11',
          x: 3,
          y: 4
        },
        {
          id: 'ps-2',
          state: 'Free',
          vehicle: '',
          x: 3,
          y: 4
        },
        {
          id: 'ps-3',
          state: 'Reserved',
          vehicle: '11-CC-22',
          x: 3,
          y: 4
        }
      ],
      vehicleCounters: [
        {
          id: 'vc-1',
          lastPlate: '',
          counter: 0,
          direction: 0,
          x: 3,
          y: 4
        },
        {
          id: 'vc-2',
          lastPlate: 'AA-11-22',
          counter: 12,
          direction: 1,
          x: 3,
          y: 4
        }
      ]
    }
  ]
}

export default exampleData
