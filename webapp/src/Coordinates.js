import React from 'react'

export default function Coordinates({ x, y }) {
  x = parseFloat(x).toFixed(1)
  y = parseFloat(y).toFixed(1)

  return <span>({x}, {y})</span>
}