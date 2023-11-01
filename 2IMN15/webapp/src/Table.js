import React from 'react'

const tdClass = 'pv2 ph3 tl'

export function HeaderCell ({ children, className }) {
  return <th className={`${tdClass} ${className}`}>{children}</th>
}

export function DataCell ({ children, className }) {
  return <td className={`${tdClass} ${className}`}>{children}</td>
}

export function Row ({ children }) {
  return (
    <tr className='striped--light-gray '>
      {children}
    </tr>
  )
}

export function Table ({ children }) {
  return (
    <table className='collapse ba b--moon-gray w-100'>
      <tbody>
        {children}
      </tbody>
    </table>
  )
}
