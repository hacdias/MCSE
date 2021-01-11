export const LATITUDE_RANGE = [-90, 90];
export const LONGITUDE_RANGE = [-30, 60];

export const FIRST_YEAR = 1958;
export const LAST_YEAR = 2019;
export const MONTHS = [
  "January",
  "February",
  "March",
  "April",
  "May",
  "June",
  "July",
  "August",
  "September",
  "October",
  "November",
  "December",
];

export function numToMonth(num) {
  if (num <= 0 || num > 12) {
    throw new Error("month number must be between 1 and 12");
  }
  return MONTHS[num - 1];
}

export function monthToNum(month) {
  const i = MONTHS.indexOf(month);
  if (i == -1) {
    throw new Error("invalid month");
  }
  return i + 1;
}
