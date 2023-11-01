export class Gistemp {
  constructor() {
    this.data = {};
  }

  async fetch(from, to) {
    if (to === undefined) {
      to = from;
    }
    for (let year = from; year <= to; year++) {
      if (!this.data[year]) {
        const response = await fetch(`/data/gistemp/${year}.json`);
        const raw = await response.json();
        this.data[year] = this._convert(raw);
        console.info(`Fetched temperature data from ${year}`);
      }
    }
  }

  _convert(data) {
    return data.map((d) => {
      const parsed = {};

      for (let i = 0, lat = -89; i <= d.length; i++, lat += 2) {
        const temps = d[i];
        parsed[lat] = {};

        if (!temps) {
          continue;
        }

        for (let i = 0, lon = -179; i <= temps.length; i++, lon += 2) {
          if (temps[i]) {
            parsed[lat][lon] = temps[i];
          }
        }
      }

      return parsed;
    });
  }

  get(year, month) {
    if (month) {
      return this.data[year]?.[month - 1];
    } else {
      return this.data[year];
    }
  }
}
