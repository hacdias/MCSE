<script>
  import { line, curveMonotoneX, scaleLinear, extent, scaleTime } from "d3";
  import { onMount } from "svelte";
  import { numToMonth } from "./utils";

  export let startYear, endYear, year, month;
  export let latRange, lonRange;
  export let temperatureSource, birdData;
  export let view;

  let width, height;
  let extentX, xScale, xTicks, xPath, yPath;
  let extentTempY, yTempScale, yTempTicks;
  let extentLatY, yLatScale, yLatTicks;

  let tempData = [],
    latData = [];
  let ready = false;

  const LAT_COLOR = "#2ecc71";
  const TEMP_COLOR = "#e74c3c";

  const margin = { bottom: 20, left: 35, right: 40, top: 20 };

  const tempPath = line()
    // @ts-ignore
    .x((d) => xScale(d.x))
    // @ts-ignore
    .y((d) => yTempScale(d.y))
    .curve(curveMonotoneX);

  const latPath = line()
    // @ts-ignore
    .x((d) => xScale(d.x))
    // @ts-ignore
    .y((d) => yLatScale(d.y))
    .curve(curveMonotoneX);

  onMount(() => {
    render();
    ready = true;
  });

  function render() {
    tempData = parseTempData();
    latData = parseLatData();

    extentX = view == "year" ? [startYear, endYear] : [1, 12];
    extentTempY = extent(tempData, (d) => d.y);
    extentTempY[0] -= 0.5;
    extentTempY[1] += 0.5;

    extentLatY = extent(latData, (d) => d.y);
    extentLatY[0] -= 1;
    extentLatY[1] += 1;

    xScale = scaleTime()
      .domain(extentX)
      .range([margin.left, width - margin.right]);

    yTempScale = scaleLinear()
      .domain(extentTempY)
      .range([height - margin.bottom - margin.top, 0]);

    yLatScale = scaleLinear()
      .domain(extentLatY)
      .range([height - margin.bottom - margin.top, 0]);

    xTicks = getTicks(extentX, Math.ceil((extentX[1] - extentX[0]) / 20), 1);
    yTempTicks = getTicks(extentTempY, 0.2, 10);
    yLatTicks = getTicks(
      extentLatY,
      Math.ceil((extentLatY[1] - extentLatY[0]) / 20),
      1
    );

    xPath = `M${margin.left + 0.5},0V0H${width + 1 - margin.right}V0`;
    yPath = `M0,${height - margin.bottom - margin.top}H0.5V0.5`;
  }

  function parseTempData() {
    let data = [];

    let start = view == "year" ? startYear : 1;
    let end = view == "year" ? endYear : 12;

    for (let it = start; it <= end; it++) {
      let sum = 0,
        i = 0;
      const monthData =
        view == "year"
          ? temperatureSource.get(it, month)
          : temperatureSource.get(year, it);

      for (let lat = latRange[0]; lat <= latRange[1]; lat++) {
        for (let lon = lonRange[0]; lon <= lonRange[1]; lon++) {
          if (monthData?.[lat] && monthData?.[lat]?.[lon]) {
            sum += monthData[lat][lon];
            i++;
          }
        }
      }

      data.push({
        x: it,
        y: sum / i,
      });
    }

    return data;
  }

  function parseLatData() {
    let data = [];

    let start = view == "year" ? startYear : 1;
    let end = view == "year" ? endYear : 12;

    for (let it = start; it <= end; it++) {
      const itData =
        view == "year" ? birdData[it]?.[month - 1] : birdData[year]?.[it - 1];

      const frac = itData
        ?.filter((cell) => {
          const [lat, lon] = cell;

          return (
            lat >= latRange[0] &&
            lat <= latRange[1] &&
            lon >= lonRange[0] &&
            lon <= lonRange[1]
          );
        })
        .reduce(
          (acc, cell) => {
            const [lat, lon, freq] = cell;

            acc[0] += lat * freq;
            acc[1] += freq;
            return acc;
          },
          [0, 0]
        );

      const weigthedAverage = frac[0] / frac[1];

      if (!Number.isNaN(weigthedAverage)) {
        data.push({
          x: it,
          y: weigthedAverage,
        });
      }
    }

    return data;
  }

  function getTicks(extent, step, approx) {
    const start = Math.floor(extent[0] * approx) / approx;
    const end = Math.ceil(extent[1] * approx) / approx;

    let ticks = [];
    for (let i = start; i < end; i += step) {
      ticks.push(Math.round(i * approx) / approx);
    }

    return ticks;
  }

  $: {
    // force reaction to those variables
    view = view;
    width = width;
    height = height;
    startYear = startYear;
    endYear = endYear;
    month = month;
    year = year;
    latRange = latRange;
    lonRange = lonRange;
    temperatureSource = temperatureSource;
    birdData = birdData;
    render();
  }
</script>

<style>
  .outer {
    width: 100%;
    padding-top: 60%;
    position: relative;
    background-color: white;
    color: black;
    margin: 1rem 0;
    border: 1px dashed black;
  }

  .inner {
    position: absolute;
    top: 0;
    left: 0;
    bottom: 0;
    right: 0;
    display: grid;
    grid-template-rows: 3.25rem auto;
  }

  .container > div,
  svg {
    width: 100%;
    height: 100%;
  }

  .container {
    padding: 1rem;
  }
  .legend,
  .x-tick text,
  .y-tick text {
    font-size: 0.6rem;
  }

  .y-tick:first-of-type,
  .x-tick:first-of-type {
    display: none;
  }

  .title {
    text-align: center;
    font-size: 1.25rem;
    line-height: 1;
    margin: 1rem 0;
    font-weight: 400;
  }
</style>

<div class="outer">
  <div class="inner">
    <div class="title">
      Mean temperature anomaly and bird latitude
      {#if view === 'year'}in {numToMonth(month)}{:else}during {year}{/if}
    </div>
    <div class="container">
      <div bind:clientWidth={width} bind:clientHeight={height}>
        <svg>
          {#if ready}
            <g transform="translate(0, {margin.top})">
              <path
                d={tempPath(tempData)}
                fill="none"
                stroke={TEMP_COLOR}
                stroke-width="2" />
              <path
                d={latPath(latData)}
                fill="none"
                stroke={LAT_COLOR}
                stroke-width="2" />
            </g>

            <g transform="translate({margin.left}, {margin.top})">
              <text fill={TEMP_COLOR} class="legend" y="-10" x={-margin.left}>
                Temperature (°C)
              </text>
              <path stroke="currentColor" d={yPath} fill="none" />

              {#each yTempTicks as y}
                <g
                  class="y-tick"
                  opacity="1"
                  transform="translate(0,{yTempScale(y)})">
                  <!-- svelte-ignore component-name-lowercase -->
                  <line stroke="currentColor" x2="-5" />
                  <text dy="0.32em" fill="currentColor" x="-{margin.left}">
                    {y}
                  </text>
                </g>
              {/each}
            </g>

            <g transform="translate(0, {height - 20})">
              <path stroke="currentColor" d={xPath} fill="none" />

              {#each xTicks as x}
                <g
                  class="x-tick"
                  opacity="1"
                  transform="translate({xScale(x)},0)">
                  <!-- svelte-ignore component-name-lowercase -->
                  <line stroke="currentColor" y2="6" />
                  {#if view == 'year'}
                    <text fill="currentColor" y="9" dy="0.71em" x="-13">
                      {x}
                    </text>
                  {:else}
                    <text fill="currentColor" y="9" dy="0.71em" x="-9">
                      {numToMonth(x).substring(0, 3)}
                    </text>
                  {/if}
                </g>
              {/each}
            </g>

            <g transform="translate({width - margin.right + 1}, {margin.top})">
              <text fill={LAT_COLOR} class="legend" y="-10" x="-21">
                Latitude (°N)
              </text>
              <path stroke="currentColor" d={yPath} fill="none" />

              {#each yLatTicks as y}
                <g
                  class="y-tick"
                  opacity="1"
                  transform="translate(5,{yLatScale(y)})">
                  <!-- svelte-ignore component-name-lowercase -->
                  <line stroke="currentColor" x2="-5" />
                  <text dy="0.32em" fill="currentColor" x="5">{y}</text>
                </g>
              {/each}
            </g>
          {/if}
        </svg>
      </div>
    </div>
  </div>
</div>
