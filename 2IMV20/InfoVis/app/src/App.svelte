<script>
  import {
    MIN_YEAR,
    MAX_YEAR,
    MONTHS,
    LATITUDE_RANGE,
    LONGITUDE_RANGE,
    BIRDS,
    wait,
  } from "./utils";
  import Maps from "./Maps.svelte";
  import Graph from "./Graph.svelte";
  import { Gistemp } from "./gistemp";
  import { onMount } from "svelte";

  let species = BIRDS[0].code;
  let prevSpecies = species;
  let startYear = MIN_YEAR;
  let endYear = MAX_YEAR;
  let year = MIN_YEAR;
  let month = 3;
  let playing = false;
  let period = 2;
  let loading = true;
  let latRange = LATITUDE_RANGE,
    lonRange = LONGITUDE_RANGE;
  let view = "year";
  let loop = false;

  let geometryData,
    birdData,
    birdDataCache = {};

  const temperatureSource = new Gistemp();

  onMount(async () => {
    geometryData = await fetch("/data/map.json").then((res) => res.json());
    // Prefetch all the temperature data
    await temperatureSource.fetch(MIN_YEAR, MAX_YEAR);
    await fetchBirdData();
  });

  async function fetchBirdData() {
    loading = true;
    if (birdDataCache[species]) {
      birdData = birdDataCache[species];
    } else {
      const data = await fetch(
        `/data/ebird/ebd_grid_${species}_1980_2019.json`
      ).then((res) => res.json());

      birdDataCache[species] = data;
      birdData = data;
    }
    loading = false;
  }

  function frequency() {
    return 1000 / period;
  }

  function updateBounds(event) {
    const bounds = event.detail.target.getBounds();

    const newLat = [
      Math.floor(bounds.getSouth()),
      Math.ceil(bounds.getNorth()),
    ];
    const newLon = [Math.floor(bounds.getWest()), Math.ceil(bounds.getEast())];

    latRange = [
      Math.max(newLat[0], LATITUDE_RANGE[0]),
      Math.min(newLat[1], LATITUDE_RANGE[1]),
    ];
    lonRange = [
      Math.max(newLon[0], LONGITUDE_RANGE[0]),
      Math.min(newLon[1], LONGITUDE_RANGE[1]),
    ];
  }

  async function play() {
    if (view == "month") {
      month = 1;
      await wait(frequency());

      while (month <= 12 && playing) {
        if (month == 12) {
          if (loop) month = 1;
          else break;
        } else {
          month++;
        }
        await wait(frequency());
      }
    } else {
      year = startYear;
      await wait(frequency());

      while (year <= endYear && playing) {
        if (year == endYear) {
          if (loop) year = startYear;
          else break;
        } else {
          year++;
        }
        await wait(frequency());
      }
    }
    playing = false;
  }

  $: {
    if (playing) {
      play();
    }

    if (species != prevSpecies) {
      prevSpecies = species;
      fetchBirdData();
    }
  }
</script>

<style>
  main {
    width: 100%;
    max-width: 1200px;
    margin: 0 auto;
    display: grid;
    grid-template-columns: 25rem auto;
    grid-gap: 2rem;
  }

  h1 {
    font-size: 1.75rem;
    margin: 0 0 1rem;
  }

  .loading {
    height: 100%;
    width: 100%;
    background: rgba(0, 0, 0, 0.8);
    position: fixed;
    top: 0;
    left: 0;
    z-index: 10000;
    color: white;
    justify-content: center;
    align-items: center;
    font-size: 6rem;
  }

  .sidebar {
    margin: 1rem 0;
  }
  #controls {
    display: grid;
    grid-template-columns: 6rem auto;
    align-items: center;
    margin: 1rem 0;
    grid-auto-rows: minmax(min-content, max-content);
    grid-gap: 1rem;
  }

  #view-controls {
    display: grid;
    grid-template-columns: 7% 43% 7% 43%;
    line-height: 1;
  }

  .fifty-buttons {
    display: grid;
    grid-template-columns: repeat(2, 1fr);
    grid-gap: 1rem;
  }

  .loop-control {
    display: grid;
    grid-template-columns: 1.5rem auto;
  }
</style>

<svelte:head>
  <title>BirdVis</title>
</svelte:head>

<div class="loading" style="display: {loading ? 'flex' : 'none'}">
  Loading...
</div>

<main>
  <div class="sidebar">
    <h1>BirdVis</h1>

    <div id="controls">
      <label for="species">Species</label>
      <select id="species" bind:value={species} disabled={playing}>
        {#each BIRDS as bird}
          <option value={bird.code}>{bird.name}</option>
        {/each}
      </select>

      <span>View</span>

      <div id="view-controls">
        <input
          disabled={playing}
          type="radio"
          id="year"
          name="view"
          value="year"
          bind:group={view} />
        <label for="year">Yearly</label>

        <input
          disabled={playing}
          type="radio"
          id="month"
          name="view"
          value="month"
          bind:group={view} />
        <label for="month">Monthly</label>
      </div>

      {#if view == 'year'}
        <label for="start-year">Start Year</label>
        <select id="start-year" bind:value={startYear} disabled={playing}>
          {#each Array(MAX_YEAR - MIN_YEAR + 1) as _, i}
            <option value={i + MIN_YEAR}>{i + MIN_YEAR}</option>
          {/each}
        </select>

        <label for="end-year">End year</label>
        <select disabled={playing} id="end-year" bind:value={endYear}>
          {#each Array(MAX_YEAR - startYear + 1) as _, i}
            <option value={i + startYear}>{i + startYear}</option>
          {/each}
        </select>
      {/if}

      <label for="month">Month</label>
      <select disabled={playing} id="month" bind:value={month}>
        {#each MONTHS as month, i}
          <option value={i + 1}>{month}</option>
        {/each}
      </select>

      <span><!-- i am important. leave me here --></span>
      <div class="fifty-buttons">
        <button
          disabled={month == 1 || playing}
          on:click={() => month--}>Previous</button>
        <button
          disabled={month == 12 || playing}
          on:click={() => month++}>Next</button>
      </div>

      <label for="period">{#if view == 'month'}Months{:else}Years{/if}
        per second ({period})</label>
      <input type="range" id="period" min="1" max="12" bind:value={period} />

      <label for="curr-year">View year ({year})</label>
      <input
        disabled={playing}
        type="range"
        id="curr-year"
        min={MIN_YEAR}
        max={MAX_YEAR}
        bind:value={year} />
      <span><!-- i am important. leave me here --></span>
      <div class="fifty-buttons">
        <button
          disabled={year == MIN_YEAR || playing}
          on:click={() => year--}>Previous</button>
        <button
          disabled={year == MAX_YEAR || playing}
          on:click={() => year++}>Next</button>
      </div>

      <span><!-- i am important. leave me here --></span>
      <div class="loop-control">
        <input type="checkbox" id="loop" bind:checked={loop} />
        <label for="loop">Loop</label>
      </div>

      <span><!-- i am important. leave me here --></span>
      <button
        on:click={() => {
          playing = !playing;
        }}>{#if playing}Stop{:else}Start{/if}</button>
    </div>
  </div>

  <div class="vis">
    {#if !loading}
      <Maps
        {year}
        {month}
        {geometryData}
        temperatureData={temperatureSource.get(year, month)}
        allBirdData={birdData}
        on:moveend={updateBounds} />

      <Graph
        {year}
        {startYear}
        {endYear}
        {month}
        {latRange}
        {lonRange}
        {temperatureSource}
        {birdData}
        {view} />
    {/if}
  </div>
</main>
