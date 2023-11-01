<script>
  import Scale from "./Scale.svelte";
  import LeafletMap from "./LeafletMap.svelte";
  import MapGeometry from "./MapGeometry.svelte";
  import TemperatureGrid, {
    scale as temperatureScale,
  } from "./TemperatureGrid.svelte";
  import BirdGrid, { scale as birdScale } from "./BirdGrid.svelte";
  import { numToMonth } from "./utils";
  import LeafletSync from "./LeafletSync.svelte";
  import LatitudeLabels from "./LatitudeLabels.svelte";

  export let year;
  export let month;

  export let geometryData;
  export let temperatureData;
  export let allBirdData;

  // Update bird data when year/month change
  let birdData;
  $: if (allBirdData) {
    birdData = allBirdData[year]?.[month - 1];
  }
</script>

<style>
  .outer {
    width: 100%;
    padding-top: 65%;
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

  .maps {
    display: grid;
    grid-template-columns: 50% 50%;
    grid-template-rows: auto 8rem;
  }

  .info {
    text-align: center;
    max-width: 25rem;
    width: 100%;
    margin: 1rem auto 0;
  }

  .title {
    text-align: center;
    font-size: 1.25rem;
    line-height: 1;
    margin: 1rem 0;
    font-weight: 400;
  }
</style>

<div class="outer" id="graph">
  <div class="inner">
    <div class="title">{numToMonth(month)} of {year}</div>

    <div class="maps">
      <LeafletSync>
        <LeafletMap
          options={{ zoomControl: true, attributionControl: false }}
          on:moveend>
          <LatitudeLabels />
          <TemperatureGrid data={temperatureData} />
          <MapGeometry data={geometryData} />
        </LeafletMap>
        <LeafletMap>
          <LatitudeLabels />
          <MapGeometry data={geometryData} />
          <BirdGrid data={birdData} />
        </LeafletMap>
      </LeafletSync>

      <div class="info">
        <strong>Temperature anomaly (°C)</strong>
        <Scale scale={temperatureScale} />
      </div>

      <div class="info">
        <strong>Bird frequency (%)</strong>
        <!-- override ticks because d3 wants way too many -->
        <Scale scale={birdScale} ticksOverride={[1, 2, 4, 10, 20, 40, 100]} />
      </div>
    </div>
  </div>
</div>
