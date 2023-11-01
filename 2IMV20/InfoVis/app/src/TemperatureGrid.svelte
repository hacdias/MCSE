<script context="module">
  import { scaleLinear } from "d3-scale";

  export const scale = scaleLinear()
    .domain([-4, -2, 0, 2, 4])
    // @ts-ignore
    .range(["#2980b9", "#3498db", "#ecf0f1", "#f1c40f", "#c0392b"]);
</script>

<script>
  import GridCell from "./GridCell.svelte";
  import { LATITUDE_RANGE, LONGITUDE_RANGE } from "./utils";

  export let data;

  let gridCells = [];
  $: {
    if (data) {
      gridCells = [];
      for (let lat = LATITUDE_RANGE[0]; lat <= LATITUDE_RANGE[1]; lat += 2) {
        for (
          let lon = LONGITUDE_RANGE[0];
          lon <= LONGITUDE_RANGE[1];
          lon += 2
        ) {
          const temperature = data[lat]?.[lon];
          if (temperature != null) {
            gridCells.push({
              lat,
              lon,
              temperature,
              color: scale(temperature),
            });
          }
        }
      }
    }
  }
</script>

{#each gridCells as cell}
  <GridCell
    lat={cell.lat}
    lon={cell.lon}
    color={cell.color}
    size={2}
    tooltipText={`${cell.temperature.toFixed(2)}°C`} />
{/each}
