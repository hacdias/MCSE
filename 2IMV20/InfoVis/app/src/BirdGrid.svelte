<script context="module">
  import { scaleLog } from "d3-scale";

  export const scale = scaleLog()
    .domain([1, 100])
    // @ts-ignore
    .range(["white", "green"])
    .clamp(true);
</script>

<script>
  import GridCell from "./GridCell.svelte";

  export let data;

  let grid;

  $: if (data) {
    grid = data.map((cell) => {
      // Parse data, this depends on the JSON structure
      const [lat, lon, frequency] = cell;

      // Map frequency to color scale
      let percent = frequency * 100;
      return { lat, lon, percent, color: scale(percent) };
    });
  }
</script>

{#if grid}
  {#each grid as cell}
    <GridCell
      lat={cell.lat}
      lon={cell.lon}
      color={cell.color}
      size={4}
      tooltipText={`${cell.percent.toFixed(2)}%`} />
  {/each}
{/if}
