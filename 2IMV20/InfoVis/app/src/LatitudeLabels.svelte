<script>
  import { getContext, onDestroy, onMount } from "svelte";
  import { scaleLinear } from "d3";
  import L from "leaflet";
  import LatitudeLabel from "./LatitudeLabel.svelte";

  let latRange;
  let lon;
  let scale;

  $: map = getContext(L)?.getMap();

  $: if (latRange) {
    // Scale is only used to generate ticks, no mapping is done
    scale = scaleLinear().domain(latRange).range(latRange);
  }

  function handleMove(event) {
    const bounds = event.target.getBounds();
    latRange = [bounds.getSouth(), bounds.getNorth()];
    lon = bounds.getEast();
  }

  onMount(() => {
    if (map) {
      const bounds = map.getBounds();
      latRange = [bounds.getSouth(), bounds.getNorth()];
      lon = bounds.getEast();

      map.on("move", handleMove);
    }
  });

  onDestroy(() => {
    if (map) {
      map.off("move", handleMove);
    }
  });
</script>

{#if scale}
  {#each scale.ticks() as tick}
    <LatitudeLabel lat={tick} {lon} />
  {/each}
{/if}
