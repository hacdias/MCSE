<script>
  import L from "leaflet";
  import LeafletLayer from "./LeafletLayer.svelte";

  export let lat;
  export let lon;

  let options;

  $: options = {
    icon: L.divIcon({
      // Add custom content to the marker icon
      html: `<div class="map-coordinate-label-content">${lat}&deg;</div>`,
      // Set CSS class to override default Leaflet styling
      className: "map-coordinate-label",
    }),
  };
</script>

{#if lat !== undefined && lon !== undefined}
  <LeafletLayer layer={L.marker([lat, lon], options)} />
{/if}
