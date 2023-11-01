<script>
  import L from "leaflet";
  import LeafletLayer from "./LeafletLayer.svelte";

  export let lat;
  export let lon;
  export let size = 1;
  export let color;
  export let tooltipText;

  let layer;

  $: {
    const bounds = [
      [lat, lon],
      [lat + size, lon + size],
    ];
    const options = {
      weight: 0,
      fillOpacity: 100,
      pane: "tilePane",
    };
    // @ts-ignore
    layer = L.rectangle(bounds, options);
    if (tooltipText) {
      layer.bindTooltip(tooltipText);
    }
  }

  // Update layer color without re-rendering
  $: if (layer) {
    layer.setStyle({ color });
  }
</script>

<LeafletLayer {layer} />
