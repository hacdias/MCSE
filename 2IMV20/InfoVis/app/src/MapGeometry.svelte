<script>
  import L from "leaflet";
  import LeafletLayer from "./LeafletLayer.svelte";

  export let data;
  export let options = {};

  const defaultOptions = {
    style: {
      color: "#333333",
      weight: 1,
      opacity: 1,
      fillOpacity: 0,
    },
  };
</script>

<LeafletLayer layer={L.geoJSON(data, { ...defaultOptions, ...options })} />
