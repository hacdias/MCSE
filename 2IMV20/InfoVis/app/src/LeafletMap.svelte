<script>
  import {
    onDestroy,
    onMount,
    setContext,
    createEventDispatcher,
    getContext,
  } from "svelte";
  import L from "leaflet";
  import "leaflet/dist/leaflet.css";
  import { debounce } from "lodash-es";
  import { contextKey as syncContext } from "./LeafletSync.svelte";
  import { BOUNDS } from "./utils.js";

  export let options = {};

  let mapObject;
  let mapElement;
  let width;
  let height;
  let debouncedFitBounds;

  const defaultOptions = {
    zoomControl: false,
    maxBounds: BOUNDS,
    minZoom: 1.6,
    zoomSnap: 0.1,
    crs: L.CRS.EPSG4326, // equirectangular projection
    maxBoundsViscosity: 1.0, // prevent panning outside bounds
  };

  const dispatch = createEventDispatcher();

  setContext(L, {
    getMap: () => mapObject,
  });

  const { sync, unsync } = getContext(syncContext);

  function handleMoveEnd(e) {
    dispatch("moveend", e);
  }

  onMount(() => {
    // Debounce this method to prevent running it too often
    debouncedFitBounds = debounce(() => {
      mapObject.fitBounds(BOUNDS);
    }, 100);

    mapObject = L.map(mapElement, { ...defaultOptions, ...options });
    mapObject.on("moveend", handleMoveEnd);

    // Need to set bounds before syncing
    // Don't use debounced function here because it is not "immediate"
    mapObject.fitBounds(BOUNDS);

    sync(mapObject);
  });

  onDestroy(() => {
    mapObject.off("moveend", handleMoveEnd);
    debouncedFitBounds.cancel();
    unsync(mapObject);
  });

  $: if (mapObject) {
    width = width;
    height = height;
    debouncedFitBounds();
  }
</script>

<div bind:this={mapElement} bind:clientWidth={width} bind:clientHeight={height}>
  {#if mapObject}
    <slot />
  {/if}
</div>
