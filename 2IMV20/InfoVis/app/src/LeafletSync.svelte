<script context="module">
  export const contextKey = {};
</script>

<script>
  import { setContext } from "svelte";
  import "leaflet.sync";

  let maps = [];
  let syncedMaps = [];

  function syncMaps(mapsToSync) {
    for (let i = 0; i < mapsToSync.length; i++) {
      for (let j = i + 1; j < mapsToSync.length; j++) {
        mapsToSync[i].sync(mapsToSync[j]);
        mapsToSync[j].sync(mapsToSync[i]);
      }
    }
    syncedMaps = mapsToSync;
  }

  function unsyncMaps(mapsToUnsync) {
    for (let i = 0; i < mapsToUnsync.length; i++) {
      for (let j = i + 1; j < mapsToUnsync.length; j++) {
        mapsToUnsync[i].unsync(mapsToUnsync[j]);
        mapsToUnsync[j].unsync(mapsToUnsync[i]);
      }
    }
    syncedMaps = [];
  }

  // Context lets maps request to be synced or unsynced by calling
  // the respective functions
  setContext(contextKey, {
    sync: (map) => {
      maps = [map, ...maps];
    },
    unsync: (map) => {
      maps = maps.filter((m) => m !== map);
    },
  });

  // When a map requests to be synced, unsync all currently synced maps and
  // sync the new array of maps (could be more optimized)
  $: {
    unsyncMaps(syncedMaps);
    syncMaps(maps);
  }
</script>

<slot />
