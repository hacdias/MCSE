<script>
  export let scale;
  // An approximate number of ticks to show
  export let numTicks = 5;
  // An array of values where ticks will be shown
  // Takes precedence over numTicks
  export let ticksOverride = undefined;

  let width;
  let ticksWithOffset;

  $: if (scale) {
    // Create a new scale to get the x-position of ticks
    const originalDomain = scale.domain();
    const xScale = scale
      .copy()
      .domain([originalDomain[0], originalDomain[originalDomain.length - 1]])
      .range([0, width]);

    const ticks = ticksOverride ?? scale.ticks(numTicks);

    ticksWithOffset = ticks.map((value) => ({
      value,
      xOffset: xScale(value),
    }));
  }
</script>

<style>
  svg {
    width: 100%;
    overflow: visible;
  }
</style>

<div bind:clientWidth={width}>
  {#if ticksWithOffset && width}
    <svg>
      <!-- horizontal line -->
      <path d="M 0 0 H {width}" fill="none" stroke="currentColor" />
      <!-- ticks -->
      {#each ticksWithOffset as { value, xOffset }}
        <g transform="translate({xOffset}, 0)">
          <line y2="6" stroke="currentColor" />
          <text transform="translate(0, 20)" text-anchor="middle">{value}</text>
        </g>
      {/each}
    </svg>
  {/if}
</div>
