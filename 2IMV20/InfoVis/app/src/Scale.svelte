<script>
  import Axis from "./Axis.svelte";

  export let scale;
  // An approximate number of ticks to show
  export let numTicks = 5;
  // An array of values where ticks will be shown
  // Takes precedence over numTicks
  export let ticksOverride = undefined;

  let background = "none";

  $: if (scale) {
    const ticks = ticksOverride ?? scale.ticks(numTicks);

    const domain = scale.domain();
    const minValue = domain[0];
    const maxValue = domain[domain.length - 1];

    const ticksWithColor = ticks.map((value) => ({
      value,
      percent: ((value - minValue) / (maxValue - minValue)) * 100,
      color: scale(value),
    }));

    const colorStops = ticksWithColor
      .map((tick) => `${tick.color} ${tick.percent}%`)
      .join(", ");

    background = `linear-gradient(to right, ${colorStops})`;
  }
</script>

<style>
  .scale .bar {
    width: 100%;
    height: 2rem;
  }

  .scale {
    display: flex;
    padding: 0 2rem;
    margin: 0.5rem 0px;
    width: 100%;
    box-sizing: border-box;
  }

  .top {
    flex-grow: 1;
  }
</style>

<div class="scale">
  <div class="top">
    <div class="bar" style="background: {background}" />
    <Axis {scale} {numTicks} {ticksOverride} />
  </div>
</div>
