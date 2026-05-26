/**
 * Visualizer base — small utilities every visualizer module is encouraged
 * to use so the look-and-feel stays coherent.
 *
 * Import this *after* `runtime-bootstrap.js` has fired the `dreggUi:ready`
 * event:
 *
 *   import { defineVisualizer, useStepper } from '/_includes/visualizer-base.js';
 *
 * Visualizer authoring contract:
 *   - One module per visualizer under `playground/visualizers/<name>.js`.
 *   - Module side effect: call `defineVisualizer('name', component)`.
 *   - The component is a Preact functional component that receives
 *     `{ host, dataset, api }` props.
 *   - Components SHOULD render a header + controls + body + footer in that
 *     order so visualizers are visually consistent.
 *
 * Reduced-motion: the stepper hook reads `api.reducedMotion()` and exposes
 * `autoplay` as a no-op when motion is suppressed.
 */

function ready() {
  return new Promise(resolve => {
    if (window.dreggUi) return resolve(window.dreggUi);
    window.addEventListener('dreggUi:ready', e => resolve(e.detail), { once: true });
  });
}

/**
 * Register a visualizer once the runtime is ready.
 *
 * @param {string} name           Matches `<[data-vizzer=name]>`.
 * @param {Function} Component    Preact functional component.
 */
export async function defineVisualizer(name, Component) {
  const api = await ready();
  api.register(name, (host, dataset, runtime) => {
    return api.h(Component, { host, dataset, api: runtime });
  });
}

/**
 * Tiny stepper hook for "step 1 → step 2 → …" visualizers.
 * Returns reactive controls; autoplay collapses to a single tick under
 * `prefers-reduced-motion: reduce`.
 */
export function useStepper(api, { steps, autoplayMs = 0 } = {}) {
  const index = api.signal(0);
  const playing = api.signal(false);
  let timer = null;

  function go(i) {
    index.value = Math.max(0, Math.min(steps - 1, i));
  }
  function next() { go(index.value + 1); }
  function prev() { go(index.value - 1); }
  function reset() { stop(); go(0); }

  function start() {
    if (api.reducedMotion() || autoplayMs <= 0) return;
    if (playing.value) return;
    playing.value = true;
    timer = setInterval(() => {
      if (index.value >= steps - 1) { stop(); return; }
      next();
    }, autoplayMs);
  }
  function stop() {
    playing.value = false;
    if (timer) clearInterval(timer);
    timer = null;
  }

  return { index, playing, go, next, prev, reset, start, stop };
}

/**
 * Render a standard visualizer chrome: title, optional subtitle, controls
 * slot, body slot, footer slot. Builders should use this so every vizzer
 * has the same affordances and a11y semantics.
 */
export function VizzerFrame(api, { title, subtitle, controls, body, footer }) {
  const { html } = api;
  return html`
    <section class="vizzer" role="group" aria-label=${title}>
      <header class="vizzer__head">
        <h3 class="vizzer__title">${title}</h3>
        ${subtitle ? html`<p class="vizzer__sub">${subtitle}</p>` : null}
        ${controls ? html`<div class="vizzer__controls" role="toolbar">${controls}</div>` : null}
      </header>
      <div class="vizzer__body">${body}</div>
      ${footer ? html`<footer class="vizzer__foot">${footer}</footer>` : null}
    </section>
  `;
}
