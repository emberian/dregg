// starbridge-apps/shared/inspectors/index.js
//
// Inspector registry for starbridge-apps. Each app contributes its
// domain inspectors (Preact components published as ES modules — see
// site/STUDIO.md §6) and registers them via `window.pyana.register`.
//
// Today: empty stub. The first concrete inspectors land alongside
// `starbridge-apps/nameservice/` (the file `name.js` in this
// directory once written), then `auction.js`, `proposal.js`,
// `credential.js`, etc., as each starbridge-app comes online per
// STARBRIDGE-APPS-PLAN.md §6.
//
// Once an inspector file exists, register it here:
//
//   import { NameInspector, NameRegistryInspector } from './name.js';
//   window.pyana?.register?.('pyana-name', NameInspector);
//   window.pyana?.register?.('pyana-name-registry', NameRegistryInspector);
//
// The wasm runtime + Studio context resolve `<pyana-name uri="...">`
// custom elements through this registry.
//
// Identity inspectors are imported here so they self-register their
// custom elements with `customElements.define` at module-load time.
// (The import has side effects — see
// starbridge-apps/identity/pages/inspectors.js for the registration
// block.) When this shared loader runs in a host that doesn't serve
// the identity assets, the dynamic import gracefully fails and the
// rest of the shared registry continues to load.
import('/starbridge-apps/identity/inspectors.js').catch(() => {
  /* identity bundle not served by this host — ignore. */
});

// Subscription inspectors (storage-as-cell-programs proof: the
// CapInbox-shaped publisher/consumer queue rebuilt as a starbridge-app
// — see starbridge-apps/subscription/README.md). Side-effecting import
// so `<pyana-subscription>`, `<pyana-subscription-publish-form>`, and
// `<pyana-subscription-feed>` self-register at module-load time. Hosts
// that don't serve subscription assets silently skip registration.
import('/starbridge-apps/subscription/inspectors.js').catch(() => {
  /* subscription bundle not served by this host — ignore. */
});

// Nameservice inspectors. Side-effecting import so
// `<pyana-name>`, `<pyana-name-registry>`, and
// `<pyana-name-register-form>` self-register via
// customElements.define at module-load time. The companion
// turn-builders module registers under
// `window.pyana.builders.nameservice` so the register-form's
// mutation buttons resolve. See
// `starbridge-apps/nameservice/pages/{inspectors,turn-builders}.js`.
import('/starbridge-apps/nameservice/inspectors.js').catch(() => {
  /* nameservice inspectors not served by this host — ignore. */
});
import('/starbridge-apps/nameservice/turn-builders.js').catch(() => {
  /* nameservice turn-builders not served by this host — ignore. */
});

export const registry = {
  // app-name -> { tag-name -> component }
};

export function register(app, tag, component) {
  if (!registry[app]) registry[app] = {};
  registry[app][tag] = component;
  if (typeof window !== 'undefined' && window.pyana?.register) {
    window.pyana.register(tag, component);
  }
}
