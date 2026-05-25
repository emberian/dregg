// starbridge-apps/shared/turn-builders/index.js
//
// Per-app turn-builder presets. Each module wraps
// `window.pyana.signTurn(turnSpec)` (the extension wallet API — see
// extension/src/page.ts) with app-domain conveniences like
// `register_name(name, owner, expiry)` that produce the right
// `turnSpec` shape.
//
// Today: empty stub. The first concrete builder lands as
// `./nameservice.js` once the JS surface of
// `starbridge-apps/nameservice/` is fleshed out. Subsequent apps
// follow per STARBRIDGE-APPS-PLAN.md §6.
//
// Pattern (matches the Rust `build_register_action` in
// starbridge-apps/nameservice/src/lib.rs):
//
//   export function registerName(registryCellHex, name, ownerHex, expiry) {
//     return window.pyana.signTurn({
//       target: registryCellHex,
//       method: 'register_name',
//       effects: [
//         { kind: 'SetField', cell: registryCellHex, index: 8,  value: blake3(name) },
//         { kind: 'SetField', cell: registryCellHex, index: 9,  value: blake3(ownerHex) },
//         { kind: 'SetField', cell: registryCellHex, index: 10, value: u64BE(expiry) },
//         { kind: 'EmitEvent', cell: registryCellHex, topic: 'name-registered',
//           data: [blake3(name), blake3(ownerHex), u64BE(expiry)] },
//       ],
//     });
//   }
//
// The JS side stays the thinnest shim possible — all *policy* lives
// in the Rust crate (which is what the audit-trail and proof code
// path see).

export const builders = {
  // app-name -> { method-name -> async function }
};

export function register(app, name, fn) {
  if (!builders[app]) builders[app] = {};
  builders[app][name] = fn;
}

// Side-effecting import: the identity app self-registers its
// `window.pyana.builders.identity = { issue_credential, ... }` map at
// module-load time. Hosts that don't serve identity assets silently
// skip the registration.
import('/starbridge-apps/identity/turn-builders.js').catch(() => {});

// Side-effecting import: the subscription app self-registers its
// `window.pyana.builders.subscription = { publish, consume,
// grant_publisher, grant_consumer }` map at module-load time. Hosts
// that don't serve subscription assets silently skip the registration.
import('/starbridge-apps/subscription/turn-builders.js').catch(() => {});

// Side-effecting import: the nameservice app self-registers its
// `window.pyana.builders.nameservice = { register_name, renew_name,
// transfer_name, revoke_name, set_target_name }` map at module-load
// time. Mirrors `starbridge-apps/nameservice/src/lib.rs::build_*_action`.
import('/starbridge-apps/nameservice/turn-builders.js').catch(() => {});

// Side-effecting import: the governed-namespace app self-registers its
// `window.pyana.builders['governed-namespace'] = { propose_table_update,
// vote_on_proposal, commit_table_update, register_service }` map at
// module-load time. Mirrors
// `starbridge-apps/governed-namespace/src/lib.rs::build_*_action`.
import('/starbridge-apps/governed-namespace/turn-builders.js').catch(() => {});
