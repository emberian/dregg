import Reactor.Bridge
import Reactor.Captp

/-!
# Reactor.WireCaptp — the CapTP epoch guard, confirmed on the deployed serve path

The CapTP netlayer epoch guard — *a descriptor is valid only in its epoch* — is
already attached to the deployed serve path. The seam lives in `Reactor.Captp`
(namespace `Reactor.Netlayer`):

  * `Reactor.Netlayer.captp_epoch_seam` (headline) transports the real
    `Captp.Session.bump_invalidates` onto the reactor's session state: any stamped
    reference that resolves in the reactor's post-grant session is REJECTED after a
    future run of session operations that advanced the epoch and rebound the
    descriptor's position. Its `Session.WF` precondition is discharged (not
    assumed) from the deployed cold start via `init_wf` → `grantRun_wf` →
    `exportObject_wf`.
  * `Reactor.Netlayer.grant_serves_routed_deployed` lands the served-byte routing
    of the captp-wired step on the *deployed* submissions `Reactor.Deploy.deploySubs
    input` — what `serveFull`/`main` runs — through the Bridge congruence
    `Reactor.Bridge.deployed_routes`. So the epoch-guarded grant sits on the exact
    request the deployed orb dispatched, not a fresh side model.

This file does not re-prove any of that. It (1) `#check`s the existing deployed
seams so any regression fails loudly, and (2) lands one concrete
transport, `captp_deployed`: the epoch guard instantiated at the deployed cold
start `Reactor.Netlayer.NetState.init` (the session `main` boots with, well-formed
by `init_wf`). This is not a restatement — it carries the real `hcur`/`hbump`
hypotheses and its conclusion is the genuine `resolveStamped … = none` rejection,
resting entirely on the existing machinery.
-/

namespace Reactor
namespace WireCaptp

open Proto (Bytes)

-- The deployed CapTP seams already in the tree; this file only confirms they
-- typecheck at their real statements.
#check @Reactor.Netlayer.captp_epoch_seam
#check @Reactor.Netlayer.captp_epoch_seam_grant
#check @Reactor.Netlayer.grant_serves_routed_deployed
#check @Reactor.Netlayer.reset_rebind_rejects_stale
#check @Reactor.Bridge.deploySubs_eq_reactorSubs

/-- **`captp_deployed` — the epoch guard at the deployed cold start.** The
reference the reactor grants for a served request, on the session `main` boots
with (`NetState.init`, well-formed by `Reactor.Netlayer.init_wf`), is valid ONLY
within its epoch: after any run of session operations that advanced the epoch and
rebound the granted descriptor's position at the new current epoch (`hcur`,
`hbump`), the original stamp is REJECTED — `resolveStamped` returns `none`. This
is `Reactor.Netlayer.captp_epoch_seam_grant` instantiated at the deployed start,
its `WF` precondition discharged by `init_wf` (not assumed). A pure transport of
the real `Captp.Session.bump_invalidates` onto the deployed cold-start session. -/
theorem captp_deployed (input : Bytes) (ops : List Captp.Session.Op)
    (hcur :
      ((Reactor.Netlayer.sessionAfter Reactor.Netlayer.NetState.init input).run ops).descEpoch
          (Reactor.Netlayer.grantOf Reactor.Netlayer.NetState.init input).desc
        = some
          (((Reactor.Netlayer.sessionAfter Reactor.Netlayer.NetState.init input).run ops).epoch))
    (hbump :
      (Reactor.Netlayer.sessionAfter Reactor.Netlayer.NetState.init input).epoch
        < ((Reactor.Netlayer.sessionAfter Reactor.Netlayer.NetState.init input).run ops).epoch) :
    ((Reactor.Netlayer.sessionAfter Reactor.Netlayer.NetState.init input).run ops).resolveStamped
        (Reactor.Netlayer.grantOf Reactor.Netlayer.NetState.init input).desc
        (Reactor.Netlayer.grantOf Reactor.Netlayer.NetState.init input).stamp = none :=
  Reactor.Netlayer.captp_epoch_seam_grant Reactor.Netlayer.init_wf input ops hcur hbump

#print axioms captp_deployed

end WireCaptp
end Reactor
