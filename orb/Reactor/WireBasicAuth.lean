import Reactor.AuthDeploy

/-!
# Reactor.WireBasicAuth — the BasicAuth deployed seam already lives on the path

The BasicAuth library property "bad credential ⇒ 401, never admit" (RFC 7617) is
ALREADY transported onto the deployed serve path in `Reactor/AuthDeploy.lean`.
`serveBasicAuthGuarded` runs the REAL `BasicAuth.authenticate` over
`Reactor.Deploy.deploySubs` (the submissions `Arena.Orb.main` acts on), and the
seam theorems land the library facts there:

* `deployed_basic_401` — a dispatched protected request whose REAL
  `BasicAuth.authenticate` challenges yields EXACTLY the serializer-built 401
  with the realm challenge, byte-for-byte, on `serveBasicAuthGuarded` — never the
  handler body. (RFC 7617: bad/missing credential ⇒ 401.)
* `deployBasic_noCreds` — the concrete "without credentials" driver: no
  `Authorization` header ⇒ the REAL machine challenges.
* `deployBasic_admit_good_cred` — transport of `BasicAuth.basic_rejects_bad_cred`:
  an `ok` out of the deployed gate FORCES a password the `verify` boundary
  accepted. Contrapositive: a bad credential is never admitted on the deployed
  path.

This file adds no seam — it re-confirms (kernel `#check`) that the deployed
corollary is present, without duplicating it. The mathematical content is
entirely in `AuthDeploy` and the `BasicAuth` core theorems it transports.
-/

namespace Reactor.WireBasicAuth

open Reactor.AuthDeploy

-- The deployed byte-level 401: bad/missing credential ⇒ 401 on the served bytes.
#check @Reactor.AuthDeploy.deployed_basic_401

-- No credentials ⇒ the REAL BasicAuth machine challenges.
#check @Reactor.AuthDeploy.deployBasic_noCreds

-- Transport of the core `basic_rejects_bad_cred`: ok forces a verified password,
-- so a bad credential is never admitted on the deployed path.
#check @Reactor.AuthDeploy.deployBasic_admit_good_cred

-- The deployed serve itself and the REAL decision function it gates on.
#check @Reactor.AuthDeploy.serveBasicAuthGuarded
#check @Reactor.AuthDeploy.deployBasicOutcome

-- The library core theorem being transported (RFC 7617).
#check @BasicAuth.basic_rejects_bad_cred

end Reactor.WireBasicAuth

-- Axiom check of the deployed seam: must stay within the trusted three.
#print axioms Reactor.AuthDeploy.deployed_basic_401
#print axioms Reactor.AuthDeploy.deployBasic_admit_good_cred
