/-
Safety.Traversal — path-escape freedom for a static-file handler.

This is the composition theorem: a static-file handler resolves an *arbitrary*
request target (percent-encoded, dot-laden, adversarial) into a filesystem path,
and that path always keeps the configured document root as a prefix. Nothing
resolves outside the root.

The static-file handler is modelled as the boundary decode followed by the
`Route.Path` normalization pipeline joined under the document root:

    serveStatic docRoot rawReq  :=  docRoot ++ normalize rawReq
                                 =  resolveUnder docRoot (decodeSegs rawReq)

so it reuses, unchanged, the two `Route.Path` results that carry the safety
content:

  * `resolveUnder_root_prefix`          — the root is a structural prefix of the
                                          resolved path (join never drops it);
  * `descend_resolveUnder_root_prefix`  — the root survives even a filesystem
                                          interpreter that actually pops on `..`,
                                          because the normalized tail carries no
                                          `..` for a pop to consume.

The decode boundary runs exactly once (percent-decode is NOT idempotent — see
`Route.Path.decode_not_idempotent_twice`), so an attacker's `%252e%252e` cannot
be double-decoded into a `..` after the dot-segment walk.

Theorems:
  * `serveStatic_root_prefix`      — root <+: resolved path, for every input.
  * `serveStatic_tail_no_parent`   — the resolved tail beyond the root has no `..`.
  * `serveStatic_no_escape`        — under a `..`-popping filesystem interpreter,
                                     the root still stays a prefix (traversal-safety
                                     against a real directory walker).
  * `serveStatic_dotdot_confined` / `serveStatic_encoded_dotdot_confined` —
                                     concrete adversarial witnesses.
-/

import Route.Path

namespace Safety.Traversal

open Route.Path

/-- A static-file handler's path resolution: percent-decode the raw request
target once (the boundary), remove dot-segments (the idempotent core), and join
the result under the configured document root. Definitionally
`docRoot ++ removeDotSegments (decodeSegs rawReq) = docRoot ++ normalize rawReq`. -/
def serveStatic (docRoot rawReq : List String) : List String :=
  resolveUnder docRoot (decodeSegs rawReq)

/-- `serveStatic` is exactly the document root followed by the normalized
request path — the "canonicalize then join" shape. -/
theorem serveStatic_eq_normalize (docRoot rawReq : List String) :
    serveStatic docRoot rawReq = docRoot ++ normalize rawReq := by
  unfold serveStatic resolveUnder normalize
  rfl

/-- **Path-traversal safety, prefix form.** For every raw request target the
resolved filesystem path keeps the configured document root as a prefix. No
input — however many encoded or literal `..` it carries — resolves outside the
root. -/
theorem serveStatic_root_prefix (docRoot rawReq : List String) :
    docRoot <+: serveStatic docRoot rawReq :=
  resolveUnder_root_prefix docRoot (decodeSegs rawReq)

/-- The resolved tail (everything below the document root) carries no `..`
segment: the dot-segment walk removed them all before the join. This is what
makes the prefix invariant non-vacuous under real directory semantics. -/
theorem serveStatic_tail_no_parent (_docRoot rawReq : List String) :
    ∀ s ∈ removeDotSegments (decodeSegs rawReq), s ≠ ".." :=
  resolveUnder_tail_no_parent (decodeSegs rawReq)

/-- **Path-traversal safety against a popping filesystem walker.** Given a clean
document root (a real directory path carries no dot-segments), interpreting the
resolved path with `descend` — which actually pops a component on `..` — still
leaves the document root as a prefix. The attacker's encoded `..` was removed
before resolution, so no pop ever fires above the root. -/
theorem serveStatic_no_escape (docRoot rawReq : List String)
    (hclean : ∀ s ∈ docRoot, ¬ IsDot s) :
    docRoot <+: descend [] (serveStatic docRoot rawReq) :=
  descend_resolveUnder_root_prefix docRoot (decodeSegs rawReq) hclean

/-! ### Concrete adversarial witnesses -/

/-- A literal `../../etc/passwd` under `/srv/www` is clamped to
`/srv/www/etc/passwd` — it stays under the root rather than climbing to
`/etc/passwd`. -/
theorem serveStatic_dotdot_confined :
    serveStatic ["srv", "www"] ["..", "..", "etc", "passwd"]
      = ["srv", "www", "etc", "passwd"] := by decide

/-- The percent-encoded traversal `%2e%2e/%2e%2e/etc/passwd` is decoded once to
`../../etc/passwd` and then clamped identically — the single-decode boundary
gives the attacker no second pass to collapse `%252e` into a dot. -/
theorem serveStatic_encoded_dotdot_confined :
    serveStatic ["srv", "www"] ["%2e%2e", "%2e%2e", "etc", "passwd"]
      = ["srv", "www", "etc", "passwd"] := by decide

/-- The double-encoded traversal `%252e%252e` decodes ONCE to the harmless
literal `%2e%2e` (not a dot-segment), so it is treated as an ordinary filename
component and stays strictly under the root — never collapsing to `..`. -/
theorem serveStatic_double_encoded_confined :
    serveStatic ["srv", "www"] ["%252e%252e", "etc", "passwd"]
      = ["srv", "www", "%2e%2e", "etc", "passwd"] := by decide

end Safety.Traversal
