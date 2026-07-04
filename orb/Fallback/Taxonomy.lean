/-
Fallback.Taxonomy — the error taxonomy, handler outcome, and retry policy.

A backend attempt either yields a response or fails with one of a small, closed,
*classified* set of error classes (the taxonomy). A retry policy is exactly a
predicate on that taxonomy: it names WHICH classes are retryable — the chain
falls through to the next handler — versus terminal — the chain stops
immediately and serves the terminal error page.

Keeping the taxonomy closed (a finite `inductive`) is what makes the policy a
total decision and the chain's stopping behaviour a case analysis rather than an
open-ended string match.
-/

namespace Fallback

/-- The error taxonomy: a small, closed, classified set of failure classes a
handler may fail with. Each names a distinct reason a backend attempt did not
yield a response.

The transport/availability classes (`connectFailed`, `timeout`, `upstream5xx`,
`badGateway`, `gatewayTimeout`) describe a *this-backend* failure that a
different backend might not share; the definite classes (`notFound`,
`forbidden`) describe a request-level verdict that retrying cannot change. -/
inductive ErrClass where
  | connectFailed
  | timeout
  | upstream5xx
  | badGateway
  | gatewayTimeout
  | notFound
  | forbidden
deriving DecidableEq, Repr, Inhabited

/-- A handler's outcome on a request: it either produced a response (`ok`), or
it failed with one of the classified error classes (`err`). `Resp` is the
response representation, kept abstract. -/
inductive Outcome (Resp : Type) where
  | ok (resp : Resp)
  | err (cls : ErrClass)
deriving Repr

/-- A retry policy names WHICH error classes are retryable (the chain falls
through to the next handler) versus terminal (the chain stops immediately and
serves the terminal error page). It is exactly a total predicate on the closed
taxonomy. -/
structure RetryPolicy where
  /-- `retryable c = true` ⟺ class `c` falls through to the next handler. -/
  retryable : ErrClass → Bool

/-- A representative default policy: transport / availability failures fall
through (a different backend may succeed); a definite `notFound` or `forbidden`
is terminal (retrying cannot change the answer). -/
def defaultPolicy : RetryPolicy where
  retryable
    | .connectFailed => true
    | .timeout => true
    | .upstream5xx => true
    | .badGateway => true
    | .gatewayTimeout => true
    | .notFound => false
    | .forbidden => false

/-- The transport/availability classes fall through under the default policy. -/
example : defaultPolicy.retryable .timeout = true := rfl
example : defaultPolicy.retryable .connectFailed = true := rfl

/-- The definite classes are terminal under the default policy. -/
example : defaultPolicy.retryable .notFound = false := rfl
example : defaultPolicy.retryable .forbidden = false := rfl

end Fallback
