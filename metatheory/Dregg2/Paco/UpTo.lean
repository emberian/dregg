import Dregg2.Paco.UpTo.Rclo
import Dregg2.Paco.UpTo.Compat
import Dregg2.Paco.UpTo.Cpn
import Dregg2.Paco.UpTo.GPacoClo
import Dregg2.Paco.UpTo.WCompat
import Dregg2.Paco.UpTo.Closures
import Dregg2.Paco.UpTo.Compose
import Dregg2.Paco.UpTo.Respectful

/-!
# Up-To Techniques for Paco (GPaco with Closures)

This module provides "up-to" techniques for parametrized coinduction following
the Coq gpaco library architecture. The key insight is that gpaco composes
the generating function with a reflexive-transitive closure operator.

## Architecture

The gpaco framework extends paco by:
1. `rclo clo R`: Reflexive-transitive closure under closure operator `clo`
2. Modified generating function: `F ∘ rclo clo`
3. `gpaco_clo clo r rg = rclo clo (paco (F ∘ rclo clo) (rg ⊔ r) ⊔ r)`
4. `gupaco_clo clo r = gpaco_clo clo r r`

## Main Definitions

- `rclo clo R`: Reflexive-transitive closure of R under clo
- `Compatible F clo`: Property that clo (F R) ≤ F (clo R)
- `WCompatible F clo`: Weaker version using gupaco
- `cpn F`: Companion (greatest compatible closure)
- `gpaco_clo F clo r rg`: Generalized paco with user-defined closure
- `gupaco_clo F clo r`: Symmetric version (guard = accumulator)

## Modules

- `Paco.UpTo.Rclo`: Reflexive-transitive closure definitions and lemmas
- `Paco.UpTo.Compat`: Compatibility definitions and basic lemmas
- `Paco.UpTo.Cpn`: Companion construction and properties
- `Paco.UpTo.GPacoClo`: GPaco with closure, coinduction principles
- `Paco.UpTo.WCompat`: Weak compatibility theory and companion integration
- `Paco.UpTo.Closures`: Common up-to closures (reflexive, symmetric, etc.)
- `Paco.UpTo.Compose`: Closure composition and union
- `Paco.UpTo.Respectful`: Respectfulness (weaker than compatibility)

## References

- [Paco paper (POPL 2013)](https://plv.mpi-sws.org/paco/)
- [GPaco paper (CPP 2020)](https://paulhe.com/assets/gpaco.pdf)
- [Paco Coq: gpacoN.v](https://github.com/snu-sf/paco)
-/
