# Monads with Lean
This repository contains a Lean 4 formalization of:
- Functors
- Applicative Functors
- Monads
- implementations for some example types
along with all the associated laws and proofs that they hold for the
examples. It focuses especially on readability of the proofs and
declarations for non Lean people. Hence whenever possible and sensible
the rw tactic is used and notation typeclasses etc. are avoided
when possible.

## Planned
Eventually I'd like to add:
- Monad transformers
- Semigroup
- Monoid
- Alternative
- Bifunctors
- Implementations of those for specific types
- The Reader and State Monad + their transformers
