/-
# GFCore.Variance — Argument variance for predicate positions

Controls whether IsA substitution is sound at each argument position.

Example:
  Rel(produces, [star, light]) + IsA(sun, star)
    Position 0 is covariant → Rel(produces, [sun, light]) ✓
  Rel(orbits, [earth, sun]) + IsA(sun, star)
    Position 1 is invariant → Rel(orbits, [earth, star]) ✗

Default: covariant (safe for generic science facts in EntailmentBank).
Override for specific predicates as the domain demands.

Council: de Paiva (variance = functorial action on IsA ordering),
         Goertzel (PLN: extensional vs intensional inheritance)
-/

import GFCore.ConceptId

namespace GFCore

/-- Variance of an argument position with respect to IsA ordering. -/
inductive Variance where
  | covariant     -- IsA(A,B): replacing B with A is sound (narrowing)
  | contravariant -- IsA(A,B): replacing A with B is sound (widening)
  | invariant     -- no substitution allowed
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Get variance for a predicate's argument at position `i`.
    Default: covariant (all argument positions allow narrowing substitution).
    This is correct for generic science facts where predicates describe
    kind-level properties inherited by subkinds.

    To make this non-trivial, override for specific predicates:
    e.g., `orbits` at position 1 should be `invariant`. -/
def getVariance (_pred : ConceptId) (_argPos : Nat) : Variance :=
  .covariant

end GFCore
