/-!
# Independent and synchronized products of partial observations

For partial results, two product carriers must be distinguished:

* `Option Left × Option Right` retains each coordinate independently;
* `Option (Left × Right)` retains a pair only on common success.

Synchronization forgets unilateral success.  Splitting can recover the
independent pair exactly when the two coordinates are defined together.
This boundary is independent of any event language, valuation algebra, or
foundational calculus.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.PartialObservationProduct

universe uLeft uRight

/-- Synchronize two optional coordinates.  A failure in either coordinate
removes the joint pair. -/
def synchronize {Left : Type uLeft} {Right : Type uRight}
    (results : Option Left × Option Right) : Option (Left × Right) :=
  results.1.bind fun left =>
    results.2.bind fun right =>
      some (left, right)

/-- Split a synchronized result.  Joint failure does not retain which
coordinate failed, so it becomes failure in both projections. -/
def split {Left : Type uLeft} {Right : Type uRight} :
    Option (Left × Right) → Option Left × Option Right
  | none => (none, none)
  | some (left, right) => (some left, some right)

/-- Two optional coordinates are defined together when neither can succeed
without the other. -/
def DefinedTogether {Left : Type uLeft} {Right : Type uRight}
    (left : Option Left) (right : Option Right) : Prop :=
  left.isSome = right.isSome

/-- Synchronization followed by splitting is exact precisely on the
failure-aligned part of the independent product. -/
theorem split_synchronize_eq_iff_definedTogether
    {Left : Type uLeft} {Right : Type uRight}
    (left : Option Left) (right : Option Right) :
    split (synchronize (left, right)) = (left, right) ↔
      DefinedTogether left right := by
  cases left <;> cases right <;>
    simp [split, synchronize, DefinedTogether]

/-! ## Positive and negative controls -/

theorem common_success_roundTrip {Left : Type uLeft} {Right : Type uRight}
    (left : Left) (right : Right) :
    split (synchronize (some left, some right)) =
      (some left, some right) :=
  rfl

theorem unilateral_success_is_not_recoverable
    {Left : Type uLeft} {Right : Type uRight} (right : Right) :
    split (synchronize ((none : Option Left), some right)) ≠
      ((none : Option Left), some right) := by
  simp [split, synchronize]

#print axioms split_synchronize_eq_iff_definedTogether
#print axioms common_success_roundTrip
#print axioms unilateral_success_is_not_recoverable

end Mettapedia.GSLT.Dynamics.PartialObservationProduct
