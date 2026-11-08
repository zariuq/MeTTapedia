import Mettapedia.Logic.Metaphysics.UltrainfinitismLosTransfer
import Mettapedia.Logic.Metaphysics.UltrainfiniteCofinite

/-!
# Łoś through the cofinite meet: what every free ultrapower satisfies

For a family of first-order structures `A i`:

* **a sentence holds in every free ultraproduct exactly when it holds at all but finitely many
  coordinates** (`forall_free_uprod_iff`);
* **it holds in some free ultraproduct exactly when it holds at infinitely many coordinates**
  (`exists_free_uprod_iff`);
* the free ultraproducts disagree about a sentence exactly when it holds at infinitely many
  coordinates and fails at infinitely many (`freeOpen_uprod_iff`).

These are `ultraTrue_iff_uprod` (Łoś) composed with `forall_free_ultraTrue_iff`,
`exists_free_ultraTrue_iff` and `freeOpen_iff` of `UltrainfiniteCofinite`. They are kept apart
from that module for the reason `UltrainfinitismLosTransfer` gives: the first-order library
declares global syntax.
-/

set_option autoImplicit false

universe u

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

open LO FirstOrder FirstOrder.Structure

variable {I : Type u} {L : Language.{u}} {A : I → Type u} [(i : I) → Structure L (A i)]
  [Nonempty I] [(i : I) → Nonempty (A i)]

/-- **A sentence holds in every free ultraproduct exactly when it holds at all but finitely many
coordinates.** -/
theorem forall_free_uprod_iff (φ : Sentence L) :
    (∀ U : Ultrafilter I, IsFree U → (Uprod A U) ⊧ₘ φ) ↔ {i | ¬ (A i ⊧ₘ φ)}.Finite := by
  rw [← forall_free_ultraTrue_iff]
  exact forall_congr' fun U => imp_congr_right fun _ => (ultraTrue_iff_uprod U φ).symm

/-- **A sentence holds in some free ultraproduct exactly when it holds at infinitely many
coordinates.** -/
theorem exists_free_uprod_iff (φ : Sentence L) :
    (∃ U : Ultrafilter I, IsFree U ∧ (Uprod A U) ⊧ₘ φ) ↔ {i | A i ⊧ₘ φ}.Infinite := by
  rw [← exists_free_ultraTrue_iff]
  exact exists_congr fun U => and_congr_right fun _ => (ultraTrue_iff_uprod U φ).symm

/-- The free ultraproducts disagree about a sentence exactly when it holds at infinitely many
coordinates and fails at infinitely many. -/
theorem freeOpen_uprod_iff (φ : Sentence L) :
    (∃ U V : Ultrafilter I, IsFree U ∧ IsFree V ∧ (Uprod A U) ⊧ₘ φ ∧ ¬ (Uprod A V) ⊧ₘ φ) ↔
      {i | A i ⊧ₘ φ}.Infinite ∧ {i | ¬ (A i ⊧ₘ φ)}.Infinite := by
  rw [← freeOpen_iff]
  refine exists_congr fun U => exists_congr fun V => and_congr_right fun _ => and_congr_right
    fun _ => and_congr (ultraTrue_iff_uprod U φ).symm (not_congr (ultraTrue_iff_uprod V φ).symm)

end Mettapedia.Logic.Metaphysics.Ultrainfinite

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

#print axioms forall_free_uprod_iff
#print axioms exists_free_uprod_iff
#print axioms freeOpen_uprod_iff

end Mettapedia.Logic.Metaphysics.Ultrainfinite
