import Mettapedia.GSLT.Scope.ConsumerDescent
import Mettapedia.GSLT.Scope.PredicateDescent

/-!
# Readouts determined by a view

The existing consumer-descent criterion connects to the shared predicate
result: image is contained in universal image exactly when a predicate
descends along the observational quotient. The liftings themselves and their
fibre-constancy proof are supplied by `PredicateDescent` and Mathlib.

The comparison with Mathlib's `Function.FactorsThrough` connects the existing
recovery-function interface to its fibrewise interface. A nonempty result
type is needed when extending recovery to unrepresented views.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.ReadoutDescent

open Mettapedia.GSLT.Core.NonFactorization

universe u v w

variable {X : Type u} {Y : Type v} {Z : Sort w}

theorem factors_iff_factorsThrough [Nonempty Z] (view : X → Y) (consumer : X → Z) :
    Factors view consumer ↔ consumer.FactorsThrough view := by
  constructor
  · intro factors x y same
    exact factors.constantOnFibers x y same
  · intro constant
    obtain ⟨recover, equality⟩ := (Function.factorsThrough_iff consumer).mp constant
    exact ⟨recover, fun x => (congrFun equality x).symm⟩

/-- This is the quotient interface to the one shared predicate-lifting law. -/
theorem predicate_factorization_iff_lift_inclusion (view : X → Y) (predicate : X → Prop) :
    Factors (Quotient.mk (Setoid.ker view)) predicate ↔
      view '' {state | predicate state} ⊆ Set.kernImage view {state | predicate state} := by
  rw [function_descends_iff]
  exact constantOnFibers_iff_image_subset_kernImage view predicate

end Mettapedia.GSLT.Scope.ReadoutDescent
