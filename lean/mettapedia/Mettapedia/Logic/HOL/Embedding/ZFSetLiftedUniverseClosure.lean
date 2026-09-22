import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseLift

/-!
# Least-universe formation preserved across the actual ZFSet lift

Universe closure is preserved and reflected by the quotient-level lift.
Every lifted input has a larger-ambient least enclosure, bounded by the
constructed carrier of all lifted small sets. Under the original smaller-
ambient hypothesis this enclosure is exactly the lift of the original
`univOf`, and consequently stays in the shifted carrier.

No larger cofinal-inaccessibles hypothesis is required for that comparison.
Such a hypothesis is needed only for the separately stated comparison with
the globally defined larger-ambient `univOf` operation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetLiftedUniverseClosure

open ZFSetHenkinInterpretation ZFSetUniverseClosure
open ZFSetDependentProducts ZFSetUniverseLift

universe u

theorem closed_lift {U : ZFSet.{u}} (closed : Closed U) : Closed (lift U) where
  transitive := by
    intro a ha b hb
    obtain ⟨smallA, hA, equalA⟩ := mem_lift.mp ha
    rw [← equalA] at hb
    obtain ⟨smallB, hB, equalB⟩ := mem_lift.mp hb
    rw [← equalB]
    exact lift_mem_lift.mpr (closed.transitive smallA hA hB)
  union_mem := by
    intro a ha
    obtain ⟨small, hsmall, rfl⟩ := mem_lift.mp ha
    rw [← lift_sUnion]
    exact lift_mem_lift.mpr (closed.union_mem hsmall)
  power_mem := by
    intro a ha
    obtain ⟨small, hsmall, rfl⟩ := mem_lift.mp ha
    rw [← lift_powerset]
    exact lift_mem_lift.mpr (closed.power_mem hsmall)
  replacement_mem := by
    intro a ha F hF
    obtain ⟨small, hsmall, equal⟩ := mem_lift.mp ha
    rw [← equal] at hF ⊢
    let f : ZFSet.{u} → ZFSet.{u} := fun x => lowerValue (F (lift x))
    have agree : ∀ x ∈ small, F (lift x) = lift (f x) := by
      intro x hx
      have imageInU := hF (lift x) (lift_mem_lift.mpr hx)
      have imageSmall : F (lift x) ∈ carrierCode :=
        carrierCode_transitive (lift U) (mem_carrierCode.mpr ⟨U, rfl⟩) imageInU
      exact (lift_lowerValue imageSmall).symm
    rw [← lift_replacement small f F agree]
    apply lift_mem_lift.mpr
    apply closed.replacement_mem hsmall f
    intro x hx
    have imageInU := hF (lift x) (lift_mem_lift.mpr hx)
    rw [agree x hx] at imageInU
    exact lift_mem_lift.mp imageInU

theorem closed_of_lift {U : ZFSet.{u}} (closed : Closed (lift U)) : Closed U where
  transitive := by
    intro a ha b hb
    exact lift_mem_lift.mp (closed.transitive (lift a)
      (lift_mem_lift.mpr ha) (lift_mem_lift.mpr hb))
  union_mem := by
    intro a ha
    apply lift_mem_lift.mp
    rw [lift_sUnion]
    exact closed.union_mem (lift_mem_lift.mpr ha)
  power_mem := by
    intro a ha
    apply lift_mem_lift.mp
    rw [lift_powerset]
    exact closed.power_mem (lift_mem_lift.mpr ha)
  replacement_mem := by
    intro a ha f hf
    let F : ZFSet.{u + 1} → ZFSet.{u + 1} := fun x => lift (f (lowerValue x))
    have agree : ∀ x ∈ a, F (lift x) = lift (f x) := by
      intro x _
      dsimp [F]
      rw [lowerValue_lift]
    apply lift_mem_lift.mp
    rw [lift_replacement a f F agree]
    apply closed.replacement_mem (lift_mem_lift.mpr ha) F
    intro x hx
    obtain ⟨small, hsmall, rfl⟩ := mem_lift.mp hx
    rw [agree small hsmall]
    exact lift_mem_lift.mpr (hf small hsmall)

theorem closed_lift_iff (U : ZFSet.{u}) : Closed (lift U) ↔ Closed U :=
  ⟨closed_of_lift, closed_lift⟩

/-! ## Actual least enclosures and the original universe operation -/

noncomputable def liftedEnclosure (a : ZFSet.{u}) : ZFSet.{u + 1} :=
  hull (lift a) carrierCode

theorem liftedEnclosure_contains (a : ZFSet.{u}) : lift a ∈ liftedEnclosure a :=
  contains_hull (mem_carrierCode.mpr ⟨a, rfl⟩)

theorem liftedEnclosure_closed (a : ZFSet.{u}) : Closed (liftedEnclosure a) :=
  hull_closed carrierCode_closed

theorem liftedEnclosure_minimal (a : ZFSet.{u}) {U : ZFSet.{u + 1}}
    (contains : lift a ∈ U) (closed : Closed U) : liftedEnclosure a ⊆ U :=
  hull_minimal contains closed

/-- Subset classification and reflection turn the larger least enclosure
back into a smaller closed set, allowing the original minimality theorem
to supply the other inclusion. -/
theorem liftedEnclosure_eq (h : CofinalInaccessibles.{u}) (a : ZFSet.{u}) :
    liftedEnclosure a = lift (univOf h a) := by
  have below : liftedEnclosure a ⊆ lift (univOf h a) :=
    liftedEnclosure_minimal a (lift_mem_lift.mpr (mem_univOf h a))
      (closed_lift (univOf_closed h a))
  obtain ⟨small, _, equal⟩ := subset_lift_classification.mp below
  have closed : Closed small := closed_of_lift (equal.symm ▸ liftedEnclosure_closed a)
  have contains : a ∈ small :=
    lift_mem_lift.mp (equal.symm ▸ liftedEnclosure_contains a)
  have reverse : lift (univOf h a) ⊆ lift small :=
    lift_subset_lift.mpr (univOf_minimal h contains closed)
  apply ZFSet.ext
  intro z
  exact ⟨fun hz => below hz, fun hz => equal ▸ reverse hz⟩

noncomputable def carrierUniverse (h : CofinalInaccessibles.{u})
    (a : Elements carrierCode.{u}) : Elements carrierCode.{u} :=
  ⟨hull a.1 carrierCode, by
    rw [← lift_decode a]
    change liftedEnclosure (carrierEquiv a) ∈ carrierCode
    rw [liftedEnclosure_eq h]
    exact mem_carrierCode.mpr ⟨univOf h (carrierEquiv a), rfl⟩⟩

theorem decode_universe (h : CofinalInaccessibles.{u}) (a : Elements carrierCode.{u}) :
    carrierEquiv (carrierUniverse h a) = univOf h (carrierEquiv a) := by
  apply lift_injective
  rw [lift_decode]
  change hull a.1 carrierCode = lift (univOf h (carrierEquiv a))
  rw [← lift_decode a]
  exact liftedEnclosure_eq h (carrierEquiv a)

theorem carrierUniverse_contains (h : CofinalInaccessibles.{u})
    (a : Elements carrierCode.{u}) : a.1 ∈ (carrierUniverse h a).1 :=
  contains_hull a.2

theorem carrierUniverse_closed (h : CofinalInaccessibles.{u})
    (a : Elements carrierCode.{u}) : Closed (carrierUniverse h a).1 :=
  hull_closed carrierCode_closed

theorem carrierUniverse_minimal (h : CofinalInaccessibles.{u})
    (a : Elements carrierCode.{u}) {U : ZFSet.{u + 1}}
    (contains : a.1 ∈ U) (closed : Closed U) : (carrierUniverse h a).1 ⊆ U := by
  change hull a.1 carrierCode ⊆ U
  exact hull_minimal contains closed

theorem carrierUniverse_not_idempotent (h : CofinalInaccessibles.{u})
    (a : Elements carrierCode.{u}) : carrierUniverse h (carrierUniverse h a) ≠ carrierUniverse h a := by
  intro equal
  have member := carrierUniverse_contains h (carrierUniverse h a)
  rw [equal] at member
  exact ZFSet.mem_irrefl _ member

/-- The extra target hypothesis is needed only to compare with its globally
defined universe operator, not to construct the shifted carrier operation. -/
theorem larger_univOf_eq (h : CofinalInaccessibles.{u + 1}) (a : ZFSet.{u}) :
    univOf h (lift a) = liftedEnclosure a := by
  apply ZFSet.ext
  intro z
  exact ⟨fun hz => univOf_minimal h (liftedEnclosure_contains a) (liftedEnclosure_closed a) hz,
    fun hz => liftedEnclosure_minimal a (mem_univOf h (lift a)) (univOf_closed h (lift a)) hz⟩

theorem lift_univOf (small : CofinalInaccessibles.{u})
    (large : CofinalInaccessibles.{u + 1}) (a : ZFSet.{u}) :
    lift (univOf small a) = univOf large (lift a) := by
  rw [larger_univOf_eq, liftedEnclosure_eq small]

#print axioms closed_lift
#print axioms closed_of_lift
#print axioms closed_lift_iff
#print axioms liftedEnclosure_closed
#print axioms liftedEnclosure_minimal
#print axioms liftedEnclosure_eq
#print axioms carrierUniverse
#print axioms decode_universe
#print axioms carrierUniverse_contains
#print axioms carrierUniverse_closed
#print axioms carrierUniverse_minimal
#print axioms carrierUniverse_not_idempotent
#print axioms larger_univOf_eq
#print axioms lift_univOf

end Mettapedia.Logic.HOL.Embedding.ZFSetLiftedUniverseClosure
