import Mettapedia.GSLT.Core.NonFactorization

/-!
# Predicate invariance and observation sufficiency

Predicate-valued factorization uses the existing `NonFactorization.Factors`
contract. Invariance under an equivalence is weaker than invariance under a
coarser equivalence. The exact condition for transporting *every* invariant
predicate is inclusion of the equivalence relations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.PredicateInvariance

open NonFactorization

universe uState uRecord

variable {State : Type uState} {Record : Type uRecord}

/-- A predicate cannot distinguish states related by the declared relation. -/
def InvariantUnder (relation : State → State → Prop) (property : State → Prop) : Prop :=
  ∀ ⦃first second⦄, relation first second → (property first ↔ property second)

/-- A finer relation preserves every predicate invariant under a coarser one. -/
theorem InvariantUnder.of_refinement
    {coarser finer : State → State → Prop} {property : State → Prop}
    (invariant : InvariantUnder coarser property)
    (refines : ∀ ⦃first second⦄, finer first second → coarser first second) :
    InvariantUnder finer property := by
  intro first second related
  exact invariant (refines related)

/-- For predicates, fibrewise invariance is precisely observation sufficiency.
The recovery predicate also covers unobserved records, using an existential
description rather than selecting an arbitrary state. -/
theorem factors_iff_invariantUnder_record
    (record : State → Record) (property : State → Prop) :
    Factors record property ↔
      InvariantUnder (fun first second => record first = record second) property := by
  constructor
  · intro factors first second same
    exact Iff.of_eq (factors.constantOnFibers first second same)
  · intro invariant
    refine ⟨fun value => ∃ state, record state = value ∧ property state, fun state => ?_⟩
    apply propext
    constructor
    · rintro ⟨witness, same, holds⟩
      exact (invariant same).mp holds
    · intro holds
      exact ⟨state, rfl, holds⟩

/-- Moving all invariant predicates to another observational boundary requires
that its relation introduce no new identifications. The converse constructs a
separating predicate from a single equivalence class. -/
theorem all_invariants_transfer_iff_refinement
    (implementation record : State → State → Prop)
    (implementation_equivalence : Equivalence implementation) :
    (∀ property : State → Prop,
      InvariantUnder implementation property → InvariantUnder record property) ↔
      ∀ ⦃first second⦄, record first second → implementation first second := by
  constructor
  · intro transfer first second recorded
    have classInvariant : InvariantUnder implementation (implementation first) := by
      intro left right related
      exact ⟨fun member => implementation_equivalence.trans member related,
        fun member => implementation_equivalence.trans member
          (implementation_equivalence.symm related)⟩
    exact (transfer (implementation first) classInvariant recorded).mp
      (implementation_equivalence.refl first)
  · intro refines property invariant
    exact invariant.of_refinement refines

#print axioms factors_iff_invariantUnder_record
#print axioms all_invariants_transfer_iff_refinement

end Mettapedia.GSLT.Core.PredicateInvariance
