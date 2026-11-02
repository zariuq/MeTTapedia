import Mettapedia.Logic.ProjectedObservations
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-! Boundary controls for converse claims: cardinality needs inclusion and
finiteness; universal logical queries need a consistency check before they
can authorize an operational action. -/

set_option autoImplicit false

namespace Mettapedia.Logic.ObservationReversalBoundaryControls

theorem equal_counts_without_inclusion_do_not_identify_witnesses :
    ({false} : Finset Bool).card = ({true} : Finset Bool).card ∧
      ({false} : Finset Bool) ≠ {true} := by decide +kernel

def positiveEquiv : Nat ≃ {number : Nat // 0 < number} where
  toFun number := ⟨number + 1, by omega⟩
  invFun number := number.val - 1
  left_inv number := by simp
  right_inv number := by apply Subtype.ext; have positive := number.property; dsimp; omega

theorem proper_infinite_subset_still_has_a_bijection :
    ({number : Nat | 0 < number} : Set Nat) ⊂ Set.univ ∧
      Nonempty (Nat ≃ {number : Nat // 0 < number}) := by
  refine ⟨?_, ⟨positiveEquiv⟩⟩
  constructor
  · exact Set.subset_univ _
  · intro included
    have impossible := included (Set.mem_univ (0 : Nat))
    exact Nat.lt_irrefl 0 impossible

theorem inconsistent_models_make_every_universal_query_true {A O : Type*}
    (observe : A → O) (query : O → Prop) :
    ProjectedObservations.Necessary (∅ : Set A) observe query := by
  intro model absent
  cases absent

theorem inconsistency_is_distinguished_by_false_query :
    ProjectedObservations.Necessary (∅ : Set Unit) id (fun _ => False) ∧
      ¬ ProjectedObservations.Necessary (Set.univ : Set Unit) id (fun _ => False) := by
  exact ⟨inconsistent_models_make_every_universal_query_true _ _, fun impossible => impossible () trivial⟩

end Mettapedia.Logic.ObservationReversalBoundaryControls
