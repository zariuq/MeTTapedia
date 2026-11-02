import Mettapedia.Logic.WitnessObservations
import Mathlib.Data.Finset.Prod

/-! Joint witness coverage is measured in one shared model. Independent
component coverage and prefix-dependent semijoins both suffice; aggregate
absence alone cannot recover all physical witness tuples. -/

set_option autoImplicit false

namespace Mettapedia.Logic.JoinedWitnessCoverage

variable {M A B : Type*}

def Joint (left : M → A → Prop) (right : M → B → Prop) (model : M) (pair : A × B) : Prop :=
  left model pair.1 ∧ right model pair.2

theorem semijoin_coverage (models : Set M) (leftWorld leftVisible : Finset A) (rightWorld rightVisible : Finset B)
    (left : M → A → Prop) (right : M → B → Prop)
    (leftCovered : ∀ model ∈ models, WitnessObservations.Covers leftVisible leftWorld (left model))
    (rightAfterLeft : ∀ model ∈ models, (∃ first ∈ leftVisible, left model first) →
      WitnessObservations.Covers rightVisible rightWorld (right model)) :
    ∀ model ∈ models, WitnessObservations.Covers (leftVisible ×ˢ rightVisible)
      (leftWorld ×ˢ rightWorld) (Joint left right model) := by
  intro model admitted pair member accepted
  obtain ⟨inLeft, inRight⟩ := Finset.mem_product.mp member
  have first := leftCovered model admitted pair.1 inLeft accepted.1
  have second := rightAfterLeft model admitted ⟨pair.1, first, accepted.1⟩ pair.2 inRight accepted.2
  exact Finset.mem_product.mpr ⟨first, second⟩

theorem component_coverage (models : Set M) (leftWorld leftVisible : Finset A) (rightWorld rightVisible : Finset B)
    (left : M → A → Prop) (right : M → B → Prop)
    (leftCovered : ∀ model ∈ models, WitnessObservations.Covers leftVisible leftWorld (left model))
    (rightCovered : ∀ model ∈ models, WitnessObservations.Covers rightVisible rightWorld (right model)) :
    ∀ model ∈ models, WitnessObservations.Covers (leftVisible ×ˢ rightVisible)
      (leftWorld ×ˢ rightWorld) (Joint left right model) :=
  semijoin_coverage models leftWorld leftVisible rightWorld rightVisible left right leftCovered
    (fun model admitted _ => rightCovered model admitted)

theorem joint_coverage_iff_counts (models : Set M) (world visible : Finset (A × B))
    (left : M → A → Prop) (right : M → B → Prop) (included : visible ⊆ world) :
    (∀ model ∈ models, WitnessObservations.Covers visible world (Joint left right model)) ↔
      ∀ model ∈ models, ∀ _ : DecidablePred (Joint left right model),
        (WitnessObservations.matchingWitnesses visible (Joint left right model)).card =
        (WitnessObservations.matchingWitnesses world (Joint left right model)).card := by
  classical
  constructor
  · intro covers model admitted decision
    exact (WitnessObservations.covers_iff_count_eq visible world _ included).mp (covers model admitted)
  · intro counts model admitted
    exact (WitnessObservations.covers_iff_count_eq visible world _ included).mpr (counts model admitted inferInstance)

theorem separate_solvability_does_not_imply_joint_solvability :
    (∃ model : Bool, model = false) ∧ (∃ model : Bool, model = true) ∧
      ¬ ∃ model : Bool, model = false ∧ model = true := by decide +kernel

/-- Two different physical tuples have the same join answer. Retaining one
preserves emptiness while changing both count and occurrence coverage. -/
theorem join_absence_does_not_force_tuple_coverage :
    let visible : Finset (Bool × Unit) := {(false, ())}
    let world : Finset (Bool × Unit) := {(false, ()), (true, ())}
    visible ⊆ world ∧
      (WitnessObservations.matchingWitnesses visible (fun _ => True) = ∅ ↔
        WitnessObservations.matchingWitnesses world (fun _ => True) = ∅) ∧
      ¬ WitnessObservations.Covers visible world (fun _ => True) := by
  simp only [WitnessObservations.Covers]
  decide +kernel

end Mettapedia.Logic.JoinedWitnessCoverage
