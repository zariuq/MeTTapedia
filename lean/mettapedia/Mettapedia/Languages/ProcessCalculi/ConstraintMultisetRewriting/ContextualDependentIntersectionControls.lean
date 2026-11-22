import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFlexReorderControls

/-!
# Controls for the intersection round

Over `A : U0, F : U0 → U0 → U0`, at budget 16 and eight rounds:

| Store | Reorder solver | Intersection solver |
|---|---|---|
| `λ x y. F x y ≐ λ x y. F y x` (R107's `intersectionStore`) | stuck | commit |
| the same equation twice | stuck | stuck |

The first store is in the fragment and solvable (R107's `intersection_in_fragment`, `intersection_solvable`); the
intersection rule fires on it at budget 16 (`intersection_rule_fires`), so the round is not stuck there by the general
lemma (`intersection_round_not_stuck`).

The second store is in the fragment and solvable, and stays stuck: the rule reads the first equation only when no other
equation mentions `F`. It is the witness, at this budget, of what remains of intersection: the decrease of the normal
weight under the pruning instantiation at every other occurrence of `F`. The intersection step never refutes, so its
refutation control is the absence of one: on every store the rule returns a progress or nothing (`Progress`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersection.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentFlexReorder.Controls

/-- The intersection solver of the tower controls, as a fuel-indexed family. -/
noncomputable def intersectTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  intersectFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The intersection solver at budget 16. -/
noncomputable def intersectOnly : Solver setting.levels := intersectTower.solver 16

/-! ## Intersection -/

theorem intersection_reorder_stuck : isStuck (run reorderOnly intersectionStore 8) = true := by decide +kernel

/-- **The intersection solver commits on `λ x y. F x y ≐ λ x y. F y x`.** -/
theorem intersection_committed : (run intersectOnly intersectionStore 8).readout = .commit := by decide +kernel

/-- **The intersection rule fires on the store**, at budget 16. -/
theorem intersection_rule_fires :
    (intersectRule (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentNormalCheckingTower.head_typing_unique 16 intersectionStore).isSome := by decide +kernel

/-- **The intersection round is not stuck on the store**, by the general lemma. -/
theorem intersection_round_not_stuck :
    intersectRound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) 16 intersectionStore ≠ .stuck :=
  intersectRound_not_stuck_of_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ 16 intersection_rule_fires

/-! ## Intersection with a second occurrence -/

/-- The intersection equation twice. -/
def twiceStore : EquationStore (TotalTerm withBinary) := [intersectionEquation, intersectionEquation]

theorem twice_in_fragment : InFragmentStore twiceStore := by
  intro equation member
  have same : equation = intersectionEquation := by
    rcases List.mem_cons.mp member with same | later
    · exact same
    · exact List.mem_singleton.mp later
  rw [same]
  exact intersection_in_fragment intersectionEquation (by rw [intersectionStore_eq]; exact List.mem_singleton_self _)

theorem twice_solvable : (frames setting.levels).Solvable twiceStore := by
  obtain ⟨Δ, σ, solved⟩ := intersection_solvable
  refine ⟨Δ, σ, fun equation member => ?_⟩
  have same : equation = intersectionEquation := by
    rcases List.mem_cons.mp member with same | later
    · exact same
    · exact List.mem_singleton.mp later
  rw [same]
  exact solved intersectionEquation (by rw [intersectionStore_eq]; exact List.mem_singleton_self _)

/-- **A second occurrence of `F` is not read**: in the fragment, solvable, and stuck at budget 16. -/
theorem twice_stuck : isStuck (run intersectOnly twiceStore 8) = true := by decide +kernel

end ContextualDependentIntersection.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
