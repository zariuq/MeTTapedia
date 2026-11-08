import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFlexReorder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEliminationsRoundControls

/-!
# Controls for the reorder round

Over `A : U0, F : U0 → U0, B : U0, G : U0 → U0`, at `U0 → U0 → U0`, budget 16 and eight rounds:

| Store | Eliminations solver | Reorder solver |
|---|---|---|
| `λ x y. G x ≐ λ x y. F y` (R107's `farStore`) | stuck | commit |
| the same, and `λ x y. G x ≐ λ x y. Π (F y) A` | stuck | refuted |

The first store is in the fragment and solvable (R107's `far_in_fragment`, `far_solvable`). The second is in the
fragment and has no solution: reordering, pruning `G` and solving `F` leaves `λ x y. H ≐ λ x y. Π H A`, which the occurs
check refutes. The reorder round fires on the first store at depth `1`, through its general firing lemmas
(`far_reorder_fires`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFlexReorder.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentEliminations.Controls

/-- The reorder solver of the tower controls, as a fuel-indexed family. -/
noncomputable def reorderTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  reorderFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The reorder solver at budget 16. -/
noncomputable def reorderOnly : Solver setting.levels := reorderTower.solver 16

/-! ## Flex–flex with a declaration between -/

/-- **The reorder solver commits on flex–flex with a declaration between.** -/
theorem far_committed : (run reorderOnly farStore 8).readout = .commit := by decide +kernel

/-- **The reorder rule fires on the store at depth `1`**, at budget 16. -/
theorem far_reorder_fires :
    (reorderRule (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique 16 farStore).isSome := by decide +kernel

/-- **The reorder round is not stuck on the store**, by the general lemma. -/
theorem far_round_not_stuck :
    reorderRound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) 16 farStore ≠ .stuck :=
  reorderRound_not_stuck_of_reorder _ _ _ _ _ _ _ _ _ _ _ _ _ _ 16 far_reorder_fires

/-! ## A refutation through the reordered store -/

/-- `λ x y. G x ≐ λ x y. F y` and `λ x y. G x ≐ λ x y. Π (F y) A`. -/
def crossStore : EquationStore (TotalTerm withFar) :=
  [(termIn withFar twoLocalsFar (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn withFar twoLocalsFar (.lam (.lam (.app (.var 4) (.var 0)))) (by decide +kernel)),
   (termIn withFar twoLocalsFar (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn withFar twoLocalsFar (.lam (.lam (.pi (.app (.var 4) (.var 0)) (.var 6)))) (by decide +kernel))]

theorem cross_elims_stuck : isStuck (run elimsOnly crossStore 8) = true := by decide +kernel

/-- **The reorder solver refutes it.** -/
theorem cross_refuted : (run reorderOnly crossStore 8).readout = .refuted := by decide +kernel

/-- The store has no solution: the reorder solver's refutation is certified. -/
theorem cross_unsolvable : ¬ (frames setting.levels).Solvable crossStore :=
  Outcome.readout_eq_refuted cross_refuted

end ContextualDependentFlexReorder.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
