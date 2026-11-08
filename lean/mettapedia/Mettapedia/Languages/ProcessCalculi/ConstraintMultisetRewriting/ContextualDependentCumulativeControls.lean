import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpineEtaControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringRowsControls

/-!
# Controls for the cumulative round

Over `A : U0, F : U1 → U1`, budget 16 and eight rounds:

| Store | Flexible-base solver | Cumulative solver |
|---|---|---|
| `λ x. F x ≐ λ x. x` at `U0 → U1` (R107's `cumulativeStore`) | suspended | commit |
| the same, and `F (Π A A) ≐ Σ A A` at `U1` | suspended | refuted |

The first store is in the fragment and solvable by `F := λ y. y` (R107's `cumulative_in_fragment`,
`cumulative_solvable`). In the second, the cumulative rule solves `F := λ y. y` and the other equation becomes
`Π A A ≐ Σ A A`, a clash of formers: the store has no solution, certified by the refutation.

The intersection equation twice (`twiceStore`) stays suspended under the cumulative family (`twice_open_last`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulative.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentSpineEta.Controls

/-- The cumulative solver of the tower controls, as a fuel-indexed family. -/
noncomputable def cumulativeTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  cumulativeFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The cumulative solver at budget 16. -/
noncomputable def cumulativeOnly : Solver setting.levels := cumulativeTower.solver 16

/-! ## The cumulative argument -/

theorem cumulative_flex_suspended : (run flexOnly cumulativeStore 8).readout = .suspended := by decide +kernel

/-- **The cumulative solver commits on `λ x. F x ≐ λ x. x`** at `U0 → U1`, with `F : U1 → U1`. -/
theorem cumulative_committed : (run cumulativeOnly cumulativeStore 8).readout = .commit := by decide +kernel

/-- **The cumulative rule fires on the store**, at budget 16. -/
theorem cumulative_rule_fires :
    (cumulativeRule (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal 16 cumulativeStore).isSome := by decide +kernel

/-- **The cumulative round is not stuck on the store**, by the general lemma. -/
theorem cumulative_round_not_stuck :
    cumulativeRound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) 16 cumulativeStore ≠ .stuck :=
  cumulativeRound_not_stuck_of_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ 16 cumulative_rule_fires

/-! ## A refutation after the cumulative answer -/

/-- `U1`, over `A, F`. -/
def universeOne : TypeOver withLarge := formIn withLarge (.head (.sort (.succ Tower.zero))) (by decide +kernel)

/-- `λ x. F x ≐ λ x. x` and `F (Π A A) ≐ Σ A A`. -/
def clashStore : EquationStore (TotalTerm withLarge) :=
  [ContextualDependentPatternFiring.Controls.cumulativeEquation,
   (termIn withLarge universeOne (.app (.var 0) (.pi (.var 1) (.var 2))) (by decide +kernel),
    termIn withLarge universeOne (.sigma (.var 1) (.var 2)) (by decide +kernel))]

theorem clash_flex_suspended : (run flexOnly clashStore 8).readout = .suspended := by decide +kernel

/-- **The cumulative solver refutes it.** -/
theorem clash_refuted : (run cumulativeOnly clashStore 8).readout = .refuted := by decide +kernel

theorem clash_unsolvable : ¬ (frames setting.levels).Solvable clashStore :=
  Outcome.readout_eq_refuted clash_refuted

/-! ## The open row -/

/-- **Intersection with another equation on the metavariable stays open** under the cumulative family: the store is in
the fragment and solvable, and the run is suspended. -/
theorem twice_open_last :
    InFragmentStore ContextualDependentIntersection.Controls.twiceStore ∧
      (frames setting.levels).Solvable ContextualDependentIntersection.Controls.twiceStore ∧
      (run cumulativeOnly ContextualDependentIntersection.Controls.twiceStore 8).readout = .suspended :=
  ⟨ContextualDependentIntersection.Controls.twice_in_fragment, ContextualDependentIntersection.Controls.twice_solvable,
    by decide +kernel⟩

end ContextualDependentCumulative.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
