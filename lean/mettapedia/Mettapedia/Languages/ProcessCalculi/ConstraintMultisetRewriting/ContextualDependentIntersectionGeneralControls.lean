import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionControls

/-!
# Controls for the general round

Over `A : U0, F : U0 → U0 → U0`, at budget 16 and eight rounds:

| Store | Cumulative solver | General solver |
|---|---|---|
| `λ x y. F x y ≐ λ x y. F y x` twice (R110's `twiceStore`) | suspended | commit |
| that equation, then `λ x y. F x x ≐ λ x y. x` | suspended | refuted |
| that equation, then `λ x y. F x y ≐ λ x y. x` | refuted | refuted |

`twiceStore` is in the fragment and solvable (R110's `twice_in_fragment`, `twice_solvable`); the general intersection
rule fires on it at budget 16 (`twice_rule_fires`), with the second equation mentioning `F`. Its answer prunes `F` to a
constant `H`, the second equation becomes `H ≐ H`, and the store is solved.

In the second store, intersection prunes `F` to a constant `H`, and the second equation becomes `λ x y. H ≐ λ x y. x`,
whose right side is a local outside `H`'s scope: no solution, certified by the refutation. The cumulative family
cannot read it: its first equation is the intersection, and its second is not a pattern. In the third, the cumulative
family already refutes from the second equation; the general family agrees, being conservative over it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionGeneral.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls

/-- The general solver of the tower controls, as a fuel-indexed family. -/
noncomputable def generalTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  generalFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The general solver at budget 16. -/
noncomputable def generalOnly : Solver setting.levels := generalTower.solver 16

/-! ## Intersection with a second occurrence -/

/-- **The general solver commits on R110's gap witness** `twiceStore`. -/
theorem twice_committed :
    (run generalOnly ContextualDependentIntersection.Controls.twiceStore 8).readout = .commit := by decide +kernel

/-- **The general intersection rule fires on `twiceStore`**, at budget 16, though the second equation mentions `F`. -/
theorem twice_rule_fires :
    (generalIntersectRule (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentNormalCheckingTower.head_typing_unique 16
      ContextualDependentIntersection.Controls.twiceStore).isSome := by decide +kernel

/-- **The general round is not stuck on `twiceStore`**, by the general lemma. -/
theorem twice_round_not_stuck :
    generalRound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) 16
      ContextualDependentIntersection.Controls.twiceStore ≠ .stuck :=
  generalRound_not_stuck_of_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ 16 twice_rule_fires

/-! ## A refutation after intersection -/

/-- The intersection equation, then `λ x y. F x x ≐ λ x y. x`. -/
def diagonalStore : EquationStore (TotalTerm withBinary) :=
  [intersectionEquation,
   (termIn withBinary binaryHere (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 1)))) (by decide +kernel),
    termIn withBinary binaryHere (.lam (.lam (.var 1))) (by decide +kernel))]

theorem diagonal_cumulative_suspended :
    (run ContextualDependentCumulative.Controls.cumulativeOnly diagonalStore 8).readout = .suspended := by
  decide +kernel

/-- **The general solver refutes it**: intersection makes `F` constant, and `F x x ≐ x` has no constant solution. -/
theorem diagonal_refuted : (run generalOnly diagonalStore 8).readout = .refuted := by decide +kernel

theorem diagonal_unsolvable : ¬ (frames setting.levels).Solvable diagonalStore :=
  Outcome.readout_eq_refuted diagonal_refuted

/-- The intersection equation, then `λ x y. F x y ≐ λ x y. x`. -/
def projectionStore : EquationStore (TotalTerm withBinary) :=
  [intersectionEquation,
   (termIn withBinary binaryHere (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn withBinary binaryHere (.lam (.lam (.var 1))) (by decide +kernel))]

theorem projection_cumulative_refuted :
    (run ContextualDependentCumulative.Controls.cumulativeOnly projectionStore 8).readout = .refuted := by
  decide +kernel

theorem projection_refuted : (run generalOnly projectionStore 8).readout = .refuted := by decide +kernel

end ContextualDependentIntersectionGeneral.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
