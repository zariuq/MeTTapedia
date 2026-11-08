import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralAnywhere
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance3ControlsRest
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMillerClosureReorderControls

/-!
# Controls for intersection anywhere in the store

At budget 16 and eight rounds, over the context of the reorder witness
(`A B : U0, G : U0 → U0 → U0, X : U0, Z : X, Y : G A B, Y' : G B A`):

| Store | In-place solver | Anywhere solver |
|---|---|---|
| `λ x y. G x y ≐ λ x y. G y x`, the twin `Y ≐ Y'`, `X ≐ A` | suspended | commit |
| the same, then `λ x y. G x x ≐ λ x y. x` | suspended | refuted |

The first round answers `X` in place and puts the twin first; the anywhere rule then intersects `G` at the second
equation, which makes the twin's annotations equal.

Wherever the last family decides, the anywhere family decides the same way (`anywhere_of_final`), so the census
results of `ContextualDependentAcceptance3Controls` hold for it as well.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionGeneral.AnywhereControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentIntersectionGeneral.InPlaceControls
open ContextualDependentMillerClosure.ReorderControls

/-- The anywhere solver of the tower controls, as a fuel-indexed family. -/
noncomputable def anywhereTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  anywhereFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The anywhere solver at budget 16. -/
noncomputable def anywhereOnly : Solver setting.levels := anywhereTower.solver 16

/-! ## The reorder witness -/

/-- **The anywhere solver commits on the reorder witness.** -/
theorem reorder_committed : (run anywhereOnly reorderStore 8).readout = .commit := by decide +kernel

/-- `λ x y. G x x ≐ λ x y. x`. -/
def diagonal : Equation (TotalTerm withTwins) :=
  (termIn withTwins binaryTwins (.lam (.lam (.app (.app (.var 6) (.var 1)) (.var 1)))) (by decide +kernel),
    termIn withTwins binaryTwins (.lam (.lam (.var 1))) (by decide +kernel))

/-- The reorder witness, then the diagonal. -/
def reorderDiagonalStore : EquationStore (TotalTerm withTwins) := reorderStore ++ [diagonal]

theorem reorderDiagonal_inPlace_suspended : (run inPlaceOnly reorderDiagonalStore 8).readout = .suspended := by
  decide +kernel

/-- **The anywhere solver refutes the reorder witness with the diagonal.** -/
theorem reorderDiagonal_refuted : (run anywhereOnly reorderDiagonalStore 8).readout = .refuted := by decide +kernel

theorem reorderDiagonal_unsolvable : ¬ (frames setting.levels).Solvable reorderDiagonalStore :=
  Outcome.readout_eq_refuted reorderDiagonal_refuted

/-! ## The census -/

/-- **Every store the last family decides at budget 16, the anywhere family decides the same way.** -/
theorem anywhere_of_final {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (final : ContextualDependentAcceptance3.Controls.finalDecided problem = true) :
    (run inPlaceOnly problem 8).Decided ∧ run anywhereOnly problem 8 = run inPlaceOnly problem 8 := by
  unfold ContextualDependentAcceptance3.Controls.finalDecided at final
  simp only [Bool.and_eq_true] at final
  have decided : (run inPlaceOnly problem 8).Decided := by
    have read := final.1
    generalize run inPlaceOnly problem 8 = outcome at read ⊢
    cases outcome with
    | solved _ _ => exact trivial
    | refuted _ => exact trivial
    | stuck _ => simp [Outcome.readout] at read
    | cutoff _ => simp [Outcome.readout] at read
  exact ⟨decided, anywhere_run_of_inPlace (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) 16 8 problem decided⟩

theorem twice_anywhere :
    (run inPlaceOnly ContextualDependentIntersection.Controls.twiceStore 8).Decided ∧
      run anywhereOnly ContextualDependentIntersection.Controls.twiceStore 8 =
        run inPlaceOnly ContextualDependentIntersection.Controls.twiceStore 8 :=
  anywhere_of_final ContextualDependentAcceptance3.Controls.twice_final

theorem twin_anywhere :
    (run inPlaceOnly ContextualDependentShortClosure.Controls.twinStore 8).Decided ∧
      run anywhereOnly ContextualDependentShortClosure.Controls.twinStore 8 =
        run inPlaceOnly ContextualDependentShortClosure.Controls.twinStore 8 :=
  anywhere_of_final ContextualDependentAcceptance3.Controls.twin_final

theorem witness_anywhere :
    (run inPlaceOnly ContextualDependentInPlaceClosure.witnessStore 8).Decided ∧
      run anywhereOnly ContextualDependentInPlaceClosure.witnessStore 8 =
        run inPlaceOnly ContextualDependentInPlaceClosure.witnessStore 8 :=
  anywhere_of_final ContextualDependentAcceptance3.Controls.witness_final

end ContextualDependentIntersectionGeneral.AnywhereControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
