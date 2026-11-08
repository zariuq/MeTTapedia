import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance3
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMillerClosureReorderOutside

/-!
# The cumulative round does not keep `MillerNormal`

The reorder witness is a `MillerNormal` store: it is in the stratified Miller class (`reorder_stratifiedMiller`), and its
opened sides are β-normal already (`reorder_openedNormal`). At budget 16 the cumulative round answers `X` in place
(R86) and leaves a residual store outside the class (`cumulativeRound_leaves_class`). So the closure hypothesis of
`ContextualDependentAcceptance3.inPlace_decided_of_cumulative` fails in the tower (`cumulativeRound_not_keeps`): that
reduction, on `MillerNormal`, cannot be discharged, and the corrected reduction is
`ContextualDependentAcceptance3.anywhere_decided_of_cumulative`, on the permuted class.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentMillerClosure.ReorderControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentCumulative

/-- The executable normalizer reaches a normal form of the code. -/
def reachesNormal {n : Nat} (code : Tower.Tm n) : Bool :=
  match ContextualDependentExecutableConversion.red (L := Nat) 64 code with
  | some result => (ExecutableReduction.step Tower.rules (fun _ => none) result.val).isNone
  | none => false

theorem reachesNormal_sound {n : Nat} {code : Tower.Tm n} (check : reachesNormal code = true) :
    ∃ opened, ContextualDependentExecutableJoin.Star (R := Tower.rules) code opened ∧
      ContextualDependentExecutableJoin.Normal Tower.rules opened := by
  unfold reachesNormal at check
  cases computed : ContextualDependentExecutableConversion.red (L := Nat) 64 code with
  | none =>
      rw [computed] at check
      cases check
  | some result =>
      rw [computed] at check
      exact ⟨result.val, ContextualDependentExecutableConversion.normalize_star 64 computed,
        (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (Option.isNone_iff_eq_none.mp check)⟩

/-- **The opened sides of the reorder witness have normal reducts.** -/
theorem reorder_openedNormal : OpenedNormal (S := setting) reorderStore := by
  intro equation member
  have reaches : ∀ equation ∈ reorderStore,
      (reachesNormal (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) &&
        reachesNormal (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code)) =
          true := by
    decide +kernel
  have both := reaches equation member
  simp only [Bool.and_eq_true] at both
  exact ⟨reachesNormal_sound both.1, reachesNormal_sound both.2⟩

/-- The cumulative round of the tower controls at budget 16. -/
noncomputable def cumulativeAt16 {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  cumulativeRound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) 16 problem

noncomputable def cumulativeOutside : Bool :=
  match cumulativeAt16 reorderStore with
  | .progress update _ => outsideCheck update.remaining
  | _ => false

theorem cumulativeOutside_true : cumulativeOutside = true := by decide +kernel

/-- **The cumulative round takes the reorder witness out of the class.** -/
theorem cumulativeRound_leaves_class :
    ∃ (update : ContextualDependentUpdate.Update setting.levels reorderStore) (smaller : _),
      cumulativeAt16 reorderStore = .progress update smaller ∧
        ¬ ContextualDependentShortClosure.StratifiedMiller setting.levels update.remaining := by
  have key := cumulativeOutside_true
  unfold cumulativeOutside at key
  generalize ran : cumulativeAt16 reorderStore = outcome at key
  cases outcome with
  | progress update smaller => exact ⟨update, smaller, rfl, not_stratifiedMiller_of_check key⟩
  | refuted _ => simp at key
  | stuck => simp at key

/-- **The closure hypothesis of the reduction on `MillerNormal` fails in the tower**, at budget 16. -/
theorem cumulativeRound_not_keeps :
    ¬ ContextualDependentAcceptance3.KeepsMillerNormal (S := setting) TowerModel.facts TowerModel.roots
      TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      fun problem => cumulativeAt16 problem := by
  intro keeps
  obtain ⟨update, smaller, fired, outside⟩ := cumulativeRound_leaves_class
  exact outside (keeps reorderStore update smaller ⟨reorder_stratifiedMiller, reorder_openedNormal⟩ fired).1

end ContextualDependentMillerClosure.ReorderControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
