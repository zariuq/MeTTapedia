import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRecognitionConversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentCompleteControls

/-!
# Recognition up to conversion on a concrete store

Over `A X : U0`, the equation `X ≐ A` is stated at the universe `sort (max 0 0)`, equal to `sort 0`, the
universe `X` is declared at, but not the same code.

* Syntactic recognition rejects it: the annotation is not the pattern's type.
* Recognition up to conversion accepts it, and the conversion pattern rule solves `X := A`; run alone in
  the driver, it commits with a principal answer.

Every result is computed by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRecognitionConversion.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver ContextualDependentPatternSolver.Controls
open ContextualDependentDecisiveFragment ContextualDependentFragment ContextualDependentFragment.Controls

theorem lifted_universe : setting.R.cumulative (.sort Tower.zero) familyType.level := by decide +kernel

/-- `X` at `sort (max 0 0)`. -/
def highX : Term twoTypes functionUniverse :=
  ⟨.var 0, by rw [functionUniverse_code]; exact .cumul (.var 0) lifted_universe⟩

/-- `A` at `sort (max 0 0)`. -/
def highA : Term twoTypes functionUniverse :=
  ⟨.var 1, by rw [functionUniverse_code]; exact .cumul (.var 1) lifted_universe⟩

/-- The equation `X ≐ A` at `sort (max 0 0)`, read without leading abstractions. -/
def highActive : Active twoTypes := ⟨functionUniverse, highX, highA⟩

/-- **Syntactic recognition rejects it.** -/
theorem syntactic_rejects :
    (recognize (Spine.stop ContextualDependentInversion.Controls.extraType) (Spine.stop functionUniverse)
      highActive).isNone = true := by decide +kernel

/-- **Recognition up to conversion accepts it.** -/
theorem conversion_accepts :
    (recognizeConv (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.reducer 16 (Spine.stop ContextualDependentInversion.Controls.extraType)
      (Spine.stop functionUniverse) highActive).isSome = true := by decide +kernel

/-- `X ≐ A` at `sort (max 0 0)`. -/
def highStore : EquationStore (TotalTerm twoTypes) := [(⟨functionUniverse, highX⟩, ⟨functionUniverse, highA⟩)]

/-- The conversion pattern rule of the controls at one budget. -/
abbrev rule (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  patternRuleConv (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel problem

/-- **The conversion pattern rule solves it**, leaving nothing. -/
theorem conversion_rule_solves :
    (match rule 16 highStore with
      | some (.solved update _) => update.remaining.isEmpty
      | _ => false) = true := by decide +kernel

/-- The conversion pattern rule alone, as a solver. -/
def conversionOnly : Solver setting.levels where
  rank := size
  round problem :=
    match rule 16 problem with
    | some (.solved update smaller) => .progress update (Prod.Lex.left _ _ smaller)
    | some (.refuted absent) => .refuted absent
    | none => .stuck

/-- **Run in the driver, it commits** with a principal answer. -/
theorem high_solved : (run conversionOnly highStore 2).readout = .commit := by decide +kernel

theorem high_principal :
    ∃ state finished, run conversionOnly highStore 2 = .solved state finished ∧
      (frames setting.levels).Principal highStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit high_solved
  exact ⟨state, finished, solved, drive_solved_principal conversionOnly solved⟩

end ContextualDependentRecognitionConversion.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
