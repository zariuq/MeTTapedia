import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.CheckedCalls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.FormationConversion

/-!
# Convertible arguments can retain divergence

The actual row-answer theorem allows arguments merely convertible to supplied
typed arguments. A call of checked addition meets that premise and has an
answer, while also having an infinite directed execution inside its argument.
Consequently that premise does not license a strongly normalizing evaluation
strategy or identify the behavior of every reduction schedule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.ConvertibleArguments

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open NativeTypesOnTheStep.Computing NativeTypesOnTheStep.Computing.Definitions
open NativeTypesOnTheStep.Computing.DirectedAnswers
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg D)
open TowerVectorsModel (zeroC)

abbrev delta : Tower.Tm 0 := FormationSensitive.Examples.ConversionCollapse.delta
abbrev omega : Tower.Tm 0 := FormationSensitive.Examples.ConversionCollapse.omega

theorem omega_reduces_to_itself (rules : Rules Tower.Head) :
    StrongNormalization.Reduces rules omega omega := by
  simpa [omega, delta, FormationSensitive.Examples.ConversionCollapse.omega,
    FormationSensitive.Examples.ConversionCollapse.delta, inst0, subst, subst0] using
    (StepCore.betaPi (root := rules.computation) (headEq := StrongNormalization.noHeadSteps)
      (.app (.var 0) (.var 0)) delta)

def delayedZero : Tower.Tm 0 := .app (.lam zeroC) omega

theorem delayed_reduces_zero (rules : Rules Tower.Head) :
    StrongNormalization.Reduces rules delayedZero zeroC := by
  simpa [delayedZero, zeroC, inst0, subst, subst0] using
    (StepCore.betaPi (root := rules.computation) (headEq := StrongNormalization.noHeadSteps)
      (zeroC : Tower.Tm 1) omega)

theorem delayed_self_step (rules : Rules Tower.Head) :
    StrongNormalization.Reduces rules delayedZero delayedZero :=
  .congAppArg (omega_reduces_to_itself rules)

theorem argument_conversion : Conv addAppendExt.headEq delayedZero zeroC addAppendExt.computation :=
  conv_of_stepStar (.single (step_of_reduces (delayed_reduces_zero addAppendExt)))

def sourceCall : Tower.Tm 0 := spine (.const addName) [delayedZero, zeroC]

theorem row_call_has_answer : ∃ value, DirectedAnswer addAppendExt sourceCall value := by
  obtain ⟨k, _, answer, _⟩ := add_rows_answer (a := delayedZero) (b := zeroC)
    D.zero_typed D.zero_typed argument_conversion (.refl _)
  exact ⟨_, answer⟩

theorem row_call_self_step : StrongNormalization.Reduces addAppendExt sourceCall sourceCall :=
  .congAppFun (.congAppArg (delayed_self_step addAppendExt))

theorem row_call_not_strongly_normalizing :
    ¬ Acc (fun after before : Tower.Tm 0 => StrongNormalization.Reduces addAppendExt before after) sourceCall :=
  not_acc_iff_exists_descending_chain.mpr ⟨fun _ => sourceCall, rfl, fun _ => row_call_self_step⟩

/-- Both the completeness class and the argument-conversion premises really
hold; the source nevertheless has a diverging schedule as well as an answer. -/
theorem answer_license_is_not_progress_license :
    RowsReach addDef addTerm addName addAppendRows 1 0 ∧
      SubstMor pkg addDef.telescope .nil (addArgs zeroC zeroC) ∧
      (∀ x, Conv addAppendExt.headEq (addArgs delayedZero zeroC x) (addArgs zeroC zeroC x)
        addAppendExt.computation) ∧
      (∃ value, DirectedAnswer addAppendExt sourceCall value) ∧
      ¬ Acc (fun after before : Tower.Tm 0 => StrongNormalization.Reduces addAppendExt before after) sourceCall := by
  refine ⟨add_rowsReach, addArgs_typed D.zero_typed D.zero_typed, ?_,
    row_call_has_answer, row_call_not_strongly_normalizing⟩
  intro x
  fin_cases x
  · exact .refl _
  · exact argument_conversion

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.ConvertibleArguments

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.ConvertibleArguments.answer_license_is_not_progress_license
