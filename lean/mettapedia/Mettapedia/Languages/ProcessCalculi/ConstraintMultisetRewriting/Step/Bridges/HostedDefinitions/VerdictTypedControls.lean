import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.VerdictProgramProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.CheckedRowsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalTypingControls

/-!
# Compiled append remains typed inside actual mixed developments

Append's checked result type uses the compiled addition export. Its actual
public query returns the dependent vector result, even in a fresh development
whose unrelated raw row is refused by typing qualification. Named raw calls
retain their separately proved declaration and agreement conditions.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.VerdictTypedControls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing NativeTypesOnTheStep.Computing.Definitions
open NativeTypesOnTheStep.Computing.DirectedAnswers
open TelescopeAbstraction (applyClosed)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (two twoThree single)

abbrev built := CheckedRowsControls.built
abbrev supply := CheckedRowsControls.supply
abbrev compiledAppendCall : Tower.Tm 0 := applyClosed appendRDef.telescope groundSub appendRTerm

theorem append_checked_and_old : Checked appendRDef 0 appendRTerm ∧ OldTerm addAppendDev compiledAppendCall :=
  ⟨appendR_checked, (VerdictTypedCalls.compiled_call_typed_old addAppend_fresh appendR_checked groundSub_typed).2⟩

theorem append_public_iff_native (result : Tower.Tm 0) :
    NormalTypedExecution.Answer built untyped.discipline Hosting.mettaNodes compiledAppendCall result ↔
      CheckedCalls.NativeAnswer appendR_checked groundSub_typed result :=
  VerdictTypedCalls.compiled_public_iff_checked_native built untyped.discipline Hosting.mettaNodes supply
    addAppend_devCheck addAppend_fresh appendR_checked groundSub_typed result

theorem append_public_returns :
    NormalTypedExecution.Answer built untyped.discipline Hosting.mettaNodes compiledAppendCall twoThree :=
  (append_public_iff_native twoThree).mpr Controls.CheckedCalls.append_native_answer

theorem append_public_result_typed :
    Typed (devPackage addAppendDev built.nativeRows) .nil twoThree (subst groundSub appendRDef.result) :=
  (VerdictTypedCalls.compiled_public_answer_typed built untyped.discipline Hosting.mettaNodes supply
    addAppend_devCheck addAppend_fresh appendR_checked groundSub_typed append_public_returns).2.1

theorem append_actual_source_run :
    ∃ after branch,
      Runs untyped.discipline (NormalProgram.program built untyped.discipline) supply
        (Config.initial (fun _ => 0) (NormalProgram.query built compiledAppendCall)) after ∧
      branch ∈ after.branches ∧ branch.Finished (D := untyped.discipline) ∧ Solvable branch.store ∧
      encodeTm (twoThree : Tower.Tm 0) ∈ branch.answer (D := untyped.discipline) := by
  have baseAnswer := (CheckedCalls.compiled_answer_iff_native appendR_checked groundSub_typed twoThree).mpr
    Controls.CheckedCalls.append_native_answer
  have extended := (VerdictTypedCalls.old_directedAnswer_iff addAppend_devCheck built.native append_checked_and_old.2).mpr baseAnswer
  exact NormalEvaluatorPublic.public_source_executes built untyped.discipline supply extended.1 extended.2

theorem shorter_public_answer_impossible :
    ¬ NormalTypedExecution.Answer built untyped.discipline Hosting.mettaNodes compiledAppendCall (single two) := by
  intro answered
  exact Controls.CheckedCalls.shorter_native_answer_refused ((append_public_iff_native _).mp answered)

theorem append_source_normalizes_if_baseAcc (normalizing : StrongNormalization.SN pkg compiledAppendCall) :
    Acc (fun after before => SourceLanguage.Step untyped.discipline
      (NormalProgram.program built untyped.discipline) supply before after)
      (Config.initial (fun _ => 0) (NormalProgram.query built compiledAppendCall)) :=
  VerdictProgramProgress.compiled_source_normalizes built untyped.discipline supply addAppend_devCheck addAppend_fresh
    appendR_checked groundSub_typed normalizing

theorem append_controller_normalizes_if_baseAcc (normalizing : StrongNormalization.SN pkg compiledAppendCall) :
    Acc (fun after before => (FrontierArrow.target (D := untyped.discipline) Hosting.mettaNodes
      (NormalProgram.program built untyped.discipline)).Step before after)
      (FrontierArrow.initialState (D := untyped.discipline) Hosting.mettaNodes
        (NormalProgram.program built untyped.discipline) (NormalProgram.query built compiledAppendCall)) :=
  VerdictProgramProgress.compiled_controller_normalizes built untyped.discipline Hosting.mettaNodes supply
    addAppend_devCheck addAppend_fresh appendR_checked groundSub_typed normalizing

def badBuilt : Compiled NormalTypingControls.badDev :=
  (compile NormalTypingControls.badDev).get (by decide +kernel)

theorem refused_raw_row_and_typed_compiled_execution :
    qualify 16 Vectors.Checker.keepDef = .refused 0 ∧
      NormalTypedExecution.Answer badBuilt untyped.discipline Hosting.mettaNodes compiledAppendCall twoThree ∧
      Typed (devPackage NormalTypingControls.badDev badBuilt.nativeRows) .nil twoThree (subst groundSub appendRDef.result) := by
  have answered := (VerdictTypedCalls.compiled_public_iff_checked_native badBuilt untyped.discipline Hosting.mettaNodes supply
    NormalTypingControls.bad_structurally_checked NormalTypingControls.bad_name_fresh appendR_checked groundSub_typed twoThree).mpr
      Controls.CheckedCalls.append_native_answer
  have typed := (VerdictTypedCalls.compiled_public_answer_typed badBuilt untyped.discipline Hosting.mettaNodes supply
    NormalTypingControls.bad_structurally_checked NormalTypingControls.bad_name_fresh appendR_checked groundSub_typed answered).2.1
  exact ⟨NormalTypingControls.bad_typing_refused, answered, typed⟩

theorem raw_name_not_old : ¬ OldTerm addAppendDev (.const addName : Tower.Tm 0) := by
  intro old
  exact (old (addName, addDef) List.mem_cons_self) rfl

theorem raw_partial_does_not_equal_compiled_interpretation :
    ¬ Conv (devPackage addAppendDev addAppendRows).headEq
      (.app (.const addName) ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.one : Tower.Tm 0)
      (.app addTerm ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.one)
      (devPackage addAppendDev addAppendRows).computation :=
  Definitions.partial_not_convertible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.VerdictTypedControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.VerdictTypedControls.append_actual_source_run
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.VerdictTypedControls.refused_raw_row_and_typed_compiled_execution
