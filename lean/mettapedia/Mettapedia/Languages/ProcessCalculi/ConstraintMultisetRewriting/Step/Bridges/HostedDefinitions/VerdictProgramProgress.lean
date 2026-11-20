import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.VerdictTypedCalls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorProgress

/-!
# Checked compiled calls inherit actual hosted accessibility

Directed reflection on old terms pulls genuine base accessibility into the
mixed development. The actual normal-profile source query and controller
then inherit it. Verdict typing supplies the old-term licence; no global
qualification or normalization of the new raw rows is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.VerdictProgramProgress

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open TelescopeAbstraction (applyClosed)
open AlgebraicSchema (SchemaTable)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg)

theorem old_nativeAcc {dev : Definitions.Development} (checked : Definitions.devCheck dev = true)
    {rows : SchemaTable Tower.Head} (found : Definitions.devRules dev = some rows)
    {n : Nat} {term : Tower.Tm n} (old : Definitions.OldTerm dev term)
    (normalizing : StrongNormalization.SN pkg term) : StrongNormalization.SN (Definitions.devPackage dev rows) term := by
  revert old
  induction normalizing with
  | intro current _ smaller =>
      intro old
      refine Acc.intro current ?_
      intro after step
      obtain ⟨baseStep, resultOld⟩ := VerdictTypedCalls.old_directed_step checked found old step
      exact smaller after baseStep resultOld

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (N : Hosting.Nodes MSig [] ()) (supply : Nat → MClosed)
  (checkedDev : Definitions.devCheck dev = true) (fresh : Definitions.devFresh dev = true)

include checkedDev fresh

theorem compiled_source_normalizes {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0}
    (checked : Definitions.Checked definition 0 compiled)
    {arguments : Sub Tower.Head definition.arity 0} (typedArguments : SubstMor pkg definition.telescope .nil arguments)
    (normalizing : StrongNormalization.SN pkg (applyClosed definition.telescope arguments compiled)) :
    Acc (fun after before => SourceLanguage.Step D (NormalProgram.program built D) supply before after)
      (Config.initial (fun _ => 0) (NormalProgram.query built (applyClosed definition.telescope arguments compiled))) :=
  NormalEvaluatorProgress.source_normalizes built D supply _
    (old_nativeAcc checkedDev built.native (VerdictTypedCalls.compiled_call_typed_old fresh checked typedArguments).2 normalizing)

include supply in
theorem compiled_controller_normalizes {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0}
    (checked : Definitions.Checked definition 0 compiled)
    {arguments : Sub Tower.Head definition.arity 0} (typedArguments : SubstMor pkg definition.telescope .nil arguments)
    (normalizing : StrongNormalization.SN pkg (applyClosed definition.telescope arguments compiled)) :
    Acc (fun after before => (FrontierArrow.target (D := D) N (NormalProgram.program built D)).Step before after)
      (FrontierArrow.initialState (D := D) N (NormalProgram.program built D)
        (NormalProgram.query built (applyClosed definition.telescope arguments compiled))) :=
  NormalEvaluatorProgress.native_normalizes built D supply N _
    (old_nativeAcc checkedDev built.native (VerdictTypedCalls.compiled_call_typed_old fresh checked typedArguments).2 normalizing)

include supply in
theorem compiled_has_typed_public_answer {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0}
    (checked : Definitions.Checked definition 0 compiled)
    {arguments : Sub Tower.Head definition.arity 0} (typedArguments : SubstMor pkg definition.telescope .nil arguments)
    (normalizing : StrongNormalization.SN pkg (applyClosed definition.telescope arguments compiled)) :
    ∃ result, NormalTypedExecution.Answer built D N (applyClosed definition.telescope arguments compiled) result ∧
      CheckedCalls.NativeAnswer checked typedArguments result ∧
      Typed pkg .nil result (subst arguments definition.result) ∧
      Typed (Definitions.devPackage dev built.nativeRows) .nil result (subst arguments definition.result) ∧
      Equal (Definitions.devPackage dev built.nativeRows) .nil
        (applyClosed definition.telescope arguments compiled) result (subst arguments definition.result) := by
  obtain ⟨result, answer⟩ := DirectedAnswers.exists_of_sn normalizing
  have old := (VerdictTypedCalls.compiled_call_typed_old fresh checked typedArguments).2
  have extended := (VerdictTypedCalls.old_directedAnswer_iff checkedDev built.native old).mpr answer
  have publicAnswer := (NormalTypedExecution.answer_iff built D N supply _ _).mpr extended
  have native := (VerdictTypedCalls.compiled_public_iff_checked_native built D N supply checkedDev fresh checked
    typedArguments result).mp publicAnswer
  exact ⟨result, publicAnswer, native, VerdictTypedCalls.compiled_public_answer_typed built D N supply checkedDev fresh checked
    typedArguments publicAnswer⟩

theorem compiled_has_typed_source_answer {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0}
    (checked : Definitions.Checked definition 0 compiled)
    {arguments : Sub Tower.Head definition.arity 0} (typedArguments : SubstMor pkg definition.telescope .nil arguments)
    (normalizing : StrongNormalization.SN pkg (applyClosed definition.telescope arguments compiled)) :
    ∃ after branch result,
      Runs D (NormalProgram.program built D) supply
        (Config.initial (fun _ => 0) (NormalProgram.query built (applyClosed definition.telescope arguments compiled))) after ∧
      branch ∈ after.branches ∧ branch.Finished (D := D) ∧ Solvable branch.store ∧
      encodeTm result ∈ branch.answer (D := D) ∧
      Typed (Definitions.devPackage dev built.nativeRows) .nil result (subst arguments definition.result) := by
  obtain ⟨result, answer⟩ := DirectedAnswers.exists_of_sn normalizing
  have call := VerdictTypedCalls.compiled_call_typed_old fresh checked typedArguments
  have extended := (VerdictTypedCalls.old_directedAnswer_iff checkedDev built.native call.2).mpr answer
  obtain ⟨after, branch, run, member, finished, live, read⟩ :=
    NormalEvaluatorPublic.public_source_executes built D supply extended.1 extended.2
  have oldSteps := (Definitions.dev_stepStar_old checkedDev built.native extended.stepStar call.2).1
  have resultTyped := (Vectors.vectors_subjectReduction
    ProgrammingOnTheStep.IndexedFamilies.Eliminator.level1 .nil oldSteps call.1).1
  exact ⟨after, branch, result, run, member, finished, live, read, Definitions.typed_dev fresh built.nativeRows resultTyped⟩

include supply in
theorem verdict_closed (fuel : Nat) (definition : Vectors.Checker.Definition)
    (verdict : Definitions.qualify fuel definition = .function true) :
    ∃ compiled : Tower.Tm 0, Definitions.compile 0 definition = some compiled ∧
      Definitions.Checked definition 0 compiled ∧
      ∀ (arguments : Sub Tower.Head definition.arity 0)
        (_typedArguments : SubstMor pkg definition.telescope .nil arguments),
        Definitions.OldTerm dev (applyClosed definition.telescope arguments compiled) ∧
        (∀ result, NormalTypedExecution.Answer built D N (applyClosed definition.telescope arguments compiled) result →
          Typed (Definitions.devPackage dev built.nativeRows) .nil result (subst arguments definition.result)) ∧
        (StrongNormalization.SN pkg (applyClosed definition.telescope arguments compiled) →
          Acc (fun after before => SourceLanguage.Step D (NormalProgram.program built D) supply before after)
            (Config.initial (fun _ => 0) (NormalProgram.query built (applyClosed definition.telescope arguments compiled))) ∧
          Acc (fun after before => (FrontierArrow.target (D := D) N (NormalProgram.program built D)).Step before after)
            (FrontierArrow.initialState (D := D) N (NormalProgram.program built D)
              (NormalProgram.query built (applyClosed definition.telescope arguments compiled))) ∧
          ∃ result, NormalTypedExecution.Answer built D N (applyClosed definition.telescope arguments compiled) result ∧
            Typed (Definitions.devPackage dev built.nativeRows) .nil result (subst arguments definition.result)) := by
  obtain ⟨compiled, checked⟩ := Definitions.qualify_closed verdict
  refine ⟨compiled, checked.compiled, checked, ?_⟩
  intro arguments typedArguments
  refine ⟨(VerdictTypedCalls.compiled_call_typed_old fresh checked typedArguments).2, ?_, ?_⟩
  · intro result answered
    exact (VerdictTypedCalls.compiled_public_answer_typed built D N supply checkedDev fresh checked typedArguments answered).2.1
  · intro normalizing
    obtain ⟨result, answered, _, _, typed, _⟩ :=
      compiled_has_typed_public_answer built D N supply checkedDev fresh checked typedArguments normalizing
    exact ⟨compiled_source_normalizes built D supply checkedDev fresh checked typedArguments normalizing,
      compiled_controller_normalizes built D N supply checkedDev fresh checked typedArguments normalizing, result, answered, typed⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.VerdictProgramProgress

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.VerdictProgramProgress.old_nativeAcc
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.VerdictProgramProgress.verdict_closed
