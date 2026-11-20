import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationInputs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Whole

/-!
# Checked source definitions execute through their proved compilation

The source is the existing row checker and compiler, not an arbitrary typed
implementation supplied for a recursive-function variable. Every checked
compiler output, at arguments typed along its source telescope, starts the
general computation profile. Answers correspond to actual full-step runs and
retain the source definition's computed result type.

This is the compiler interpretation within the unchanged qualified vectors
package. It does not infer qualification of the different construction that
extends the package with new constants and their equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.CheckedDefinitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing
open NativeTypesOnTheStep.Computing.Definitions
open TelescopeAbstraction (applyClosed)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg)

abbrev setting := Controls.setting
abbrev qualified := Controls.qualified
abbrev presentation := Controls.presentation

def sourceFrame {b : Nat} (definition : Vectors.Checker.Definition)
    (formed : CtxFormed pkg (baseCtx definition b)) : Context pkg :=
  ⟨b, baseCtx definition b, formed⟩

def input {definition : Vectors.Checker.Definition} {b : Nat} {compiled : Tower.Tm b}
    (checked : Checked definition b compiled) (formed : CtxFormed pkg (baseCtx definition b))
    {arguments : Sub Tower.Head definition.arity b}
    (typedArguments : SubstMor pkg definition.telescope (baseCtx definition b) arguments) :
    Configuration (S := setting) :=
  Configuration.ofTyped (sourceFrame definition formed) (call_typed checked typedArguments)

theorem input_is_compiled_call {definition : Vectors.Checker.Definition} {b : Nat} {compiled : Tower.Tm b}
    (checked : Checked definition b compiled) (formed : CtxFormed pkg (baseCtx definition b))
    {arguments : Sub Tower.Head definition.arity b}
    (typedArguments : SubstMor pkg definition.telescope (baseCtx definition b) arguments) :
    (input checked formed typedArguments).code = applyClosed definition.telescope arguments compiled := rfl

theorem checked_call_answers {definition : Vectors.Checker.Definition} {b : Nat} {compiled : Tower.Tm b}
    (checked : Checked definition b compiled) (formed : CtxFormed pkg (baseCtx definition b))
    {arguments : Sub Tower.Head definition.arity b}
    (typedArguments : SubstMor pkg definition.telescope (baseCtx definition b) arguments)
    (value : Tower.Tm b) :
    Answer pkg (applyClosed definition.telescope arguments compiled) value ↔
      ∃ run : (step setting.levels Nat).toStep.Run (input checked formed typedArguments).state,
        ∃ profile : RunProfile qualified presentation (input checked formed typedArguments) run,
          profile.execution.term = value ∧ ConstructorSystem.Normal pkg profile.execution.term :=
  full_answers_iff qualified presentation (configuration := input checked formed typedArguments)

theorem checked_run_at_source_type {definition : Vectors.Checker.Definition} {b : Nat} {compiled : Tower.Tm b}
    (checked : Checked definition b compiled) (formed : CtxFormed pkg (baseCtx definition b))
    {arguments : Sub Tower.Head definition.arity b}
    (typedArguments : SubstMor pkg definition.telescope (baseCtx definition b) arguments)
    {run : (step setting.levels Nat).toStep.Run (input checked formed typedArguments).state}
    (profile : RunProfile qualified presentation (input checked formed typedArguments) run) :
    Typed pkg (baseCtx definition b) profile.execution.term (subst arguments definition.result) :=
  full_run_typed qualified presentation profile

theorem checked_run_unique {definition : Vectors.Checker.Definition} {b : Nat} {compiled : Tower.Tm b}
    (checked : Checked definition b compiled) (formed : CtxFormed pkg (baseCtx definition b))
    {arguments : Sub Tower.Head definition.arity b}
    (typedArguments : SubstMor pkg definition.telescope (baseCtx definition b) arguments)
    {first second : Tower.Tm b}
    (firstAnswer : Answer pkg (input checked formed typedArguments).code first)
    (secondAnswer : Answer pkg (input checked formed typedArguments).code second) : first = second :=
  (call_answer checked formed typedArguments secondAnswer).2.2 _ firstAnswer

theorem insufficient_budget_is_not_refusal :
    qualify 0 addDef = .undecided .rows ∧ qualify 16 addDef = .function true :=
  ⟨add_budget, add_verdict⟩

theorem wrong_recursive_definition_refused : Vectors.Checker.checkDefinition 16 Vectors.Checker.keepDef = .refused 0 :=
  keep_refused_by_rows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.CheckedDefinitions

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.CheckedDefinitions.checked_call_answers
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.CheckedDefinitions.checked_run_at_source_type
