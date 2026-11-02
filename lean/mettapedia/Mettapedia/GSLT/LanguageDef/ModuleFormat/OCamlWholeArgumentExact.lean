import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEmptyArgumentCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlArgumentReadback

/-! Whole-plan argument entry is two-sided for its actual source row.
Empty entry emits a build request; nonempty entry is the encoded source
gather successor. No execution row is supplied by the caller.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem whole_build_entry_exact (program : OCaml.Program) (prepared : Prepared) (reference : OCaml.Code)
    (kind : OCaml.Build) (arguments : List OCaml.Code) (capturedEnvironment : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (declared : program.instruction? reference = some (buildInstruction kind arguments))
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ (ordinal : Nat) (row : GeneralExecutionAdmission.RulePlan), (plan prepared).rules[ordinal]? = some row ∧
      compileInstruction? (patterns program) reference (buildInstruction kind arguments) = some row.authored ∧
      ∀ target, (∃ trace captured completed history,
        GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (plan prepared)) [] (.base "MlConfig")
          (node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest]) ordinal
          trace captured completed history target) ↔
        target = startArguments (build kind) arguments (environment capturedEnvironment) encodedRest := by
  obtain ⟨ordinal, row, selected, formed, _⟩ :=
    whole_plan_instruction program prepared reference (buildInstruction kind arguments) built declared complete
  obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
  refine ⟨ordinal, row, selected, formed, ?_⟩
  intro target
  constructor
  · rintro ⟨trace, captured, completed, history, firing⟩
    exact (build_instruction_firing_readback selected terms types formed firing).2.2
  · rintro rfl
    cases reversed : arguments.reverse with
    | nil =>
      have empty : arguments = [] := List.reverse_eq_nil_iff.mp reversed
      subst arguments
      obtain ⟨trace, captured, firing⟩ := empty_build_instruction_plan_step selected terms types formed resolved
      exact ⟨trace, captured, captured, [], firing⟩
    | cons last later =>
      obtain ⟨trace, captured, firing⟩ := build_instruction_plan_step selected terms types reversed formed resolved
      exact ⟨trace, captured, captured, [], firing⟩

theorem build_entry_encoding (program : OCaml.Program) (kind : OCaml.Build) (arguments : List OCaml.Code)
    (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    (arguments = [] ∧ startArguments (build kind) arguments (environment capturedEnvironment) encodedRest =
        node "MlBuildConfig" [build kind, valueList [], encodedRest]) ∨
      ∃ last later, arguments.reverse = last :: later ∧
        OCaml.startArguments program kind arguments capturedEnvironment rest =
          .ok (.evaluate last capturedEnvironment (.gather kind later capturedEnvironment [] :: rest)) ∧
        state? (patterns program) (.evaluate last capturedEnvironment (.gather kind later capturedEnvironment [] :: rest)) =
          some (startArguments (build kind) arguments (environment capturedEnvironment) encodedRest) := by
  cases reversed : arguments.reverse with
  | nil =>
    have empty : arguments = [] := List.reverse_eq_nil_iff.mp reversed
    subst arguments
    exact Or.inl ⟨rfl, rfl⟩
  | cons last later =>
    refine Or.inr ⟨last, later, rfl, ?_, ?_⟩
    · simp only [OCaml.startArguments, reversed]
    · exact start_arguments_nonempty_encoding (patterns program) kind arguments last later capturedEnvironment rest encodedRest reversed resolved

#print axioms whole_build_entry_exact
#print axioms build_entry_encoding

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
