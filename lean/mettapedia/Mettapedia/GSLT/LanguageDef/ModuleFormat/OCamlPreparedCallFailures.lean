import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedFunctionSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlNormalizedFailure

/-! A settled actual normalized pattern request authorizes a source
match-failure step for closure and let calls. Source faults are not inferred
from an unfinished search or from exhausted evaluation fuel.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_settled_pattern_failure (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern)
    (argument : OCaml.Value) (body : OCaml.Code) (capturedEnvironment : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (machine : Complete.Classes.Machine (epochPlan prepared table))
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (done : machine.phase = .done)
    (atRequest : machine.state = node "MlMatchOne"
      [patternId index, value argument, code body, environment capturedEnvironment, encodedRest]) :
    OCaml.matchPattern parameter argument = none :=
  normalized_match_failure program prepared table .canonical index parameter argument body capturedEnvironment rest encodedRest machine
    built (prepared_plan_complete program prepared built) (prepared_epoch_complete program prepared table built signatures closed)
    signatures indexed referenced resolved reached done atRequest

theorem settled_lambda_failure_source_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (reference body index : Nat) (parameter : OCaml.MatchPattern)
    (argument : OCaml.Value) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (machine : Complete.Classes.Machine (epochPlan prepared table)) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (declared : program.instruction? reference = some (.lambda parameter body))
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (done : machine.phase = .done)
    (atRequest : machine.state = node "MlMatchOne"
      [patternId index, value argument, code body, environment capturedEnvironment, encodedRest]) :
    OCaml.machineStep program (.returned (.closure (.lambda reference) capturedEnvironment) (.function argument :: rest)) =
      .ok (some (.halted (.error .matchFailure))) := by
  have failed := prepared_settled_pattern_failure program prepared table index parameter argument body capturedEnvironment rest encodedRest
    machine built signatures closed indexed referenced resolved reached done atRequest
  simp [OCaml.machineStep, OCaml.returnValue, OCaml.applyClosure, declared, OCaml.enterBody, failed]
  rfl

theorem settled_let_failure_source_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (body index : Nat) (parameter : OCaml.MatchPattern)
    (argument : OCaml.Value) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (machine : Complete.Classes.Machine (epochPlan prepared table)) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (done : machine.phase = .done)
    (atRequest : machine.state = node "MlMatchOne"
      [patternId index, value argument, code body, environment capturedEnvironment, encodedRest]) :
    OCaml.machineStep program (.returned argument (.letValue parameter body capturedEnvironment :: rest)) =
      .ok (some (.halted (.error .matchFailure))) := by
  have failed := prepared_settled_pattern_failure program prepared table index parameter argument body capturedEnvironment rest encodedRest
    machine built signatures closed indexed referenced resolved reached done atRequest
  simp [OCaml.machineStep, OCaml.returnValue, OCaml.enterBody, failed]
  rfl

theorem settled_recursive_failure_source_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (group groupBody slot reference body index : Nat)
    (definitions : List OCaml.Code) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (machine : Complete.Classes.Machine (epochPlan prepared table)) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (declaredGroup : program.instruction? group = some (.letRecursive definitions groupBody))
    (declaredSlot : definitions[slot]? = some reference)
    (declaredFunction : program.instruction? reference = some (.lambda parameter body))
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (done : machine.phase = .done)
    (atRequest : machine.state = node "MlMatchOne" [patternId index, value argument, code body,
      environment (OCaml.recursiveEnvironment group definitions capturedEnvironment), encodedRest]) :
    OCaml.machineStep program (.returned (.closure (.recursive group slot) capturedEnvironment) (.function argument :: rest)) =
      .ok (some (.halted (.error .matchFailure))) := by
  have failed := prepared_settled_pattern_failure program prepared table index parameter argument body
    (OCaml.recursiveEnvironment group definitions capturedEnvironment) rest encodedRest machine built signatures closed
    indexed referenced resolved reached done atRequest
  simp [OCaml.machineStep, OCaml.returnValue, OCaml.applyClosure, declaredGroup, declaredSlot, declaredFunction, OCaml.enterBody, failed]
  rfl

theorem successful_match_cannot_settle_without_a_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern)
    (argument : OCaml.Value) (bindings : List OCaml.Value) (body : OCaml.Code) (capturedEnvironment : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (machine : Complete.Classes.Machine (epochPlan prepared table))
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (atRequest : machine.state = node "MlMatchOne"
      [patternId index, value argument, code body, environment capturedEnvironment, encodedRest])
    (matched : OCaml.matchPattern parameter argument = some bindings) : machine.phase ≠ .done := by
  intro done
  have failed := prepared_settled_pattern_failure program prepared table index parameter argument body capturedEnvironment rest encodedRest
    machine built signatures closed indexed referenced resolved reached done atRequest
  rw [failed] at matched
  cases matched

#print axioms prepared_settled_pattern_failure
#print axioms settled_lambda_failure_source_step
#print axioms settled_let_failure_source_step
#print axioms settled_recursive_failure_source_step
#print axioms successful_match_cannot_settle_without_a_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
