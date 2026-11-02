import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderEpoch

/-! Pattern-success coverage survives replacement provider tables because
the actual compiled pattern rows and signatures are retained. Thus every
settled epoch, including epochs after prior cached answers, authorizes only
source pattern failures.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem epoch_match_success_step (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (bindings : List OCaml.Value) (body : OCaml.Code)
    (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest])
      (node "MlEvaluate" [code body, environment (OCaml.extend capturedEnvironment bindings), encodedRest]) := by
  obtain ⟨ordinal, row, selected, authored⟩ := epoch_pattern_row program prepared table index parameter
    ((patternRules index parameter)[0]'(by simp [patternRules])) built complete signatures indexed (List.getElem_mem _)
  obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
  obtain ⟨trace, captured, firing⟩ := match_one_plan_coverage selected terms types authored referenced resolved matched
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms := terms
  exact GeneralOccurrenceSemantics.root_firing_step selected rfl
    (match_request_open _ grammar _ referenced argument body capturedEnvironment rest encodedRest resolved) firing

theorem settled_epoch_match_failure (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (machine : Complete.Classes.Machine (epochPlan prepared table))
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (epochComplete : (epochPlan prepared table).complete = true)
    (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Classes.search (epochPlan prepared table) [] (.base "MlConfig")) machine)
    (done : machine.phase = .done)
    (atRequest : machine.state = node "MlMatchOne"
      [patternId index, value argument, code body, environment capturedEnvironment, encodedRest]) :
    OCaml.matchPattern parameter argument = none := by
  have noStep := Complete.Classes.done_no_step (epochPlan prepared table) [] (.base "MlConfig")
    (Complete.Predecessors.equationsChecked_of_complete epochComplete) reached done
  cases matched : OCaml.matchPattern parameter argument with
  | none => rfl
  | some bindings =>
    have step := epoch_match_success_step program prepared table index parameter argument bindings body capturedEnvironment rest encodedRest
      built complete signatures indexed referenced resolved matched
    rw [← atRequest] at step
    exact False.elim (noStep _ step)

#print axioms epoch_match_success_step
#print axioms settled_epoch_match_failure

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
