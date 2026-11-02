import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureInstall
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlProviderPlanWire
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochInvariant
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlNormalizedFailure

/-! Actual loaded cache execution is joined to the independent source
failure proof, typed epoch admission and stable provider row positions.
The surrounding controller still needs its runner and dispatch theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAuthorizedCacheExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit

theorem authorized_match_cache_returns (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (machine : Complete.Classes.Machine (epochPlan prepared table))
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (signatures : table.signatures = provider.signatures)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (sound : FailureRowsSound (patterns program) table)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (done : machine.phase = .done)
    (atRequest : machine.state = node "MlMatchOne"
      [patternId index, value argument, code body, environment capturedEnvironment, encodedRest]) :
    let next := ProviderAppend.appendRows table [failureRow index argument]
    let fields := OCamlProviderPlanWire.fields (epochPlan prepared table) (.base "MlConfig")
    OCaml.matchPattern parameter argument = none ∧
      (epochPlan prepared next).complete = true ∧ FailureRowsSound (patterns program) next ∧
      (∀ position, position < table.rows.length → next.rows[position]? = table.rows[position]?) ∧
      PureReturns OCamlControllerSource.runtime [] state
        (apply "gslt:provider-cache:append"
          [encoded (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")),
           encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm [failureRow index argument])]) state
        (encoded (.application "Some" [ProviderCacheExecution.planTerm prepared.compiled [] [] next fields])) := by
  have epochComplete := epoch_complete prepared table signatures complete closed
  have failed := normalized_match_failure program prepared table .canonical index parameter argument body capturedEnvironment rest encodedRest
    machine built complete epochComplete signatures indexed referenced resolved reached done atRequest
  have retained := failure_epoch_invariant program prepared table index parameter argument built complete signatures closed sound indexed failed
  obtain ⟨_, _, terms, _⟩ := prepare_readback program prepared built
  refine ⟨failed, retained.1, retained.2.1, retained.2.2.2, ?_⟩
  have appended := OCamlFailureInstall.append_returns state prepared.compiled terms [] table
    (OCamlProviderPlanWire.fields (epochPlan prepared table) (.base "MlConfig")) signatures index argument
  have wire : ProviderCacheExecution.planTerm prepared.compiled [] [] table
      (OCamlProviderPlanWire.fields (epochPlan prepared table) (.base "MlConfig")) =
      CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig") :=
    OCamlProviderPlanWire.emitted_plan_exact (epochPlan prepared table) [] [] (.base "MlConfig")
  rw [wire] at appended
  exact appended

#print axioms authorized_match_cache_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAuthorizedCacheExecution
