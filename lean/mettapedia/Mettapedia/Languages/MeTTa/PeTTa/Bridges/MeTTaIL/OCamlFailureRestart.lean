import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunnerBeginExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochRequestChecks

/-! Actual match and clause requests initialize the next provider epoch
through the common loaded runner. Their representation checks and name
coverage follow from source encodings and prepared vocabulary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureRestart

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit

theorem match_restart_returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    let source := node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest]
    PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:runner:begin" [encoded (.symbol "ClassSearch"),
        encoded (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")),
        encoded (OCamlEpochStandard.standard prepared), encoded (InferenceCettaWire.encodePattern source)]) state
      (encoded (CompleteExecution.classMachineTerm (epochPlan prepared table)
        (OCamlRunnerBeginExecution.begun prepared table source))) := by
  obtain ⟨closed, checked⟩ := epoch_match_request_checked program prepared table index parameter argument body captured rest encodedRest
    built referenced resolved
  exact OCamlRunnerBeginExecution.begin_returns state prepared table _ closed checked

theorem clause_restart_returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (captured : OCaml.Environment) (clauses : List OCaml.Clause) (later : Pattern)
    (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    let source := node "MlTryClause" [patternId index, value argument, code body, later, environment captured, encodedRest]
    PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:runner:begin" [encoded (.symbol "ClassSearch"),
        encoded (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")),
        encoded (OCamlEpochStandard.standard prepared), encoded (InferenceCettaWire.encodePattern source)]) state
      (encoded (CompleteExecution.classMachineTerm (epochPlan prepared table)
        (OCamlRunnerBeginExecution.begun prepared table source))) := by
  obtain ⟨closed, checked⟩ := epoch_clause_request_checked program prepared table index parameter argument body captured clauses later rest encodedRest
    built referenced clauseResolved resolved
  exact OCamlRunnerBeginExecution.begin_returns state prepared table _ closed checked

#print axioms match_restart_returns
#print axioms clause_restart_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureRestart
