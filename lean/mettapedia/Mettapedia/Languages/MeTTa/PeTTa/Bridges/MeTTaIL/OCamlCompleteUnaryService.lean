import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveTransition
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlUnaryPrimitives

/-! Public unary service transitions supply actual primitive computation
and source evaluation proofs to the shared epoch and restart composition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompleteUnaryService

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource

theorem negate_service_returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (number : Int) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (signatures : table.signatures = provider.signatures)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (meaning : ProviderMeaning (patterns program) table)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (atRequest : runner.state = node "MlPrimitiveRequest" [primitive .negate, valueList [.literal (.integer number)], encodedRest]) :
    let result : OCaml.Result := .ok (.literal (.integer (OCaml.wrapInteger (-number))))
    let next := ProviderAppend.appendRows table [primitiveRow .negate [.literal (.integer number)] result]
    (epochPlan prepared next).complete = true ∧ ProviderMeaning (patterns program) next ∧
      PureReturns runtime [] state (OCamlPrimitiveTransition.call prepared table runner epochs) state
        (encoded (OCamlPrimitiveTransition.nextMachine prepared table .negate [.literal (.integer number)] result runner epochs)) := by
  apply OCamlPrimitiveTransition.service_returns state program prepared table .negate [.literal (.integer number)] _ rest encodedRest
    runner epochs built complete signatures closed meaning resolved reached done atRequest
  · rfl
  · have computed := OCamlUnaryPrimitives.negate_returns state number
    rw [OCamlIntegerResult.result_exact] at computed
    exact computed

theorem not_service_returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (flag : Bool) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (signatures : table.signatures = provider.signatures)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (meaning : ProviderMeaning (patterns program) table)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (atRequest : runner.state = node "MlPrimitiveRequest" [primitive .notBool, valueList [.literal (.boolean flag)], encodedRest]) :
    let result : OCaml.Result := .ok (.literal (.boolean (!flag)))
    let next := ProviderAppend.appendRows table [primitiveRow .notBool [.literal (.boolean flag)] result]
    (epochPlan prepared next).complete = true ∧ ProviderMeaning (patterns program) next ∧
      PureReturns runtime [] state (OCamlPrimitiveTransition.call prepared table runner epochs) state
        (encoded (OCamlPrimitiveTransition.nextMachine prepared table .notBool [.literal (.boolean flag)] result runner epochs)) := by
  apply OCamlPrimitiveTransition.service_returns state program prepared table .notBool [.literal (.boolean flag)] _ rest encodedRest
    runner epochs built complete signatures closed meaning resolved reached done atRequest
  · rfl
  · have computed := OCamlUnaryPrimitives.not_returns state flag
    rw [OCamlResultServices.boolean_result_exact] at computed
    exact computed

#print axioms negate_service_returns
#print axioms not_service_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompleteUnaryService
