import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonPrimitive
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveTransition

/-! Source-authorized comparisons use the common cache/install/restart
transition with actual loaded computation, retaining the prior epoch.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompleteComparisonService

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource

theorem service_returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (operator : OCaml.Primitive) (allowed : operator.isComparison = true) (left right : OCaml.Value) (result : OCaml.Result)
    (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (signatures : table.signatures = provider.signatures)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (meaning : ProviderMeaning (patterns program) table)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (atRequest : runner.state = node "MlPrimitiveRequest" [primitive operator, valueList [left, right], encodedRest])
    (evaluated : operator.eval [left, right] = .ok result) :
    let next := ProviderAppend.appendRows table [primitiveRow operator [left, right] result]
    (epochPlan prepared next).complete = true ∧ ProviderMeaning (patterns program) next ∧
      PureReturns runtime [] state (OCamlPrimitiveTransition.call prepared table runner epochs) state
        (encoded (OCamlPrimitiveTransition.nextMachine prepared table operator [left, right] result runner epochs)) := by
  apply OCamlPrimitiveTransition.service_returns state program prepared table operator [left, right] result rest encodedRest
    runner epochs built complete signatures closed meaning resolved reached done atRequest evaluated
  have computed := OCamlComparisonPrimitive.returns state operator allowed left right
  rw [evaluated] at computed
  exact computed

#print axioms service_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompleteComparisonService
