import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveTransition
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionPrimitive

/-! Signed division services discharge both actual computation and source
result obligations in the shared cache, install and runner composition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompleteDivisionService

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource

theorem service_returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (modulo : Bool) (left right : Int) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (signatures : table.signatures = provider.signatures)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (meaning : ProviderMeaning (patterns program) table)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (atRequest : runner.state = node "MlPrimitiveRequest"
      [primitive (OCamlDivisionSource.source modulo), valueList [.literal (.integer left), .literal (.integer right)], encodedRest]) :
    let result := OCamlDivisionSource.sourceResult modulo left right
    let next := ProviderAppend.appendRows table [primitiveRow (OCamlDivisionSource.source modulo)
      [.literal (.integer left), .literal (.integer right)] result]
    (epochPlan prepared next).complete = true ∧ ProviderMeaning (patterns program) next ∧
      PureReturns runtime [] state (OCamlPrimitiveTransition.call prepared table runner epochs) state
        (encoded (OCamlPrimitiveTransition.nextMachine prepared table (OCamlDivisionSource.source modulo)
          [.literal (.integer left), .literal (.integer right)] result runner epochs)) := by
  apply OCamlPrimitiveTransition.service_returns state program prepared table (OCamlDivisionSource.source modulo)
    [.literal (.integer left), .literal (.integer right)] _ rest encodedRest
    runner epochs built complete signatures closed meaning resolved reached done atRequest
  · exact OCamlDivisionSource.source_evaluates modulo left right
  · have computed := OCamlDivisionPrimitive.primitive_returns state modulo left right
    rw [OCamlDivisionSource.result_exact] at computed
    exact computed

#print axioms service_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompleteDivisionService
