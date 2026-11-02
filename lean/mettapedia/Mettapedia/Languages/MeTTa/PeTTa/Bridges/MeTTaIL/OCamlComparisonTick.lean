import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompleteComparisonService
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveTransition
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledTick

/-! A source comparison request restarts its provider epoch through the
actual controller tick, preserving both admission and provider meaning.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonTick

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource

theorem service_returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (operator : OCaml.Primitive) (allowed : operator.isComparison = true) (left right : OCaml.Value) (result : OCaml.Result)
    (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
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
      PureReturns runtime [] state (apply "gslt:ml:tick"
        [encoded (OCamlInstallExecution.machine "MlRunning" (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig"))
          (OCamlEpochStandard.standard prepared) (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum]) state
        (encoded (OCamlPrimitiveTransition.nextMachine prepared table operator [left, right] result runner epochs)) := by
  obtain ⟨admitted, meaningful, computed⟩ := OCamlCompleteComparisonService.service_returns state program prepared table
    operator allowed left right result rest encodedRest runner epochs built complete signatures closed meaning resolved reached done atRequest evaluated
  exact ⟨admitted, meaningful, OCamlSettledTick.returns state (epochPlan prepared table) (OCamlEpochStandard.standard prepared)
    epochs _ runner done quantum computed⟩

#print axioms service_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonTick
