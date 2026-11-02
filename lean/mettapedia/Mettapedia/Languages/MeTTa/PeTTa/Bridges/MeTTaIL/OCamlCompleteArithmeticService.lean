import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticPrimitive
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveRestart
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledPrimitiveService

/-! Arithmetic service composition joins independent source evaluation,
provider admission and meaning, actual loaded dispatch and a fresh runner.
The prior plan and complete runner remain in the retained epoch history.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompleteArithmeticService

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlIntegerArithmetic OCamlInstallExecution

theorem service_returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (operator : Operator) (left right : Int) (rest : OCaml.Continuation) (encodedRest : Pattern)
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
      [primitive (OCamlArithmeticSource.source operator), valueList [.literal (.integer left), .literal (.integer right)], encodedRest]) :
    let sourceOperator := OCamlArithmeticSource.source operator
    let arguments := [OCaml.Value.literal (.integer left), .literal (.integer right)]
    let result : OCaml.Result := .ok (.literal (.integer (OCaml.wrapInteger (compute operator left right))))
    let next := ProviderAppend.appendRows table [primitiveRow sourceOperator arguments result]
    let oldPlan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let nextPlan := CompletePlanWire.planTerm (epochPlan prepared next) [] [] (.base "MlConfig")
    let fresh := CompleteExecution.classMachineTerm (epochPlan prepared next)
      (OCamlRunnerBeginExecution.begun prepared next runner.state)
    (epochPlan prepared next).complete = true ∧ ProviderMeaning (patterns program) next ∧
      PureReturns runtime [] state
        (apply "gslt:ml:service" [encoded oldPlan, encoded (OCamlEpochStandard.standard prepared),
          encoded (CompleteExecution.classMachineTerm (epochPlan prepared table) runner), encoded epochs]) state
        (encoded (machine "MlRunning" nextPlan (OCamlEpochStandard.standard prepared) fresh
          (.application "LCons" [.application "MlEpoch" [oldPlan, CompleteExecution.classMachineTerm (epochPlan prepared table) runner], epochs]))) := by
  dsimp only
  have evaluated := OCamlArithmeticSource.source_evaluates operator left right
  obtain ⟨admitted, sound, _, _⟩ := primitive_epoch_invariant program prepared table _ _ _ built signatures complete closed meaning evaluated
  refine ⟨admitted, sound, ?_⟩
  have computed := OCamlArithmeticPrimitive.primitive_returns state operator left right
  rw [OCamlIntegerResult.result_exact] at computed
  have installed := OCamlPrimitiveRestart.install_returns state program prepared table
    (OCamlArithmeticSource.source operator) [.literal (.integer left), .literal (.integer right)]
    (.ok (.literal (.integer (OCaml.wrapInteger (compute operator left right))))) rest encodedRest
    (CompleteExecution.classStateTerm (epochPlan prepared table) runner.program)
    (encodeList InferenceCettaWire.encodePattern runner.states) (encodeList CompleteExecution.classReceiptTerm runner.receipts)
    epochs built signatures resolved
  have runnerWire : CompleteExecution.classMachineTerm (epochPlan prepared table) runner =
      doneRunner (InferenceCettaWire.encodePattern runner.state)
        (CompleteExecution.classStateTerm (epochPlan prepared table) runner.program)
        (encodeList InferenceCettaWire.encodePattern runner.states) (encodeList CompleteExecution.classReceiptTerm runner.receipts) := by
    simp only [CompleteExecution.classMachineTerm, done, CompleteExecution.classPhaseSymbol, doneRunner]
  dsimp only at installed
  rw [← atRequest, ← runnerWire] at installed
  apply OCamlSettledPrimitiveService.service_returns state _ (OCamlEpochStandard.standard prepared)
    (InferenceCettaWire.encodePattern (primitive (OCamlArithmeticSource.source operator)))
    (InferenceCettaWire.encodePattern (valueList [.literal (.integer left), .literal (.integer right)]))
    (InferenceCettaWire.encodePattern encodedRest)
    (InferenceCettaWire.encodePattern (primitiveResult (.ok (.literal (.integer (OCaml.wrapInteger (compute operator left right)))))))
    epochs _ runner reached done
  · simp only [atRequest, OCamlPrimitiveServiceExecution.request, node, InferenceCettaWire.encodePattern,
      InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, id_eq]
  · exact computed
  · simpa only [OCamlPrimitiveServiceExecution.rowTerm, primitiveRow,
      PremiseOperationsExecution.GeneralExecution.providerRowTerm,
      PremiseOperationsExecution.GeneralExecution.Base.patternsTerm, InferenceCettaWire.encodePatterns_eq_encodeList,
      encodeList, id_eq] using installed

#print axioms service_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompleteArithmeticService
