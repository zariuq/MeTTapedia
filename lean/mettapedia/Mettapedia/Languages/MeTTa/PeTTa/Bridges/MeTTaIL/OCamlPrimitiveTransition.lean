import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveRestart
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledPrimitiveService
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveReflection

/-! Service composition is independent of the primitive family. Actual
source evaluation and loaded execution evidence authorize the row; the
shared install and runner theorems supply the resulting epoch transition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveTransition

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution

def nextMachine (prepared : Prepared) (table : ProviderSnapshot) (operator : OCaml.Primitive)
    (arguments : List OCaml.Value) (result : OCaml.Result)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) : Term :=
  let next := ProviderAppend.appendRows table [primitiveRow operator arguments result]
  let oldPlan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
  let nextPlan := CompletePlanWire.planTerm (epochPlan prepared next) [] [] (.base "MlConfig")
  let fresh := CompleteExecution.classMachineTerm (epochPlan prepared next)
    (OCamlRunnerBeginExecution.begun prepared next runner.state)
  machine "MlRunning" nextPlan (OCamlEpochStandard.standard prepared) fresh
    (.application "LCons" [.application "MlEpoch" [oldPlan, CompleteExecution.classMachineTerm (epochPlan prepared table) runner], epochs])

def call (prepared : Prepared) (table : ProviderSnapshot)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) :=
  apply "gslt:ml:service" [encoded (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")),
    encoded (OCamlEpochStandard.standard prepared), encoded (CompleteExecution.classMachineTerm (epochPlan prepared table) runner),
    encoded epochs]

theorem service_returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
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
    (atRequest : runner.state = node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest])
    (evaluated : operator.eval arguments = .ok result)
    (computed : PureReturns runtime [] state (OCamlPrimitiveReflection.call operator arguments) state
      (encoded (OCamlArithmeticAdequacy.resultTerm result))) :
    let next := ProviderAppend.appendRows table [primitiveRow operator arguments result]
    (epochPlan prepared next).complete = true ∧ ProviderMeaning (patterns program) next ∧
      PureReturns runtime [] state (call prepared table runner epochs) state
        (encoded (nextMachine prepared table operator arguments result runner epochs)) := by
  dsimp only
  obtain ⟨admitted, sound, _, _⟩ := primitive_epoch_invariant program prepared table operator arguments result
    built signatures complete closed meaning evaluated
  refine ⟨admitted, sound, ?_⟩
  have installed := OCamlPrimitiveRestart.install_returns state program prepared table operator arguments result rest encodedRest
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
    (InferenceCettaWire.encodePattern (primitive operator)) (InferenceCettaWire.encodePattern (valueList arguments))
    (InferenceCettaWire.encodePattern encodedRest) (InferenceCettaWire.encodePattern (primitiveResult result))
    epochs _ runner reached done
  · simp only [atRequest, OCamlPrimitiveServiceExecution.request, node, InferenceCettaWire.encodePattern,
      InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, id_eq]
  · exact computed
  · simpa only [nextMachine, OCamlPrimitiveServiceExecution.rowTerm, primitiveRow,
      PremiseOperationsExecution.GeneralExecution.providerRowTerm, PremiseOperationsExecution.GeneralExecution.Base.patternsTerm,
      InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, id_eq] using installed

#print axioms service_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveTransition
