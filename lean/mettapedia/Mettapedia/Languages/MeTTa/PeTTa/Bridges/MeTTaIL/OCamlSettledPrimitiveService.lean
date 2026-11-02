import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveServiceExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSearchWireExecution

/-! Reached completed search supplies the primitive service's complete
status and empty publication. Arithmetic and installation remain explicit
subcomputations with exact observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledPrimitiveService

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlInstallExecution OCamlPrimitiveServiceExecution

theorem service_returns (state : State) (plan : GeneralExecutionAdmission.Plan)
    (standard operator arguments rest result epochs answer : Term) (machine : CompleteExecution.ClassMachine plan)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search plan [] (.base "MlConfig") .canonical) machine)
    (done : machine.phase = .done)
    (encodedState : InferenceCettaWire.encodePattern machine.state = request operator arguments rest)
    (computed : PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:ml:primitive" [encoded operator, encoded arguments]) state (encoded (.application "Some" [result])))
    (installed : PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:ml:install" [encoded (CompletePlanWire.planTerm plan [] [] (.base "MlConfig")), encoded standard,
        encoded (CompleteExecution.classMachineTerm plan machine), encoded epochs, encoded (rowTerm operator arguments result)]) state
      (encoded answer)) :
    PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:ml:service" [encoded (CompletePlanWire.planTerm plan [] [] (.base "MlConfig")), encoded standard,
        encoded (CompleteExecution.classMachineTerm plan machine), encoded epochs]) state (encoded answer) := by
  have same : CompleteExecution.classMachineTerm plan machine = doneRunner (request operator arguments rest)
      (CompleteExecution.classStateTerm plan machine.program) (encodeList InferenceCettaWire.encodePattern machine.states)
      (encodeList CompleteExecution.classReceiptTerm machine.receipts) := by
    simp only [CompleteExecution.classMachineTerm, done, CompleteExecution.classPhaseSymbol, encodedState, doneRunner]
  rw [same] at installed ⊢
  exact OCamlPrimitiveServiceExecution.service_returns state _ standard operator arguments rest result _ _ _ epochs answer
    (OCamlSearchWireExecution.settled_status_returns state plan [] [] (.base "MlConfig") .canonical machine reached done)
    (OCamlSearchWireExecution.settled_publication_returns state plan [] (.base "MlConfig") .canonical machine reached done)
    computed installed

#print axioms service_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledPrimitiveService
