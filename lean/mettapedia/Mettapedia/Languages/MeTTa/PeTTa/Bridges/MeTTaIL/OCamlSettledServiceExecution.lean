import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureServiceExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSearchWireExecution

/-! A reached canonical runner supplies the actual completed status and
empty publication consumed by the service. Only installation and fresh
runner creation remain at this operational composition boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledServiceExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlInstallExecution OCamlFailureServiceExecution

theorem settled_match_service_returns (state : State) (plan : GeneralExecutionAdmission.Plan)
    (standard parameter argument body captured rest epochs answer : Term) (machine : CompleteExecution.ClassMachine plan)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search plan [] (.base "MlConfig") .canonical) machine)
    (done : machine.phase = .done)
    (encodedState : InferenceCettaWire.encodePattern machine.state = matchRequest parameter argument body captured rest)
    (installed : PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:ml:install" [encoded (CompletePlanWire.planTerm plan [] [] (.base "MlConfig")), encoded standard,
        encoded (CompleteExecution.classMachineTerm plan machine), encoded epochs, encoded (failureRowTerm parameter argument)]) state
      (encoded answer)) :
    PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:ml:service" [encoded (CompletePlanWire.planTerm plan [] [] (.base "MlConfig")), encoded standard,
        encoded (CompleteExecution.classMachineTerm plan machine), encoded epochs]) state (encoded answer) := by
  have same : CompleteExecution.classMachineTerm plan machine = doneRunner (matchRequest parameter argument body captured rest)
      (CompleteExecution.classStateTerm plan machine.program) (encodeList InferenceCettaWire.encodePattern machine.states)
      (encodeList CompleteExecution.classReceiptTerm machine.receipts) := by
    simp only [CompleteExecution.classMachineTerm, done, CompleteExecution.classPhaseSymbol, encodedState, doneRunner]
  rw [same] at installed ⊢
  exact match_service_returns state _ standard parameter argument body captured rest _ _ _ epochs answer
    (OCamlSearchWireExecution.settled_status_returns state plan [] [] (.base "MlConfig") .canonical machine reached done)
    (OCamlSearchWireExecution.settled_publication_returns state plan [] (.base "MlConfig") .canonical machine reached done)
    installed

#print axioms settled_match_service_returns

theorem settled_clause_service_returns (state : State) (plan : GeneralExecutionAdmission.Plan)
    (standard parameter argument body later captured rest epochs answer : Term) (machine : CompleteExecution.ClassMachine plan)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search plan [] (.base "MlConfig") .canonical) machine)
    (done : machine.phase = .done)
    (encodedState : InferenceCettaWire.encodePattern machine.state = clauseRequest parameter argument body later captured rest)
    (installed : PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:ml:install" [encoded (CompletePlanWire.planTerm plan [] [] (.base "MlConfig")), encoded standard,
        encoded (CompleteExecution.classMachineTerm plan machine), encoded epochs, encoded (failureRowTerm parameter argument)]) state
      (encoded answer)) :
    PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:ml:service" [encoded (CompletePlanWire.planTerm plan [] [] (.base "MlConfig")), encoded standard,
        encoded (CompleteExecution.classMachineTerm plan machine), encoded epochs]) state (encoded answer) := by
  have same : CompleteExecution.classMachineTerm plan machine = doneRunner (clauseRequest parameter argument body later captured rest)
      (CompleteExecution.classStateTerm plan machine.program) (encodeList InferenceCettaWire.encodePattern machine.states)
      (encodeList CompleteExecution.classReceiptTerm machine.receipts) := by
    simp only [CompleteExecution.classMachineTerm, done, CompleteExecution.classPhaseSymbol, encodedState, doneRunner]
  rw [same] at installed ⊢
  exact clause_service_returns state _ standard parameter argument body later captured rest _ _ _ epochs answer
    (OCamlSearchWireExecution.settled_status_returns state plan [] [] (.base "MlConfig") .canonical machine reached done)
    (OCamlSearchWireExecution.settled_publication_returns state plan [] (.base "MlConfig") .canonical machine reached done)
    installed

#print axioms settled_clause_service_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledServiceExecution
