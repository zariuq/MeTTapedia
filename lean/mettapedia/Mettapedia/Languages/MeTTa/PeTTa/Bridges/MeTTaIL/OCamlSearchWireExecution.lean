import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledRunner

/-! Actual common search status and publication operations run unchanged
under the loaded OCaml service libraries. Their meanings are obtained from
the reached normalized runner, not supplied as arbitrary status answers.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSearchWireExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

macro "through_ocaml" "[" names:str,* "]" fact:term : tactic =>
  `(tactic|
    (have snap := Library.lift_call SnapshotClosureExecution.checked (by decide +kernel) (by decide) (by decide +kernel) (by decide)
       [$names,*] (by decide) rfl (by decide +kernel) $fact
     have cached := Library.lift_call ProviderCacheExecution.checked (by decide +kernel) (by decide) (by decide +kernel) (by decide)
       [$names,*] (by decide) rfl (by decide +kernel) snap
     have integer := Library.lift_call integer_checked (by decide +kernel) (by decide) (by decide +kernel) (by decide)
       [$names,*] (by decide) rfl (by decide +kernel) cached
     have word := Library.lift_call word_checked (by decide +kernel) (by decide) (by decide +kernel) (by decide)
       [$names,*] (by decide) rfl (by decide +kernel) integer
     metta_lift checked [$names,*] word))

theorem settled_status_returns (state : State) (plan : GeneralExecutionAdmission.Plan)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (expected : TypeExpr)
    (mode : Complete.Normalized.Commit) (machine : CompleteExecution.ClassMachine plan)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached (Complete.Normalized.search plan bound expected mode) machine)
    (done : machine.phase = .done) :
    PureReturns runtime [] state
      (apply "gslt:search:status" [encoded (.symbol "ClassSearch"),
        encoded (CompletePlanWire.planTerm plan free bound expected), encoded (CompleteExecution.classStateTerm plan machine.program)]) state
      (encoded (.symbol "SearchComplete")) := by
  obtain ⟨status, _, licensed⟩ := OCamlSettledRunner.done_search_facts plan bound expected mode machine reached done
  have computed := CompleteExecution.search_status_returns plan state free bound expected machine.program licensed
  rw [status] at computed
  through_ocaml ["backend", "plan", "query"] computed

theorem settled_publication_returns (state : State) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (mode : Complete.Normalized.Commit)
    (machine : CompleteExecution.ClassMachine plan)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached (Complete.Normalized.search plan bound expected mode) machine)
    (done : machine.phase = .done) :
    PureReturns runtime [] state
      (apply "gslt:search:publication" [encoded (.symbol "ClassSearch"), encoded (CompleteExecution.classStateTerm plan machine.program)]) state
      (encoded (.symbol "LNil")) := by
  obtain ⟨_, empty, _⟩ := OCamlSettledRunner.done_search_facts plan bound expected mode machine reached done
  have computed := CompleteExecution.search_publication_returns plan state machine.program
  rw [empty] at computed
  through_ocaml ["backend", "query"] computed

#print axioms settled_status_returns
#print axioms settled_publication_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSearchWireExecution
