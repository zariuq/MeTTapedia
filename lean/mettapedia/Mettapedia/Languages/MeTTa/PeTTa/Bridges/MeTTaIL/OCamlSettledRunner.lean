import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassRunner
import Mettapedia.OSLF.MeTTaIL.Complete.Normalized

/-! A reached normalized runner that is done has a complete empty retained
search. Its actual entries remain licensed, as required by the existing
loaded status operation. No budget bound substitutes for completion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledRunner

open Mettapedia.OSLF.MeTTaIL Syntax

theorem done_search_facts (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (mode : Complete.Normalized.Commit) (machine : CompleteExecution.ClassMachine plan)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached (Complete.Normalized.search plan bound expected mode) machine)
    (done : machine.phase = .done) :
    (Complete.Classes.search plan bound expected).status machine.program = .complete ∧ machine.program.log = [] ∧
      ∀ entry ∈ machine.program.entries, CompleteExecution.KeyLicensed plan bound expected entry.1 := by
  have stopped := reached.stopped (by rw [done]; decide)
  have empty : machine.program.log = [] := stopped.1
  have status : (Complete.Classes.search plan bound expected).status machine.program = .complete := by
    have stoppedPhase := stopped.2
    rw [done] at stoppedPhase
    cases found : (Complete.Classes.search plan bound expected).status machine.program with
    | complete => rfl
    | pending => rw [show (Complete.Normalized.search plan bound expected mode).status machine.program = .pending from found] at stoppedPhase; cases stoppedPhase
    | blocked => rw [show (Complete.Normalized.search plan bound expected mode).status machine.program = .blocked from found] at stoppedPhase; cases stoppedPhase
  obtain ⟨work, current⟩ := reached.budget
  have certified := Complete.Classes.rounds_reached plan bound expected machine.state work
  refine ⟨status, empty, ?_⟩
  intro entry member
  rw [current] at member
  obtain ⟨key, search⟩ := entry
  have licensed := (certified.entries ⟨key, search⟩ member).2.1
  cases key with
  | rule rep job =>
    exact (GeneralRuleJobs.jobs_spec plan bound expected rep.pattern job).mp
      (Complete.Classes.mem_lanesOf_rule plan bound expected licensed)
  | forward rep lane => exact Complete.Classes.mem_lanesOf_forward plan bound expected licensed
  | backward rep candidate lane => exact Complete.Classes.mem_lanesOf_backward plan bound expected licensed

#print axioms done_search_facts

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledRunner
