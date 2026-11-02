import Mettapedia.Logic.BDD.SymbolicCTL
import Mettapedia.Logic.BDD.DecisionTable

/-! Executed symbolic CTL controls: least versus greatest iteration, pause
versus false, deadlock policy, and shared decision-table interpretation. -/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.SymbolicCTL.Controls

open StatePredicates StateTransducer FixedPointSolver
open Mettapedia.Machines.GuardEvaluationRegimes (scalar)

def flipProgram : Certified 1 (truth 1) :=
  ⟨[StateTransducer.Controls.flip], by intro rule _ state _ _; rfl⟩

def emptyProgram : Certified 1 (truth 1) := ⟨[], by simp⟩

def stutterProgram : Certified 1 (truth 1) :=
  ⟨totalize [], by intro rule _ state _ _; rfl⟩

private def allStates : Diagram 1 := truth 1
private def bitZero : Diagram 1 := bit 0

local macro "compute_ctl" : tactic => `(tactic|
  simp [untilRun, globallyRun, untilOp, globallyOp, advance, Result.frame, Result.finished,
    flipProgram, emptyProgram, stutterProgram, allStates, bitZero, equivalent,
    StateTransducer.pre, rawPre, rulePre, within, totalize, stutterRule, anyEnabled,
    StateTransducer.Controls.flip, compileGuard, substitute, choose, truth, falsity, bit,
    conj, disj, neg, apply, bddVar, bddNot, mk, BDD.eval])

theorem until_completes : (untilRun flipProgram allStates bitZero 3).finished = true := by compute_ctl

theorem until_reaches_both_states (state : State 1) :
    (untilRun flipProgram allStates bitZero 3).frame.current.val.eval state = true := by compute_ctl

theorem until_passes : (untilRun flipProgram allStates bitZero 3).frame.passes = 3 := by compute_ctl

theorem globally_bit_is_false (state : State 1) :
    (globallyRun flipProgram bitZero 3).finished = true ∧
    (globallyRun flipProgram bitZero 3).frame.current.val.eval state = false := by compute_ctl

theorem zero_fuel_is_not_a_negative_answer :
    (untilRun flipProgram allStates bitZero 0).finished = false ∧
    (untilRun flipProgram allStates bitZero 0).frame.current.val.eval (fun _ => false) = false ∧
    (untilRun flipProgram allStates bitZero 3).frame.current.val.eval (fun _ => false) = true := by compute_ctl

theorem deadlock_policy_changes_symbolic_answer (state : State 1) :
    (globallyRun emptyProgram allStates 2).frame.current.val.eval state = false ∧
    (globallyRun stutterProgram allStates 2).frame.current.val.eval state = true := by compute_ctl

theorem paged_until_keeps_receipt :
    resume (untilOp flipProgram allStates bitZero) 2 (untilRun flipProgram allStates bitZero 1) =
      untilRun flipProgram allStates bitZero 3 :=
  resume_split (untilOp flipProgram allStates bitZero) 1 2 _

theorem relation_change_can_invalidate_a_completed_result :
    (untilRun emptyProgram allStates bitZero 2).frame.current.val.eval (fun _ => false) = false ∧
    (untilRun flipProgram allStates bitZero 3).frame.current.val.eval (fun _ => false) = true := by compute_ctl

theorem opposite_approximation_polarities :
    observeUntil (untilRun flipProgram allStates bitZero 0) (fun _ => false) = none ∧
    observeGlobally (globallyRun flipProgram bitZero 0) (fun _ => false) = none := by
  simp [observeUntil, observeGlobally, untilRun, globallyRun, advance, Result.frame, Result.finished, falsity, truth]

end Mettapedia.Logic.BDDCore.SymbolicCTL.Controls
