import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution
import Mettapedia.Machines.ResumableRegion

/-!
# Suspension at MM2 rule boundaries

The existing least-key rule-scoped evaluator retains its complete workspace
between bounded runs. It needs no host-language call stack at this boundary.
The split law preserves the exact ordered workspace and successful-step count,
including executable directives installed or removed by earlier firings.

One step here is a whole rule firing. Interrupting an expensive match or sink
batch within a firing requires finer residual state and a separate refinement.
The theorem fixes the policy and workspace while paused; it does not authorize
ignoring intervening edits, permission changes or external effects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2ResumableExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ReflectiveComputable
open Mettapedia.Machines

abbrev machine (policy : UnsupportedExecPolicy) : MachineCore (List Atom) where
  State := List Atom
  load := id
  step := cRuleScopedSourceWorkQueueStep policy

/-- Connect the generic region executor to the already existing MM2 evaluator. -/
theorem runSlice_eq_existing (policy : UnsupportedExecPolicy) (fuel : Nat)
    (workspace : List Atom) :
    (machine policy).runSlice fuel workspace =
      cRuleScopedSourceWorkQueueRunN policy fuel workspace := by
  induction fuel generalizing workspace with
  | zero => rfl
  | succ fuel ih =>
      simp only [MachineCore.runSlice, machine, cRuleScopedSourceWorkQueueRunN]
      cases transition : cRuleScopedSourceWorkQueueStep policy workspace with
      | none => rfl
      | some next => simp only [ih]

theorem pause_resume_exact (policy : UnsupportedExecPolicy) (first second : Nat)
    (workspace : List Atom) :
    cRuleScopedSourceWorkQueueRunN policy (first + second) workspace =
      let earlier := cRuleScopedSourceWorkQueueRunN policy first workspace
      let later := cRuleScopedSourceWorkQueueRunN policy second earlier.1
      (later.1, earlier.2 + later.2) := by
  simpa only [runSlice_eq_existing] using
    MachineCore.runSlice_add (machine policy) first second workspace

theorem used_le_budget (policy : UnsupportedExecPolicy) (fuel : Nat)
    (workspace : List Atom) :
    (cRuleScopedSourceWorkQueueRunN policy fuel workspace).2 ≤ fuel := by
  simpa only [runSlice_eq_existing] using
    MachineCore.runSlice_used_le (machine policy) fuel workspace

theorem early_stop_quiescent (policy : UnsupportedExecPolicy) (fuel : Nat)
    (workspace : List Atom)
    (early : (cRuleScopedSourceWorkQueueRunN policy fuel workspace).2 < fuel) :
    cRuleScopedSourceWorkQueueStep policy
      (cRuleScopedSourceWorkQueueRunN policy fuel workspace).1 = none := by
  have translated : ((machine policy).runSlice fuel workspace).2 < fuel := by
    simpa only [runSlice_eq_existing] using early
  simpa only [runSlice_eq_existing] using
    MachineCore.runSlice_under_budget_final (machine policy) fuel workspace translated

namespace Controls

def fact (label : String) : Atom := .expression [.symbol label]

def rule (priority label input output : String) : Atom :=
  .expression [.symbol "exec", .expression [.symbol priority, .symbol label],
    .expression [.symbol ",", fact input],
    .expression [.symbol "O",
      .expression [.symbol "-", fact input],
      .expression [.symbol "+", fact output]]]

def first : Atom := rule "0" "first" "start" "middle"
def second : Atom := rule "1" "second" "middle" "done"
def initial : List Atom := [first, second, fact "start"]

theorem first_slice_has_live_residual :
    cRuleScopedSourceWorkQueueRunN .leaveInert 1 initial =
      ([second, fact "middle"], 1) := by decide

theorem resumed_slice_finishes :
    cRuleScopedSourceWorkQueueRunN .leaveInert 1 [second, fact "middle"] =
      ([fact "done"], 1) := by decide

theorem complete_run_is_two_firings :
    cRuleScopedSourceWorkQueueRunN .leaveInert 10 initial = ([fact "done"], 2) := by
  decide

/-- Both slices use their entire budget; only the second endpoint is quiescent. -/
theorem whole_budget_is_not_completion :
    (cRuleScopedSourceWorkQueueRunN .leaveInert 1 initial).2 = 1 ∧
      (cRuleScopedSourceWorkQueueRunN .leaveInert 1 [second, fact "middle"]).2 = 1 ∧
      cRuleScopedSourceWorkQueueStep .leaveInert [second, fact "middle"] ≠ none ∧
      cRuleScopedSourceWorkQueueStep .leaveInert [fact "done"] = none := by decide

/-- Running the original input again recreates its first firing; it does not
advance the suspended frontier. -/
theorem restart_is_not_resume :
    (cRuleScopedSourceWorkQueueRunN .leaveInert 1 initial).1 ≠
      (cRuleScopedSourceWorkQueueRunN .leaveInert 1 [second, fact "middle"]).1 := by decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MORK.MM2ResumableExecution
