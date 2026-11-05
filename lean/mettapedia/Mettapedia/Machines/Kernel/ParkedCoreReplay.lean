import Mettapedia.Machines.Kernel.EpochLedger
import Mathlib.Tactic

/-!
# Replay with permanently parked application processors

The current x86 profile enrolls every processor before user execution.  The
bootstrap processor is the sole writer; every application processor publishes
one arrival and then remains permanently parked with interrupts disabled.
Park actions are therefore erased from the visible epoch history.  Commits are
admitted only after every enrolled processor is parked.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.ParkedCoreReplay

open Mettapedia.Machines.Kernel.EpochLedger

structure Machine (State Input : Type) where
  cores : Nat
  parked : Nat → Bool
  ledger : Ledger State Input

inductive Action (Input : Type) where
  | park (core : Nat)
  | commit (input : Input)
  deriving DecidableEq, Repr

variable {State Input : Type}

def Ready (machine : Machine State Input) : Bool :=
  (List.range machine.cores).all machine.parked

def apply (maximum capacity : Nat) (step : State → Input → State)
    (machine : Machine State Input) : Action Input → Option (Machine State Input)
  | .park core =>
      if core < machine.cores && !machine.parked core && machine.ledger.epoch == 0 then
        some { machine with parked := Function.update machine.parked core true }
      else none
  | .commit input =>
      if Ready machine then
        match EpochLedger.commit maximum capacity step machine.ledger input with
        | some ledger => some { machine with ledger := ledger }
        | none => none
      else none

def run (maximum capacity : Nat) (step : State → Input → State) :
    Machine State Input → List (Action Input) → Option (Machine State Input)
  | machine, [] => some machine
  | machine, action :: rest =>
      (apply maximum capacity step machine action).bind fun next =>
        run maximum capacity step next rest

def visible : List (Action Input) → List Input
  | [] => []
  | .park _ :: rest => visible rest
  | .commit input :: rest => input :: visible rest

theorem apply_preserves_valid (maximum capacity : Nat) (step : State → Input → State)
    {machine next : Machine State Input} {action : Action Input}
    (valid : Valid step machine.ledger)
    (accepted : apply maximum capacity step machine action = some next) :
    Valid step next.ledger := by
  cases action with
  | park core =>
      simp only [apply] at accepted
      split at accepted
      · simp only [Option.some.injEq] at accepted
        subst next
        exact valid
      · simp at accepted
  | commit input =>
      simp only [apply] at accepted
      split at accepted
      · cases committed : EpochLedger.commit maximum capacity step machine.ledger input with
        | none => simp [committed] at accepted
        | some ledger =>
            simp [committed] at accepted
            subst next
            exact commit_preserves_valid step valid committed
      · simp at accepted

theorem apply_preserves_initial (maximum capacity : Nat) (step : State → Input → State)
    {machine next : Machine State Input} {action : Action Input}
    (accepted : apply maximum capacity step machine action = some next) :
    next.ledger.initial = machine.ledger.initial := by
  cases action with
  | park core =>
      simp only [apply] at accepted
      split at accepted
      · simp only [Option.some.injEq] at accepted
        subst next
        rfl
      · simp at accepted
  | commit input =>
      simp only [apply] at accepted
      split at accepted
      · cases committed : EpochLedger.commit maximum capacity step machine.ledger input with
        | none => simp [committed] at accepted
        | some ledger =>
            simp [committed] at accepted
            subst next
            unfold EpochLedger.commit at committed
            split at committed
            · simp only [Option.some.injEq] at committed
              subst ledger
              rfl
            · simp at committed
      · simp at accepted

theorem apply_inputs (maximum capacity : Nat) (step : State → Input → State)
    {machine next : Machine State Input} {action : Action Input}
    (accepted : apply maximum capacity step machine action = some next) :
    next.ledger.inputs = machine.ledger.inputs ++ visible [action] := by
  cases action with
  | park core =>
      simp only [apply] at accepted
      split at accepted
      · simp only [Option.some.injEq] at accepted
        subst next
        simp [visible]
      · simp at accepted
  | commit input =>
      simp only [apply] at accepted
      split at accepted
      · cases committed : EpochLedger.commit maximum capacity step machine.ledger input with
        | none => simp [committed] at accepted
        | some ledger =>
            simp [committed] at accepted
            subst next
            exact (commit_advances_once step committed).2.1.trans (by simp [visible])
      · simp at accepted

theorem run_preserves_valid (maximum capacity : Nat) (step : State → Input → State)
    {machine final : Machine State Input} {actions : List (Action Input)}
    (valid : Valid step machine.ledger)
    (accepted : run maximum capacity step machine actions = some final) :
    Valid step final.ledger := by
  induction actions generalizing machine with
  | nil =>
      simp [run] at accepted
      subst final
      exact valid
  | cons action rest ih =>
      simp only [run] at accepted
      cases advanced : apply maximum capacity step machine action with
      | none => simp [advanced] at accepted
      | some next =>
          simp [advanced] at accepted
          exact ih (apply_preserves_valid maximum capacity step valid advanced) accepted

theorem run_preserves_initial (maximum capacity : Nat) (step : State → Input → State)
    {machine final : Machine State Input} {actions : List (Action Input)}
    (accepted : run maximum capacity step machine actions = some final) :
    final.ledger.initial = machine.ledger.initial := by
  induction actions generalizing machine with
  | nil =>
      simp [run] at accepted
      subst final
      rfl
  | cons action rest ih =>
      simp only [run] at accepted
      cases advanced : apply maximum capacity step machine action with
      | none => simp [advanced] at accepted
      | some next =>
          simp [advanced] at accepted
          exact (ih accepted).trans (apply_preserves_initial maximum capacity step advanced)

theorem run_inputs (maximum capacity : Nat) (step : State → Input → State)
    {machine final : Machine State Input} {actions : List (Action Input)}
    (accepted : run maximum capacity step machine actions = some final) :
    final.ledger.inputs = machine.ledger.inputs ++ visible actions := by
  induction actions generalizing machine with
  | nil =>
      simp [run] at accepted
      subst final
      simp [visible]
  | cons action rest ih =>
      simp only [run] at accepted
      cases advanced : apply maximum capacity step machine action with
      | none => simp [advanced] at accepted
      | some next =>
          simp [advanced] at accepted
          rw [ih accepted, apply_inputs maximum capacity step advanced]
          cases action <;> simp [visible, List.append_assoc]

theorem whole_run_replay (maximum capacity : Nat) (step : State → Input → State)
    {machine final : Machine State Input} {actions : List (Action Input)}
    (valid : Valid step machine.ledger)
    (accepted : run maximum capacity step machine actions = some final) :
    Valid step final.ledger ∧
      final.ledger.initial = machine.ledger.initial ∧
      final.ledger.inputs = machine.ledger.inputs ++ visible actions ∧
      final.ledger.current =
        replay step machine.ledger.initial (machine.ledger.inputs ++ visible actions) := by
  have finalValid := run_preserves_valid maximum capacity step valid accepted
  have initial := run_preserves_initial maximum capacity step accepted
  have inputs := run_inputs maximum capacity step accepted
  refine ⟨finalValid, initial, inputs, ?_⟩
  calc
    final.ledger.current = replay step final.ledger.initial final.ledger.inputs := finalValid.2.1
    _ = replay step machine.ledger.initial (machine.ledger.inputs ++ visible actions) := by
      rw [initial, inputs]

theorem parked_updates_commute (parked : Nat → Bool) {left right : Nat}
    (different : left ≠ right) :
    Function.update (Function.update parked left true) right true =
      Function.update (Function.update parked right true) left true := by
  funext core
  by_cases atLeft : core = left <;> by_cases atRight : core = right <;>
    simp [atLeft, atRight, different, Ne.symm different]

theorem park_is_erased (core : Nat) : visible [Action.park core] = ([] : List Input) := rfl

namespace Controls

def epochStep (state input : Nat) : Nat := state + input
def ledger : Ledger Nat Nat := ⟨10, 10, 0, [], [], true⟩
def machine : Machine Nat Nat := ⟨4, fun core => decide (core = 0), ledger⟩
def leftSchedule : List (Action Nat) :=
  [.park 1, .park 2, .park 3, .commit 4, .commit 7]
def rightSchedule : List (Action Nat) :=
  [.park 3, .park 1, .park 2, .commit 4, .commit 7]

theorem ledger_valid : Valid epochStep ledger := by
  simp [Valid, ledger, replay, traceFrom]

theorem visible_equal : visible leftSchedule = visible rightSchedule ∧
    visible leftSchedule = [4, 7] := by
  constructor <;> rfl

theorem arrival_orders_same_parked :
    Function.update (Function.update (Function.update machine.parked 1 true) 2 true) 3 true =
      Function.update (Function.update (Function.update machine.parked 3 true) 1 true) 2 true := by
  ext core
  by_cases one : core = 1 <;> by_cases two : core = 2 <;> by_cases three : core = 3 <;>
    simp [machine, one, two, three]

theorem premature_commit_refused :
    run 16 16 epochStep machine [.commit 4] = none := by
  have notReady : Ready machine = false := by decide
  simp [run, apply, notReady]

theorem duplicate_arrival_refused :
    run 16 16 epochStep machine [.park 1, .park 1] = none := by
  norm_num [run, apply, Ready, machine]

def final : Machine Nat Nat :=
  ⟨4, (fun core => decide (core < 4)),
    ⟨10, 21, 2, [4, 7], [⟨1, 4, 10, 14⟩, ⟨2, 7, 14, 21⟩], true⟩⟩

def readyMachine : Machine Nat Nat := { machine with parked := fun core => decide (core < 4) }
def commitSchedule : List (Action Nat) := [.commit 4, .commit 7]

theorem ready_machine : Ready readyMachine = true := by decide

theorem commits_run : run 16 16 epochStep readyMachine commitSchedule = some final := by
  rfl

theorem replayed_visible_history :
    final.ledger.current = replay epochStep ledger.initial (visible commitSchedule) := by
  have result := whole_run_replay 16 16 epochStep ledger_valid commits_run
  simpa [readyMachine, machine, ledger] using result.2.2.2

end Controls

#print axioms apply_preserves_valid
#print axioms run_inputs
#print axioms whole_run_replay
#print axioms parked_updates_commute
#print axioms Controls.arrival_orders_same_parked
#print axioms Controls.replayed_visible_history

end Mettapedia.Machines.Kernel.ParkedCoreReplay
