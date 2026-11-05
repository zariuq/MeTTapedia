import Mettapedia.Machines.Kernel.EpochTransition
import Mathlib.Tactic

/-!
# A bounded committed epoch ledger

The runtime keeps a finite prefix; exhaustion refuses the effect rather than
silently dropping replay information. Each record contains the input and its
complete before/after state. Valid connects the current state, epoch, input
prefix and records to deterministic replay.

The local commutation theorem is the first erasure rule. It permits exchanging
two adjacent inputs only when their transformations commute at that state.
Per-sender independence and whole-run erasure are later layers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.EpochLedger

structure Entry (State Input : Type) where
  epoch : Nat
  input : Input
  before : State
  after : State
  deriving DecidableEq, Repr

structure Ledger (State Input : Type) where
  initial : State
  current : State
  epoch : Nat
  inputs : List Input
  events : List (Entry State Input)
  sealed : Bool
  deriving DecidableEq, Repr

variable {State Input : Type}

def replay (step : State → Input → State) (initial : State) (inputs : List Input) : State :=
  inputs.foldl step initial

def traceFrom (step : State → Input → State) : State → Nat → List Input → List (Entry State Input)
  | _, _, [] => []
  | state, epoch, input :: rest =>
      let next := step state input
      ⟨epoch + 1, input, state, next⟩ :: traceFrom step next (epoch + 1) rest

def Valid (step : State → Input → State) (ledger : Ledger State Input) : Prop :=
  ledger.sealed = true ∧
  ledger.current = replay step ledger.initial ledger.inputs ∧
  ledger.epoch = ledger.inputs.length ∧
  ledger.events = traceFrom step ledger.initial 0 ledger.inputs

def commit (maximum capacity : Nat) (step : State → Input → State)
    (ledger : Ledger State Input) (input : Input) : Option (Ledger State Input) :=
  if _h : ledger.sealed = true ∧ ledger.epoch < maximum ∧ ledger.events.length < capacity then
    let next := step ledger.current input
    let event : Entry State Input := ⟨ledger.epoch + 1, input, ledger.current, next⟩
    some { ledger with
      current := next
      epoch := ledger.epoch + 1
      inputs := ledger.inputs ++ [input]
      events := ledger.events ++ [event] }
  else none

def abort (ledger : Ledger State Input) : Ledger State Input := ledger

theorem replay_append_single (step : State → Input → State) (state : State)
    (inputs : List Input) (input : Input) :
    replay step state (inputs ++ [input]) = step (replay step state inputs) input := by
  simp [replay, List.foldl_append]

theorem traceFrom_append_single (step : State → Input → State) (state : State)
    (epoch : Nat) (inputs : List Input) (input : Input) :
    traceFrom step state epoch (inputs ++ [input]) =
      traceFrom step state epoch inputs ++
        [⟨epoch + inputs.length + 1, input, replay step state inputs,
          step (replay step state inputs) input⟩] := by
  induction inputs generalizing state epoch with
  | nil => simp [traceFrom, replay]
  | cons head tail ih =>
      simp only [List.cons_append, traceFrom, List.length_cons, List.cons_append]
      rw [ih]
      simp [replay, Nat.add_comm, Nat.add_left_comm]

theorem commit_preserves_valid (step : State → Input → State)
    {ledger next : Ledger State Input} {input : Input} (valid : Valid step ledger)
    {maximum capacity : Nat}
    (accepted : commit maximum capacity step ledger input = some next) :
    Valid step next := by
  unfold commit at accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst next
    rcases valid with ⟨sealed, current, epoch, events⟩
    refine ⟨sealed, ?_, ?_, ?_⟩
    · rw [replay_append_single, ← current]
    · simp [epoch]
    · rw [events, traceFrom_append_single]
      simp [current, epoch]
  · cases accepted

theorem commit_advances_once {maximum capacity : Nat} (step : State → Input → State)
    {ledger next : Ledger State Input} {input : Input}
    (accepted : commit maximum capacity step ledger input = some next) :
    next.epoch = ledger.epoch + 1 ∧ next.inputs = ledger.inputs ++ [input] ∧
      next.events.length = ledger.events.length + 1 := by
  unfold commit at accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst next
    simp
  · cases accepted

theorem abort_preserves_valid (step : State → Input → State)
    {ledger : Ledger State Input} (valid : Valid step ledger) :
    Valid step (abort ledger) := valid

theorem unsealed_refused (maximum capacity : Nat) (step : State → Input → State)
    (ledger : Ledger State Input) (input : Input) (unsealed : ledger.sealed = false) :
    commit maximum capacity step ledger input = none := by
  simp [commit, unsealed]

theorem epoch_exhausted_refused (maximum capacity : Nat) (step : State → Input → State)
    (ledger : Ledger State Input) (input : Input) (exhausted : maximum ≤ ledger.epoch) :
    commit maximum capacity step ledger input = none := by
  simp [commit, Nat.not_lt_of_ge exhausted]

theorem ledger_exhausted_refused (maximum capacity : Nat) (step : State → Input → State)
    (ledger : Ledger State Input) (input : Input)
    (exhausted : capacity ≤ ledger.events.length) :
    commit maximum capacity step ledger input = none := by
  simp [commit, Nat.not_lt_of_ge exhausted]

def IndependentAt (step : State → Input → State) (state : State)
    (left right : Input) : Prop :=
  step (step state left) right = step (step state right) left

theorem replay_swap_independent (step : State → Input → State) (state : State)
    (left right : Input) (independent : IndependentAt step state left right) :
    replay step state [left, right] = replay step state [right, left] := independent

namespace Controls

def step (state input : Nat) : Nat := state + input

def start : Ledger Nat Nat := ⟨10, 10, 0, [], [], true⟩

def first : Ledger Nat Nat :=
  ⟨10, 11, 1, [1], [⟨1, 1, 10, 11⟩], true⟩

def second : Ledger Nat Nat :=
  ⟨10, 13, 2, [1, 2], [⟨1, 1, 10, 11⟩, ⟨2, 2, 11, 13⟩], true⟩

theorem first_is_commit : commit 10 4 step start 1 = some first := by rfl
theorem second_is_commit : commit 10 4 step first 2 = some second := by rfl

theorem start_valid : Valid step start := by simp [Valid, start, replay, traceFrom]
theorem first_valid : Valid step first :=
  commit_preserves_valid step start_valid first_is_commit
theorem second_valid : Valid step second :=
  commit_preserves_valid step first_valid second_is_commit

theorem replayed_prefix :
    second.current = 13 ∧ second.epoch = 2 ∧ second.inputs = [1, 2] ∧
      second.events.map Entry.epoch = [1, 2] := by decide +kernel

theorem exhausted_is_explicit : commit 10 2 step second 3 = none := by decide +kernel

theorem additive_inputs_commute :
    replay step 10 [4, 7] = replay step 10 [7, 4] := by
  exact replay_swap_independent step 10 4 7 (by simp [IndependentAt, step, Nat.add_comm])

end Controls

#print axioms commit_preserves_valid
#print axioms commit_advances_once
#print axioms abort_preserves_valid
#print axioms replay_swap_independent
#print axioms Controls.second_valid
#print axioms Controls.replayed_prefix
#print axioms Controls.additive_inputs_commute

end Mettapedia.Machines.Kernel.EpochLedger
