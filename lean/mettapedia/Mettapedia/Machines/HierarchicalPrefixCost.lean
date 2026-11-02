import Mettapedia.Machines.HierarchicalPrefixLaws

/-!
# Transition and administrative-selector counts for the live hierarchy

The debit walks the actually selected branch in the current state. A local
transition is counted only when the underlying worker takes a real step.
Delegation follows the retained child, not an independently chosen witness.
Administrative selectors count clock loading, selection, stopped-worker
inspection and delegation; they do not charge the variable-time internals
of phase construction, input initialization or output decoding.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HierarchicalPrefixSearch

open KolmogorovComplexity

variable {σ κ α : Type}

structure Debit where
  localTransitions : Nat
  administrativeSelectors : Nat
  deriving DecidableEq, Repr

def Debit.add (first second : Debit) : Debit :=
  ⟨first.localTransitions + second.localTransitions,
    first.administrativeSelectors + second.administrativeSelectors⟩

theorem Debit.add_assoc (first second third : Debit) :
    (first.add second).add third = first.add (second.add third) := by
  cases first
  cases second
  cases third
  simp [Debit.add, Nat.add_assoc]

def tickDebit (worker : κ → PrefixPortfolio.Worker σ α) :
    (depth : Nat) → State σ κ α depth → Debit
  | 0, _state => ⟨0, 0⟩
  | depth + 1, (input, clock) =>
      match clock.pending with
      | [] => ⟨0, 1⟩
      | word :: _rest =>
          match clock.values word with
          | .running state =>
              match (worker input).step word state with
              | none => ⟨0, 1⟩
              | some _next => ⟨1, 1⟩
          | .rejected => ⟨0, 1⟩
          | .child _answer state =>
              let child := tickDebit worker depth state
              ⟨child.localTransitions, child.administrativeSelectors + 1⟩

theorem tickDebit_bounds (worker : κ → PrefixPortfolio.Worker σ α)
    (depth : Nat) (state : State σ κ α depth) :
    (tickDebit worker depth state).localTransitions ≤ 1 ∧
      (tickDebit worker depth state).administrativeSelectors ≤ depth := by
  induction depth with
  | zero => simp [tickDebit]
  | succ depth ih =>
      obtain ⟨input, clock⟩ := state
      cases pending : clock.pending with
      | nil => simp [tickDebit, pending]
      | cons word rest =>
          cases process : clock.values word with
          | running config =>
              cases transition : (worker input).step word config <;> simp [tickDebit, pending, process, transition]
          | rejected => simp [tickDebit, pending, process]
          | child answer child =>
              simpa [tickDebit, pending, process] using ih child

def runDebit (worker : κ → PrefixPortfolio.Worker σ α) (accepts : BinString → Bool)
    (nextInput : κ → α → κ) (depth : Nat) : Nat → State σ κ α depth → Debit
  | 0, _state => ⟨0, 0⟩
  | count + 1, state =>
      (tickDebit worker depth state).add
        (runDebit worker accepts nextInput depth count (tick worker accepts nextInput depth state))

theorem runDebit_bounds (worker : κ → PrefixPortfolio.Worker σ α) (accepts : BinString → Bool)
    (nextInput : κ → α → κ) (depth count : Nat) (state : State σ κ α depth) :
    (runDebit worker accepts nextInput depth count state).localTransitions ≤ count ∧
      (runDebit worker accepts nextInput depth count state).administrativeSelectors ≤ depth * count := by
  induction count generalizing state with
  | zero => simp [runDebit]
  | succ count ih =>
      have now := tickDebit_bounds worker depth state
      have later := ih (tick worker accepts nextInput depth state)
      simp only [runDebit, Debit.add]
      constructor <;> nlinarith

theorem runDebit_add (worker : κ → PrefixPortfolio.Worker σ α) (accepts : BinString → Bool)
    (nextInput : κ → α → κ) (depth first second : Nat) (state : State σ κ α depth) :
    runDebit worker accepts nextInput depth (first + second) state =
      (runDebit worker accepts nextInput depth first state).add
        (runDebit worker accepts nextInput depth second
          (Clock.run (tick worker accepts nextInput depth) first state)) := by
  induction first generalizing state with
  | zero => simp [runDebit, Debit.add]
  | succ first ih =>
      simp only [Nat.succ_add, runDebit, Clock.run_succ, ih, Debit.add_assoc]

end Mettapedia.Machines.HierarchicalPrefixSearch
