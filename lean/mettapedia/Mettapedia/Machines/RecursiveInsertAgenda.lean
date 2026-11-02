import Mettapedia.Logic.LP.PropositionalChainer
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Perm.Basic
import Lean.Elab.Tactic.Omega

/-!
# A resumable agenda for recursive insert-once programs

The admitted region is finite, positive, ground Horn inference. Absence is
used only to suppress an insertion already performed, never as a negative
premise. Rule occurrences and pending continuations remain lists. In
particular, a rule's premises are checked when its task executes, not when
the task is scheduled. Depth-first and FIFO scheduling are concrete policies.

The step bound counts agenda transitions. It is not a bound on grounding,
index probes, evaluator instructions, or native execution time. Admission of
a source-language region and its observations is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RecursiveInsert

open Mettapedia.Logic

inductive Task (Fact : Type) where
  | insert (fact : Fact)
  | check (rule : LP.PropRule Fact)
  deriving DecidableEq

inductive Event (Fact : Type) where
  | fresh (fact : Fact)
  | present (fact : Fact)
  deriving DecidableEq

@[ext] structure State (Fact : Type) where
  known : Finset Fact
  pending : List (Task Fact)
  /-- Newest event first. The count observations do not reverse this log. -/
  log : List (Event Fact)
  deriving DecidableEq

/-- Scheduling preserves every pending occurrence, not just its support. -/
structure QueuePolicy (Fact : Type) where
  enqueue : List (Task Fact) → List (Task Fact) → List (Task Fact)
  perm : ∀ children rest, (enqueue children rest).Perm (children ++ rest)

def depthFirst {Fact : Type} : QueuePolicy Fact where
  enqueue children rest := children ++ rest
  perm _ _ := List.Perm.refl _

def fifo {Fact : Type} : QueuePolicy Fact where
  enqueue children rest := rest ++ children
  perm _ _ := List.perm_append_comm

variable {Fact : Type} [DecidableEq Fact]

/-- Only rules that mention the newly inserted premise need a new check. -/
def triggered (rules : List (LP.PropRule Fact)) (fact : Fact) : List (Task Fact) :=
  (rules.filter (fun rule => fact ∈ rule.premises)).map Task.check

def initial (rules : List (LP.PropRule Fact)) (seeds : List Fact) : State Fact :=
  ⟨∅, seeds.map Task.insert ++
    (rules.filter (fun rule => rule.premises = ∅)).map Task.check, []⟩

def handle (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (task : Task Fact) (rest : List (Task Fact))
    (known : Finset Fact) (log : List (Event Fact)) : State Fact :=
  match task with
  | .insert fact =>
      if fact ∈ known then ⟨known, rest, .present fact :: log⟩
      else ⟨insert fact known, policy.enqueue (triggered rules fact) rest,
        .fresh fact :: log⟩
  | .check rule =>
      if rule.premises ⊆ known then
        ⟨known, policy.enqueue [.insert rule.head] rest, log⟩
      else ⟨known, rest, log⟩

def advance (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (state : State Fact) : State Fact :=
  match state.pending with
  | [] => state
  | task :: rest => handle rules policy task rest state.known state.log

omit [DecidableEq Fact] in
@[simp] theorem enqueue_mem (policy : QueuePolicy Fact) (children rest : List (Task Fact))
    (task : Task Fact) :
    task ∈ policy.enqueue children rest ↔ task ∈ children ∨ task ∈ rest := by
  rw [(policy.perm children rest).mem_iff]
  exact List.mem_append

@[simp] theorem triggered_mem (rules : List (LP.PropRule Fact)) (fact : Fact)
    (task : Task Fact) :
    task ∈ triggered rules fact ↔
      ∃ rule ∈ rules, fact ∈ rule.premises ∧ Task.check rule = task := by
  simp only [triggered, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨rule, ⟨hr, hf⟩, ht⟩
    exact ⟨rule, hr, hf, ht⟩
  · rintro ⟨rule, hr, hf, ht⟩
    exact ⟨rule, ⟨hr, hf⟩, ht⟩

def taskWeight : Task Fact → Nat
  | .insert _ => 1
  | .check _ => 2

def queueWeight (tasks : List (Task Fact)) : Nat :=
  (tasks.map taskWeight).sum

omit [DecidableEq Fact] in
@[simp] theorem queueWeight_nil : queueWeight ([] : List (Task Fact)) = 0 := rfl

omit [DecidableEq Fact] in
@[simp] theorem queueWeight_cons (task : Task Fact) (rest : List (Task Fact)) :
    queueWeight (task :: rest) = taskWeight task + queueWeight rest := by
  simp [queueWeight]

omit [DecidableEq Fact] in
@[simp] theorem queueWeight_append (first later : List (Task Fact)) :
    queueWeight (first ++ later) = queueWeight first + queueWeight later := by
  simp [queueWeight]

omit [DecidableEq Fact] in
theorem queueWeight_enqueue (policy : QueuePolicy Fact) (children rest : List (Task Fact)) :
    queueWeight (policy.enqueue children rest) = queueWeight children + queueWeight rest := by
  calc
    _ = queueWeight (children ++ rest) :=
      ((policy.perm children rest).map taskWeight).sum_eq
    _ = _ := queueWeight_append _ _

theorem triggered_weight_le (rules : List (LP.PropRule Fact)) (fact : Fact) :
    queueWeight (triggered rules fact) ≤ 2 * rules.length := by
  induction rules with
  | nil => simp [triggered, queueWeight]
  | cons rule rules ih =>
      by_cases hf : fact ∈ rule.premises
      · simp [triggered, hf, taskWeight, queueWeight, Nat.mul_add] at *
        omega
      · simpa [triggered, hf, Nat.mul_add] using le_trans ih (by omega)

section Finite

variable [Fintype Fact]

/-- Unseen facts pay for all future checks they can create. -/
def potential (rules : List (LP.PropRule Fact)) (state : State Fact) : Nat :=
  (2 * rules.length + 1) * (Fintype.card Fact - state.known.card) + queueWeight state.pending

theorem handle_potential_lt (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (task : Task Fact) (rest : List (Task Fact)) (known : Finset Fact)
    (log : List (Event Fact)) :
    potential rules (handle rules policy task rest known log) <
      potential rules ⟨known, task :: rest, log⟩ := by
  cases task with
  | insert fact =>
      by_cases held : fact ∈ known
      · simp [handle, held, potential, taskWeight]
      · have hc := Finset.card_le_univ (s := insert fact known)
        rw [Finset.card_insert_of_notMem held] at hc
        have hd : Fintype.card Fact - known.card =
            (Fintype.card Fact - (known.card + 1)) + 1 := by omega
        have hw := triggered_weight_le rules fact
        simp only [handle, held, ↓reduceIte, potential, Finset.card_insert_of_notMem held,
          queueWeight_enqueue, queueWeight_cons, taskWeight]
        rw [hd, Nat.mul_add, Nat.mul_one]
        omega
  | check rule =>
      by_cases enabled : rule.premises ⊆ known
      · simp [handle, enabled, potential, queueWeight_enqueue, taskWeight]
      · simp [handle, enabled, potential, taskWeight]

end Finite

inductive Result (Fact : Type) where
  | done (state : State Fact)
  | paused (state : State Fact)
  deriving DecidableEq

/-- Zero fuel on a nonempty agenda is a pause, not quiescence. -/
def run (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact) :
    Nat → State Fact → Result Fact
  | 0, state => if state.pending = [] then .done state else .paused state
  | fuel + 1, state =>
      match state.pending with
      | [] => .done state
      | task :: rest => run rules policy fuel (handle rules policy task rest state.known state.log)

theorem run_empty (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (fuel : Nat) (state : State Fact) (empty : state.pending = []) :
    run rules policy fuel state = .done state := by
  cases fuel <;> simp [run, empty]

theorem run_done_empty (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (fuel : Nat) (start finish : State Fact) (h : run rules policy fuel start = .done finish) :
    finish.pending = [] := by
  induction fuel generalizing start with
  | zero =>
      cases hp : start.pending with
      | nil =>
          have he : start = finish := by simpa [run, hp] using h
          simpa [← he] using hp
      | cons task rest => simp [run, hp] at h
  | succ fuel ih =>
      cases hp : start.pending with
      | nil =>
          have he : start = finish := by simpa [run, hp] using h
          simpa [← he] using hp
      | cons task rest => exact ih _ (by simpa [run, hp] using h)

theorem run_completes [Fintype Fact] (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (fuel : Nat) (start : State Fact) (enough : potential rules start < fuel) :
    ∃ finish, run rules policy fuel start = .done finish := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
      cases hp : start.pending with
      | nil => exact ⟨start, by simp [run, hp]⟩
      | cons task rest =>
          have hd := handle_potential_lt rules policy task rest start.known start.log
          have hs : start = ⟨start.known, task :: rest, start.log⟩ := by cases start; simp_all
          rw [← hs] at hd
          rcases ih (handle rules policy task rest start.known start.log) (by omega) with ⟨finish, h⟩
          exact ⟨finish, by simpa [run, hp] using h⟩

/-- Paused execution resumes with exactly the remaining agenda and event log. -/
def resume (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (fuel : Nat) : Result Fact → Result Fact
  | .done state => .done state
  | .paused state => run rules policy fuel state

theorem run_add (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (first later : Nat) (state : State Fact) :
    run rules policy (first + later) state = resume rules policy later (run rules policy first state) := by
  induction first generalizing state with
  | zero =>
      cases hp : state.pending with
      | nil => simp [run_empty rules policy _ state hp, run, hp, resume]
      | cons task rest => simp [run, hp, resume]
  | succ first ih =>
      cases hp : state.pending with
      | nil => simp only [run_empty rules policy _ state hp, resume]
      | cons task rest =>
          simpa only [Nat.succ_add, run, hp] using
            ih (handle rules policy task rest state.known state.log)

end Mettapedia.Machines.RecursiveInsert
