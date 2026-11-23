import Mettapedia.Machines.DepthFirstStack
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Pending choices, not call depth

In ordered depth-first enumeration a suspended frame represents residual
work. An empty sibling segment can be forgotten; the answer trace and the
nonempty segments of all later states are unchanged. A pending cleanup which
is observable must instead occur in the residual work. Shared storage for
that work is treated separately by `DeadActivationReuse`.

Stack slots are representation-dependent. The information in independent
pending choices is not: a family of trees with the same first answer leaves
exponentially many distinguishable continuations. This yields a bit bound
without assuming one frame per branch. The bound does not apply if resuming
is given the earlier input again outside the saved state.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.DepthFirstFrontier

open Mettapedia.Machines (ExpansionTree)

variable {Answer : Type}

structure State (Answer : Type) where
  focus : Option (ExpansionTree Answer)
  pending : List (List (ExpansionTree Answer))

def keepNonempty (pending : List (List (ExpansionTree Answer))) :
    List (List (ExpansionTree Answer)) := pending.filter fun siblings => !siblings.isEmpty

def State.compact (state : State Answer) : State Answer :=
  { state with pending := keepNonempty state.pending }

def push (keepEmpty : Bool) (siblings : List (ExpansionTree Answer))
    (pending : List (List (ExpansionTree Answer))) : List (List (ExpansionTree Answer)) :=
  if keepEmpty || !siblings.isEmpty then siblings :: pending else pending

def next (keepEmpty : Bool) : List (List (ExpansionTree Answer)) → State Answer
  | [] => ⟨none, []⟩
  | [] :: rest => next keepEmpty rest
  | (child :: siblings) :: rest => ⟨some child, push keepEmpty siblings rest⟩

def tick (keepEmpty : Bool) : State Answer → Option Answer × State Answer
  | ⟨none, pending⟩ => (none, next keepEmpty pending)
  | ⟨some (.result answer), pending⟩ => (some answer, ⟨none, pending⟩)
  | ⟨some (.branch []), pending⟩ => (none, ⟨none, pending⟩)
  | ⟨some (.branch (child :: siblings)), pending⟩ =>
      (none, ⟨some child, push keepEmpty siblings pending⟩)

def run (keepEmpty : Bool) : Nat → State Answer → List Answer × State Answer
  | 0, state => ([], state)
  | fuel + 1, state =>
      let now := tick keepEmpty state
      let later := run keepEmpty fuel now.2
      (now.1.toList ++ later.1, later.2)

private theorem compact_push (keepEmpty : Bool) (siblings : List (ExpansionTree Answer))
    (pending : List (List (ExpansionTree Answer))) :
    keepNonempty (push keepEmpty siblings pending) = push false siblings (keepNonempty pending) := by
  cases siblings <;> cases keepEmpty <;> simp [keepNonempty, push]

private theorem compact_next (keepEmpty : Bool) (pending : List (List (ExpansionTree Answer))) :
    (next keepEmpty pending).compact = next false (keepNonempty pending) := by
  induction pending with
  | nil => rfl
  | cons siblings rest ih =>
      cases siblings with
      | nil => simpa [next, keepNonempty] using ih
      | cons child others =>
          exact congrArg (State.mk (some child)) (compact_push keepEmpty others rest)

/-- No call to a source evaluator is needed to drop the empty segments.
Either machine makes the same logical transition after projecting them out. -/
theorem compact_tick (keepEmpty : Bool) (state : State Answer) :
    Prod.map id State.compact (tick keepEmpty state) = tick false state.compact := by
  obtain ⟨focus, pending⟩ := state
  cases focus with
  | none => exact congrArg (Prod.mk none) (compact_next keepEmpty pending)
  | some tree =>
      cases tree with
      | result answer => rfl
      | branch children => cases children <;> simp [tick, State.compact, compact_push]

theorem compact_run (keepEmpty : Bool) (fuel : Nat) (state : State Answer) :
    Prod.map id State.compact (run keepEmpty fuel state) = run false fuel state.compact := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rw [run, run, ← compact_tick keepEmpty state]
      simp only [Prod.map_fst, Prod.map_snd, id_eq]
      rw [← ih (tick keepEmpty state).2]
      rfl

def State.answers (state : State Answer) : List Answer :=
  state.focus.toList.flatMap ExpansionTree.leaves ++ state.pending.flatten.flatMap ExpansionTree.leaves

private theorem push_flatten (keepEmpty : Bool) (siblings : List (ExpansionTree Answer))
    (pending : List (List (ExpansionTree Answer))) :
    (push keepEmpty siblings pending).flatten = siblings ++ pending.flatten := by
  cases siblings <;> cases keepEmpty <;> simp [push]

private theorem next_answers (keepEmpty : Bool) (pending : List (List (ExpansionTree Answer))) :
    (next keepEmpty pending).answers = pending.flatten.flatMap ExpansionTree.leaves := by
  induction pending with
  | nil => rfl
  | cons siblings rest ih =>
      cases siblings with
      | nil => exact ih
      | cons child others => simp [next, State.answers, push_flatten]

theorem tick_answers (keepEmpty : Bool) (state : State Answer) :
    (tick keepEmpty state).1.toList ++ (tick keepEmpty state).2.answers = state.answers := by
  obtain ⟨focus, pending⟩ := state
  cases focus with
  | none => exact next_answers keepEmpty pending
  | some tree =>
      cases tree with
      | result answer => simp [tick, State.answers, ExpansionTree.leaves]
      | branch children =>
          cases children <;> simp [tick, State.answers, ExpansionTree.leaves, push_flatten, List.append_assoc]

/-- This is equality of ordered occurrences, and therefore preserves both
duplicate answers and any cleanup events included in the tree's observation. -/
theorem run_answers (keepEmpty : Bool) (fuel : Nat) (state : State Answer) :
    (run keepEmpty fuel state).1 ++ (run keepEmpty fuel state).2.answers = state.answers := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simpa only [run, List.append_assoc, ih] using tick_answers keepEmpty state

def unarySpine (tree : ExpansionTree Answer) : Nat → ExpansionTree Answer
  | 0 => tree
  | n + 1 => .branch [unarySpine tree n]

/-- A chain of unary choices costs no new deferred frames when compacted.
Other live ancestors, and the active focus, are not part of that savings. -/
theorem unary_descent (tree : ExpansionTree Answer) (n : Nat) (keepEmpty : Bool)
    (pending : List (List (ExpansionTree Answer))) :
    run keepEmpty n ⟨some (unarySpine tree n), pending⟩ =
      ([], ⟨some tree, List.replicate (if keepEmpty then n else 0) [] ++ pending⟩) := by
  cases keepEmpty <;> induction n generalizing pending with
  | zero => rfl
  | succ n ih =>
      simp [unarySpine, run, tick, push, ih, List.replicate_succ', List.append_assoc]

/-- Charge one visit to the active focus and one to each saved frame just
after every descent. This is a recurring root *enumeration* model, not the
size of the transitive heap or a count of native stack instructions. -/
def frameVisits (keepEmpty : Bool) : Nat → State Answer → Nat
  | 0, _ => 0
  | fuel + 1, state =>
      let after := (tick keepEmpty state).2
      1 + after.pending.length + frameVisits keepEmpty fuel after

theorem unary_frame_visits (tree : ExpansionTree Answer) (n : Nat) (keepEmpty : Bool)
    (pending : List (List (ExpansionTree Answer))) :
    2 * frameVisits keepEmpty n ⟨some (unarySpine tree n), pending⟩ =
      2 * n * (1 + pending.length) + if keepEmpty then n * (n + 1) else 0 := by
  cases keepEmpty with
  | false =>
      induction n generalizing pending with
      | zero => simp [frameVisits]
      | succ n ih =>
          have rest := ih pending
          simp [unarySpine, frameVisits, tick, push] at rest ⊢
          nlinarith only [rest]
  | true =>
      induction n generalizing pending with
      | zero => simp [frameVisits]
      | succ n ih =>
          have rest := ih ([] :: pending)
          simp [unarySpine, frameVisits, tick, push] at rest ⊢
          nlinarith only [rest]

/-! ## What a representation cannot forget -/

/-- The first answer is the same anchor for all inputs. Older branches
return the bits in the reverse of the order in which they were acquired. -/
def anchored (bits : List Bool) : ExpansionTree (Option Bool) :=
  match bits with
  | [] => .result none
  | bit :: rest => .branch [anchored rest, .result (some bit)]

theorem anchored_leaves (bits : List Bool) :
    (anchored bits).leaves = none :: bits.reverse.map some := by
  induction bits with
  | nil => simp [anchored, ExpansionTree.leaves]
  | cons bit rest ih => simp [anchored, ExpansionTree.leaves, ih]

/-- Any fixed-width representation which can resume each of these searches
after the common first answer needs at least one bit per independent saved
choice. A bitset, a trail, or shared storage can replace whole frames. -/
theorem residual_information_lower_bound (choices width : Nat)
    (save : (Fin choices → Bool) → (Fin width → Bool))
    (resume : (Fin width → Bool) → List (Option Bool))
    (exactResume : ∀ input,
      resume (save input) = (anchored (List.ofFn input)).leaves.tail) : choices ≤ width := by
  have injective : Function.Injective save := by
    intro a b same
    have decoded := congrArg resume same
    simp only [exactResume, anchored_leaves, List.tail_cons] at decoded
    exact List.ofFn_injective (List.reverse_injective
      (List.map_injective_iff.mpr (Option.some_injective Bool) decoded))
  have sizes : (2 : Nat) ^ choices ≤ 2 ^ width := by
    simpa [Fintype.card_fun] using Fintype.card_le_of_injective save injective
  exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : Nat))).mp sizes

namespace Controls

theorem unary_chain_frames (n : Nat) :
    (run true n ⟨some (unarySpine (.result 5) n), []⟩).2.pending.length = n ∧
      (run false n ⟨some (unarySpine (.result 5) n), []⟩).2.pending.length = 0 := by
  simp [unary_descent]

/-- A deterministic descent need not be a tail position: completing it
may still emit a distinct event, here `false`, after returning `true`. -/
theorem dropping_teardown_changes_trace :
    (run false 6 ⟨some (.branch [.result true, .result false]), []⟩).1 ≠
      (run false 6 ⟨some (.result true), []⟩).1 := by decide

theorem duplicate_results_not_coalesced :
    (run false 6 ⟨some (.branch [.result true, .result true]), []⟩).1 = [true, true] := by
  decide

end Controls
end Mettapedia.Machines.DepthFirstFrontier
