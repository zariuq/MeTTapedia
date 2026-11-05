import Mathlib.Data.List.Defs
import Mathlib.Tactic

/-!
# A sealed snapshot-transform-swap-commit epoch

The published state is the selected bank, committed epoch and input prefix.
Preparation may overwrite only the inactive bank. Aborting therefore leaves
the published state unchanged. Commit selects the prepared bank, advances the
epoch without wrapping and appends exactly the input that determined it.

This is the sequential single-core boundary used by the first Cesta kernel
integration. Cross-core quiescence, device completion and whole-system replay
remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.EpochTransition

structure Pending (State Event : Type) where
  base : Nat
  snapshot : State
  event : Event
  target : Bool
  transformed : Option State := none
  swapped : Bool := false

structure EpochState (Graph State Event : Type) where
  graph : Graph
  sealed : Bool
  banks : Bool → State
  head : Bool
  epoch : Nat
  inputs : List Event
  pending : Option (Pending State Event) := none

variable {Graph State Event : Type}

def current (s : EpochState Graph State Event) : State := s.banks s.head

def PublishedEq (left right : EpochState Graph State Event) : Prop :=
  left.graph = right.graph ∧ left.sealed = right.sealed ∧
  current left = current right ∧ left.epoch = right.epoch ∧
  left.inputs = right.inputs

def begin (maximum : Nat) (s : EpochState Graph State Event) (event : Event) :
    Option (EpochState Graph State Event) :=
  if _h : s.sealed = true ∧ s.pending = none ∧ s.epoch < maximum then
    let target := !s.head
    some { s with
      banks := Function.update s.banks target (current s)
      pending := some {
        base := s.epoch
        snapshot := current s
        event := event
        target := target
        transformed := none
        swapped := false } }
  else none

def transform (f : State → Event → State) (s : EpochState Graph State Event) :
    Option (EpochState Graph State Event) :=
  match s.pending with
  | none => none
  | some pending =>
      if _h : pending.base = s.epoch ∧ pending.target = !s.head ∧ pending.swapped = false then
        let value := f pending.snapshot pending.event
        some { s with
          banks := Function.update s.banks pending.target value
          pending := some { pending with transformed := some value } }
      else none

def swap (s : EpochState Graph State Event) : Option (EpochState Graph State Event) :=
  match s.pending with
  | none => none
  | some pending =>
      if _h : pending.base = s.epoch ∧ pending.target = !s.head ∧
          pending.transformed.isSome ∧ pending.swapped = false then
        some { s with pending := some { pending with swapped := true } }
      else none

def commit (maximum : Nat) (s : EpochState Graph State Event) :
    Option (EpochState Graph State Event) :=
  match s.pending with
  | none => none
  | some pending =>
      match pending.transformed with
      | none => none
      | some value =>
          if _h : pending.base = s.epoch ∧ pending.target = !s.head ∧
              pending.swapped = true ∧ s.epoch < maximum then
            some { s with
              banks := Function.update s.banks pending.target value
              head := pending.target
              epoch := s.epoch + 1
              inputs := s.inputs ++ [pending.event]
              pending := none }
          else none

def abort (s : EpochState Graph State Event) : EpochState Graph State Event :=
  { s with pending := none }

def runEpoch (maximum : Nat) (f : State → Event → State)
    (s : EpochState Graph State Event) (event : Event) :
    Option (EpochState Graph State Event) :=
  (begin maximum s event).bind fun first =>
    (transform f first).bind fun second =>
      (swap second).bind fun third =>
        commit maximum third

theorem begin_preserves_published {maximum : Nat} {s next : EpochState Graph State Event}
    {event : Event} (accepted : begin maximum s event = some next) :
    PublishedEq next s := by
  unfold begin at accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst next
    simp [PublishedEq, current]
  · cases accepted

theorem transform_preserves_published (f : State → Event → State)
    {s next : EpochState Graph State Event}
    (accepted : transform f s = some next) : PublishedEq next s := by
  unfold transform at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · simp only [Option.some.injEq] at accepted
      subst next
      simp_all [PublishedEq, current]
    · cases accepted

theorem swap_preserves_published {s next : EpochState Graph State Event}
    (accepted : swap s = some next) : PublishedEq next s := by
  unfold swap at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · simp only [Option.some.injEq] at accepted
      subst next
      simp [PublishedEq, current]
    · cases accepted

theorem abort_preserves_published (s : EpochState Graph State Event) :
    PublishedEq (abort s) s := by simp [PublishedEq, abort, current]

theorem commit_publishes_transformed {maximum : Nat}
    {s next : EpochState Graph State Event} {pending : Pending State Event}
    {value : State} (held : s.pending = some pending)
    (prepared : pending.transformed = some value)
    (accepted : commit maximum s = some next) :
    current next = value ∧ next.epoch = s.epoch + 1 ∧
      next.inputs = s.inputs ++ [pending.event] ∧
      next.graph = s.graph ∧ next.sealed = s.sealed ∧ next.pending = none := by
  unfold commit at accepted
  simp only [held] at accepted
  simp only [prepared] at accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst next
    simp [current]
  · cases accepted

theorem commit_preserves_graph {maximum : Nat}
    {s next : EpochState Graph State Event}
    (accepted : commit maximum s = some next) :
    next.graph = s.graph ∧ next.sealed = s.sealed := by
  unfold commit at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · split at accepted
      · simp only [Option.some.injEq] at accepted
        subst next
        simp
      · cases accepted

theorem unsealed_cannot_begin (maximum : Nat) (s : EpochState Graph State Event)
    (event : Event) (unsealed : s.sealed = false) :
    begin maximum s event = none := by simp [begin, unsealed]

theorem pending_cannot_begin (maximum : Nat) (s : EpochState Graph State Event)
    (event : Event) (pending : s.pending ≠ none) :
    begin maximum s event = none := by simp [begin, pending]

theorem exhausted_cannot_begin (maximum : Nat) (s : EpochState Graph State Event)
    (event : Event) (exhausted : maximum ≤ s.epoch) :
    begin maximum s event = none := by
  simp [begin, Nat.not_lt_of_ge exhausted]

namespace Controls

def start : EpochState Nat Nat Nat :=
  ⟨7, true, fun bank => if bank then 99 else 10, false, 0, [], none⟩

def update (state event : Nat) : Nat := state + event

theorem committed :
    (runEpoch 10 update start 5).map (fun s => (current s, s.epoch, s.inputs)) =
      some (15, 1, [5]) := by decide +kernel

def swapped : EpochState Nat Nat Nat :=
  { start with
    banks := fun bank => if bank then 15 else 10
    pending := some {
      base := 0
      snapshot := 10
      event := 5
      target := true
      transformed := some 15
      swapped := true } }

theorem abort_after_swap_keeps_publication :
    current (abort swapped) = 10 ∧ (abort swapped).epoch = 0 ∧
      (abort swapped).inputs = [] := by
  norm_num [abort, current, swapped, start]

theorem wrong_order_refused :
    transform update start = none ∧ swap start = none ∧ commit 10 start = none := by
  decide +kernel

theorem graph_is_immutable :
    (runEpoch 10 update start 5).map (fun s => s.graph) = some 7 := by decide +kernel

def queueStart : EpochState Nat (List Nat) Unit :=
  ⟨7, true, fun bank => if bank then [] else [1, 2, 3], false, 0, [], none⟩

def popHead (queue : List Nat) (_event : Unit) : List Nat := queue.drop 1

theorem dequeue_committed :
    (runEpoch 10 popHead queueStart ()).map
        (fun s => (current s, s.epoch, s.inputs)) =
      some ([2, 3], 1, [()]) := by decide +kernel

def dequeueSwapped : EpochState Nat (List Nat) Unit :=
  { queueStart with
    banks := fun bank => if bank then [2, 3] else [1, 2, 3]
    pending := some {
      base := 0
      snapshot := [1, 2, 3]
      event := ()
      target := true
      transformed := some [2, 3]
      swapped := true } }

theorem dequeue_abort_keeps_visible_head :
    current (abort dequeueSwapped) = [1, 2, 3] ∧
      (abort dequeueSwapped).epoch = 0 ∧
      (abort dequeueSwapped).inputs = [] := by decide +kernel

end Controls

#print axioms begin_preserves_published
#print axioms transform_preserves_published
#print axioms swap_preserves_published
#print axioms abort_preserves_published
#print axioms commit_publishes_transformed
#print axioms Controls.committed
#print axioms Controls.abort_after_swap_keeps_publication
#print axioms Controls.graph_is_immutable
#print axioms Controls.dequeue_committed
#print axioms Controls.dequeue_abort_keeps_visible_head

end Mettapedia.Machines.Kernel.EpochTransition
