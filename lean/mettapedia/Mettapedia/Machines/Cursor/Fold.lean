import Mettapedia.Machines.Cursor.Sequence

/-!
# A resumable fold client for a pull protocol

The client requests one occurrence, updates its retained accumulator, and asks
again. It neither allocates a collection of answers nor chooses an agenda.
The accumulator may be a count, a private store delta, an output sink, or an
ordinary list. Budget exhaustion retains both accumulator and producer state.

The finite list provider is the semantic reference. Existing provider homs
transfer its laws to independently implemented sequence representations.
The arbitrary-provider client can also run indefinitely; no finite list is
required in its state. Completion requires an actual exhaustion reply.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.Fold

open Mettapedia.TypeTheory
open CategoryTheory

variable {Item Accumulator : Type}

inductive State (Accumulator : Type) where
  | pulling (accumulator : Accumulator)
  | finished (accumulator : Accumulator)
  deriving Repr, DecidableEq

def client (consume : Accumulator → Item → Accumulator) :
    Client (P := Sequence.protocol Item) (Return := fun _ _ => Accumulator) where
  V _ _ := State Accumulator
  str := fun _ _ => ↾(fun state => match state with
    | .finished accumulator =>
        ⟨.inl accumulator, fun impossible => nomatch impossible⟩
    | .pulling accumulator =>
        ⟨.inr (), fun reply => match reply with
          | none => .finished accumulator
          | some item => .pulling (consume accumulator item)⟩)

def start (provider : Provider (Sequence.protocol Item))
    (consume : Accumulator → Item → Accumulator)
    (state : provider.State () ()) (accumulator : Accumulator) :
    Packet provider (client consume) () :=
  ⟨(), .pulling accumulator, state⟩

/-- A positive quantum consumes exactly that prefix when exhaustion has not
yet been inspected. Duplicate items are individual pulls. -/
theorem prefix_exact (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator) (quantum : Nat)
    (within : quantum ≤ items.length) :
    advance (Sequence.tails Item) (client consume) (fun _ _ => 1) quantum
        (start _ consume items accumulator) =
      (quantum, .paused
        (start _ consume (items.drop quantum) ((items.take quantum).foldl consume accumulator))) := by
  induction quantum generalizing items accumulator with
  | zero => simp [advance, start]
  | succ quantum ih =>
      cases items with
      | nil => simp at within
      | cons item rest =>
          have bound : quantum ≤ rest.length := by simpa using within
          change (1 + (advance (Sequence.tails Item) (client consume) (fun _ _ => 1)
              quantum (start _ consume rest (consume accumulator item))).1,
            (advance (Sequence.tails Item) (client consume) (fun _ _ => 1)
              quantum (start _ consume rest (consume accumulator item))).2) = _
          rw [ih rest (consume accumulator item) bound]
          simp [Nat.add_comm]

/-- One final pull discovers exhaustion; one client inspection returns.
The receipt charges pulls, including the exhaustion check, not client return. -/
theorem complete_exact (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator) :
    advance (Sequence.tails Item) (client consume) (fun _ _ => 1) (items.length + 2)
        (start _ consume items accumulator) =
      (items.length + 1, .done ⟨(), items.foldl consume accumulator, []⟩) := by
  induction items generalizing accumulator with
  | nil => rfl
  | cons item rest ih =>
      change (1 + (advance (Sequence.tails Item) (client consume) (fun _ _ => 1)
          (rest.length + 2) (start _ consume rest (consume accumulator item))).1,
        (advance (Sequence.tails Item) (client consume) (fun _ _ => 1)
          (rest.length + 2) (start _ consume rest (consume accumulator item))).2) = _
      rw [ih]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem resumed_prefix_completes (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator) (first rest : Nat)
    (enough : first + rest = items.length + 2) :
    resume (Sequence.tails Item) (client consume) (fun _ _ => 1) rest
      (advance (Sequence.tails Item) (client consume) (fun _ _ => 1) first
        (start _ consume items accumulator)) =
      (items.length + 1, .done ⟨(), items.foldl consume accumulator, []⟩) := by
  rw [← advance_add, enough, complete_exact]

/-- The same client can aggregate without storing its input occurrences. -/
theorem count_without_collection (items : List Item) (initial : Nat) :
    advance (Sequence.tails Item) (client (fun n _ => n + 1)) (fun _ _ => 1)
      (items.length + 2) (start _ (fun n _ => n + 1) items initial) =
      (items.length + 1, .done ⟨(), initial + items.length, []⟩) := by
  rw [complete_exact]
  have count : items.foldl (fun n _ => n + 1) initial = initial + items.length := by
    induction items generalizing initial with
    | nil => simp
    | cons item rest ih =>
        rw [List.foldl_cons, ih]
        simp only [List.length_cons]
        omega
  rw [count]

namespace Controls

theorem partial_delivery_is_retained :
    advance (Sequence.tails Nat) (client (· + ·)) (fun _ _ => 1) 2
      (start _ (· + ·) [3, 3, 5] 0) =
      (2, .paused (start _ (· + ·) [5] 6)) := rfl

theorem replay_duplicates_delivered_items :
    (advance (Sequence.tails Nat) (client (· + ·)) (fun _ _ => 1) 5
      (start _ (· + ·) [3, 3, 5] 6)).2 ≠
    (advance (Sequence.tails Nat) (client (· + ·)) (fun _ _ => 1) 3
      (start _ (· + ·) [5] 6)).2 := by
  intro equal
  have readout := congrArg (fun outcome => match outcome with
    | .done result => some result.2.1
    | .paused _ => none) equal
  change some 17 = some 11 at readout
  cases readout

end Controls

/-! ## An owned pending-return boundary

The producer removes an occurrence into a borrowed pending slot before the
consumer accepts it. Rejection retains that slot and the accumulator.
The allowance counts accepted returns; discovering exhaustion is a separate
producer request, distinct from semantic evaluation fuel.
-/

namespace OwnedSequence

structure Packet (Item Accumulator : Type) where
  remaining : List Item
  pending : Option Item
  accumulator : Accumulator
  accepted : Nat
  requested : Nat
  deriving DecidableEq, Repr

inductive Stop where
  | paused
  | complete
  deriving DecidableEq, Repr

def undelivered (state : Packet Item Accumulator) : List Item :=
  state.pending.toList ++ state.remaining

/-- A partial consumer commits only a successful update. Holding an item does
not change its bindings, delayed conditions or syntax/value provenance. -/
def sequence (consume : Accumulator → Item → Option Accumulator) :
    Nat → Packet Item Accumulator → Stop × Packet Item Accumulator
  | 0, state => (.paused, state)
  | allowance + 1, state =>
      match state.pending with
      | some item =>
          match consume state.accumulator item with
          | none => (.paused, state)
          | some accumulator => sequence consume allowance
              ⟨state.remaining, none, accumulator, state.accepted + 1, state.requested⟩
      | none =>
          match state.remaining with
          | [] => (.complete, {state with requested := state.requested + 1})
          | item :: rest =>
              let prepared : Packet Item Accumulator :=
                ⟨rest, some item, state.accumulator, state.accepted, state.requested + 1⟩
              match consume state.accumulator item with
              | none => (.paused, prepared)
              | some accumulator => sequence consume allowance
                  ⟨rest, none, accumulator, state.accepted + 1, state.requested + 1⟩

/-- Independent materialization followed by a fold is the finite reference.
The common boundary retains just the residual and accumulator. -/
theorem prefix_exact (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator) (accepted requested allowance : Nat)
    (within : allowance ≤ items.length) :
    sequence (fun acc item => some (consume acc item)) allowance
        ⟨items, none, accumulator, accepted, requested⟩ =
      (.paused, ⟨items.drop allowance, none, (items.take allowance).foldl consume accumulator,
        accepted + allowance, requested + allowance⟩) := by
  induction allowance generalizing items accumulator accepted requested with
  | zero => simp [sequence]
  | succ allowance ih =>
      cases items with
      | nil => simp at within
      | cons item rest =>
          have bound : allowance ≤ rest.length := by simpa using within
          change sequence (fun acc item => some (consume acc item)) allowance
            ⟨rest, none, consume accumulator item, accepted + 1, requested + 1⟩ = _
          rw [ih rest (consume accumulator item) (accepted + 1) (requested + 1) bound]
          simp [Nat.add_comm, Nat.add_left_comm]

/-- Completion has inspected the producer's terminal state. Duplicate
occurrences each contribute an update and are never collapsed by value. -/
theorem complete_exact (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator) (accepted requested : Nat) :
    sequence (fun acc item => some (consume acc item)) (items.length + 1)
        ⟨items, none, accumulator, accepted, requested⟩ =
      (.complete, ⟨[], none, items.foldl consume accumulator,
        accepted + items.length, requested + items.length + 1⟩) := by
  induction items generalizing accumulator accepted requested with
  | nil => simp [sequence]
  | cons item rest ih =>
      change sequence (fun acc item => some (consume acc item)) (rest.length + 1)
        ⟨rest, none, consume accumulator item, accepted + 1, requested + 1⟩ = _
      rw [ih (consume accumulator item) (accepted + 1) (requested + 1)]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem rejected_return_is_retained (consume : Accumulator → Item → Option Accumulator)
    (rest : List Item) (item : Item) (accumulator : Accumulator)
    (accepted requested allowance : Nat) (reject : consume accumulator item = none) :
    sequence consume (allowance + 1) ⟨rest, some item, accumulator, accepted, requested⟩ =
      (.paused, ⟨rest, some item, accumulator, accepted, requested⟩) := by
  simp [sequence, reject]

theorem pending_resume_does_not_pull_again (consume : Accumulator → Item → Accumulator)
    (rest : List Item) (item : Item) (accumulator : Accumulator) (accepted requested : Nat) :
    sequence (fun acc value => some (consume acc value)) 1
        ⟨rest, some item, accumulator, accepted, requested⟩ =
      (.paused, ⟨rest, none, consume accumulator item, accepted + 1, requested⟩) := rfl

/-- Moving a rejected occurrence into pending storage preserves its place in
the residual, including equal-valued predecessors or successors. -/
theorem rejected_fresh_return_preserves_residual
    (consume : Accumulator → Item → Option Accumulator)
    (rest : List Item) (item : Item) (accumulator : Accumulator)
    (accepted requested allowance : Nat) (reject : consume accumulator item = none) :
    undelivered (sequence consume (allowance + 1)
      ⟨item :: rest, none, accumulator, accepted, requested⟩).2 = item :: rest := by
  simp [sequence, reject, undelivered]

/-- Cancellation abandons undelivered work and keeps committed receipts. -/
def cancel (state : Packet Item Accumulator) : Packet Item Accumulator :=
  {state with remaining := [], pending := none}

theorem cancellation_after_prefix (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator) (accepted requested allowance : Nat)
    (within : allowance ≤ items.length) :
    (cancel (sequence (fun acc item => some (consume acc item)) allowance
      ⟨items, none, accumulator, accepted, requested⟩).2).accumulator =
        (items.take allowance).foldl consume accumulator ∧
    (cancel (sequence (fun acc item => some (consume acc item)) allowance
      ⟨items, none, accumulator, accepted, requested⟩).2).accepted = accepted + allowance := by
  rw [prefix_exact consume items accumulator accepted requested allowance within]
  exact ⟨rfl, rfl⟩

namespace Controls

theorem last_return_does_not_certify_exhaustion :
    sequence (fun n item : Nat => some (n + item)) 2 ⟨[3, 3], none, 0, 0, 0⟩ =
      (.paused, ⟨[], none, 6, 2, 2⟩) ∧
    sequence (fun n item : Nat => some (n + item)) 1 ⟨[], none, 6, 2, 2⟩ =
      (.complete, ⟨[], none, 6, 2, 3⟩) := by decide

theorem partial_replay_changes_result :
    (sequence (fun n item : Nat => some (n + item)) 4
      ⟨[3, 3, 5], none, 6, 2, 2⟩).2.accumulator = 17 ∧
    (sequence (fun n item : Nat => some (n + item)) 2
      ⟨[5], none, 6, 2, 2⟩).2.accumulator = 11 := by decide

end Controls


/-! Returned occurrences retain provenance and conditions as well as payload.
The common sequencer transports this record; activation belongs to the dialect
adapter and is absent from the transport operation. -/

inductive ReturnForm where
  | source
  | completed
  | conditional
  deriving DecidableEq, Repr

structure Returned (Term Environment : Type) where
  payload : Term
  environment : Environment
  form : ReturnForm
  conditions : List Term
  deriving DecidableEq, Repr

theorem whole_return_delivery {Term Environment : Type}
    (returns : List (Returned Term Environment)) :
    sequence (fun delivered returned => some (delivered ++ [returned]))
      (returns.length + 1) ⟨returns, none, [], 0, 0⟩ =
        (.complete, ⟨[], none, returns, returns.length, returns.length + 1⟩) := by
  rw [complete_exact]
  have appendFold (items accumulated : List (Returned Term Environment)) :
      items.foldl (fun delivered returned => delivered ++ [returned]) accumulated =
        accumulated ++ items := by
    induction items generalizing accumulated with
    | nil => simp
    | cons item rest ih => simpa [List.append_assoc] using ih (accumulated ++ [item])
  simp [appendFold]

namespace ReturnControls

def held : Returned Nat (List Nat) := ⟨7, [4, 4], .completed, []⟩
def source : Returned Nat (List Nat) := ⟨7, [4, 4], .source, []⟩
def conditional : Returned Nat (List Nat) := ⟨7, [4, 4], .conditional, [9]⟩

theorem equal_payloads_are_not_equal_returns :
    held.payload = source.payload ∧ held ≠ source ∧ conditional ≠ held := by decide

theorem held_and_delayed_forms_are_delivered_unchanged :
    sequence (fun delivered returned => some (delivered ++ [returned])) 5
      ⟨[held, held, source, conditional], none, [], 0, 0⟩ =
        (.complete, ⟨[], none, [held, held, source, conditional], 4, 5⟩) := by
  exact whole_return_delivery [held, held, source, conditional]

end ReturnControls


end OwnedSequence


#print axioms prefix_exact
#print axioms complete_exact
#print axioms resumed_prefix_completes
#print axioms count_without_collection

end Mettapedia.Machines.Cursor.Fold
