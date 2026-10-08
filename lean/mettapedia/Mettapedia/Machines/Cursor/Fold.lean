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

/-- Resuming a completed boundary does not inspect exhaustion again. A paused
boundary retries its retained loan before requesting another occurrence. -/
def resume (consume : Accumulator → Item → Option Accumulator)
    (allowance : Nat) (earlier : Stop × Packet Item Accumulator) :
    Stop × Packet Item Accumulator :=
  match earlier.1 with
  | .paused => sequence consume allowance earlier.2
  | .complete => earlier

/-- Partial acceptance grows its account monotonically and by at most the
acceptance allowance. Producer requests and terminal inspection are distinct.
A native bounded-word realization needs its separate nonwrapping premise. -/
theorem sequence_acceptance_bound
    (consume : Accumulator → Item → Option Accumulator)
    (allowance : Nat) (state : Packet Item Accumulator) :
    state.accepted ≤ (sequence consume allowance state).2.accepted ∧
    (sequence consume allowance state).2.accepted ≤ state.accepted + allowance := by
  induction allowance generalizing state with
  | zero => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ allowance ih =>
      rcases state with ⟨remaining, pending, accumulator, accepted, requested⟩
      cases pending with
      | some item =>
          cases decision : consume accumulator item with
          | none =>
              simp only [sequence, decision]
              exact ⟨Nat.le_refl accepted, Nat.le_add_right accepted (allowance + 1)⟩
          | some next =>
              have bounded := ih ⟨remaining, none, next, accepted + 1, requested⟩
              simp only [sequence, decision]
              change accepted + 1 ≤ _ ∧ _ ≤ accepted + 1 + allowance at bounded
              constructor
              · exact Nat.le_trans (Nat.le_succ accepted) bounded.1
              · rw [Nat.add_assoc, Nat.add_comm 1 allowance] at bounded
                exact bounded.2
      | none =>
          cases remaining with
          | nil =>
              change accepted ≤ accepted ∧ accepted ≤ accepted + (allowance + 1)
              exact ⟨Nat.le_refl accepted, Nat.le_add_right accepted (allowance + 1)⟩
          | cons item remaining =>
              cases decision : consume accumulator item with
              | none =>
                  simp only [sequence, decision]
                  exact ⟨Nat.le_refl accepted, Nat.le_add_right accepted (allowance + 1)⟩
              | some next =>
                  have bounded := ih ⟨remaining, none, next, accepted + 1, requested + 1⟩
                  simp only [sequence, decision]
                  change accepted + 1 ≤ _ ∧ _ ≤ accepted + 1 + allowance at bounded
                  constructor
                  · exact Nat.le_trans (Nat.le_succ accepted) bounded.1
                  · rw [Nat.add_assoc, Nat.add_comm 1 allowance] at bounded
                    exact bounded.2

/-- A finite native observation can admit a nonwrapping acceptance account
using an allowance bound, without equating acceptance with producer work. -/
theorem sequence_acceptance_below
    (consume : Accumulator → Item → Option Accumulator)
    (allowance bound : Nat) (state : Packet Item Accumulator)
    (within : state.accepted + allowance < bound) :
    (sequence consume allowance state).2.accepted < bound :=
  Nat.lt_of_le_of_lt (sequence_acceptance_bound consume allowance state).2 within

/-- Acceptance allowances compose for the actual pending-return boundary,
including refusal. Neither a rejected loan nor terminal exhaustion is replayed.
This statement concerns the pure consumer transition; it does not reorder
native callbacks, effects or authority observations. -/
theorem sequence_add (consume : Accumulator → Item → Option Accumulator)
    (first rest : Nat) (state : Packet Item Accumulator) :
    sequence consume (first + rest) state =
      resume consume rest (sequence consume first state) := by
  induction first generalizing state with
  | zero => simp [sequence, resume]
  | succ first ih =>
      rcases state with ⟨remaining, pending, accumulator, accepted, requested⟩
      cases pending with
      | some item =>
          cases decision : consume accumulator item with
          | none =>
              cases rest <;> simp [sequence, resume, decision]
          | some next =>
              simpa only [Nat.succ_add, sequence, decision] using
                ih ⟨remaining, none, next, accepted + 1, requested⟩
      | none =>
          cases remaining with
          | nil => simp [sequence, resume, Nat.succ_add]
          | cons item remaining =>
              cases decision : consume accumulator item with
              | none =>
                  cases rest <;> simp [sequence, resume, decision]
              | some next =>
                  simpa only [Nat.succ_add, sequence, decision] using
                    ih ⟨remaining, none, next, accepted + 1, requested + 1⟩

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

/-- A retained return is accepted before the residual prefix, without an
additional producer request for that return. All previous counters survive. -/
theorem pending_complete_exact (consume : Accumulator → Item → Accumulator)
    (rest : List Item) (item : Item) (accumulator : Accumulator)
    (accepted requested : Nat) :
    sequence (fun acc value => some (consume acc value)) (rest.length + 2)
        ⟨rest, some item, accumulator, accepted, requested⟩ =
      (.complete, ⟨[], none, rest.foldl consume (consume accumulator item),
        accepted + (rest.length + 1), requested + rest.length + 1⟩) := by
  change sequence (fun acc value => some (consume acc value)) (rest.length + 1)
    ⟨rest, none, consume accumulator item, accepted + 1, requested⟩ = _
  rw [complete_exact]
  simp only [Nat.add_assoc, Nat.add_comm 1 rest.length]

/-- Splitting accepted-return allowances retains the whole accumulator and
exact counters, even when the first slice already discovers exhaustion. -/
theorem resumed_complete_exact (consume : Accumulator → Item → Accumulator)
    (items : List Item) (accumulator : Accumulator)
    (accepted requested first rest : Nat)
    (enough : first + rest = items.length + 1) :
    resume (fun acc item => some (consume acc item)) rest
      (sequence (fun acc item => some (consume acc item)) first
        ⟨items, none, accumulator, accepted, requested⟩) =
      (.complete, ⟨[], none, items.foldl consume accumulator,
        accepted + items.length, requested + items.length + 1⟩) := by
  rw [← sequence_add, enough, complete_exact]

/-- A completed boundary never asks the producer to report exhaustion twice. -/
theorem completed_resume_is_inert
    (consume : Accumulator → Item → Option Accumulator)
    (allowance : Nat) (state : Packet Item Accumulator) :
    resume consume allowance (.complete, state) = (.complete, state) := rfl

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

/-- An accepted stop has committed one return. A refusal retains that same
return as a loan. Their residuals and receipts distinguish the two outcomes. -/
theorem accepted_stop_is_not_refusal :
    sequence (fun (delivered : List Nat) (item : Nat) => some (delivered ++ [item])) 1
        ⟨[7, 7], none, [], 0, 0⟩ =
      (.paused, ⟨[7], none, [7], 1, 1⟩) ∧
    sequence (fun (_ : List Nat) (_ : Nat) => none) 1
        ⟨[7, 7], none, [], 0, 0⟩ =
      (.paused, ⟨[7], some 7, [], 0, 1⟩) := by decide

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

/-- Chunked delivery transports every occurrence with its environment,
provenance and conditions; equal payloads do not collapse distinct returns. -/
theorem resumed_whole_return_delivery {Term Environment : Type}
    (returns : List (Returned Term Environment)) (first rest : Nat)
    (enough : first + rest = returns.length + 1) :
    resume (fun delivered returned => some (delivered ++ [returned])) rest
      (sequence (fun delivered returned => some (delivered ++ [returned])) first
        ⟨returns, none, [], 0, 0⟩) =
      (.complete, ⟨[], none, returns, returns.length, returns.length + 1⟩) := by
  rw [← sequence_add, enough, whole_return_delivery]

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



#print axioms sequence_add
#print axioms pending_complete_exact
#print axioms resumed_complete_exact
#print axioms resumed_whole_return_delivery



/-! ## An owned callback call as a common cursor client

Acceptance allowance and scheduler inspections are independent. Each callback
reply includes its complete provider post-state. A refusal retains the loan but
may change private callback state. Resuming that call therefore does not inherit
the pure finite-consumer allowance composition theorem above. Source callback
realization, bounded-word accounts and normal callback return remain separate
native obligations.
-/

namespace CallbackBoundary

open Mettapedia.TypeTheory.IndexedPolynomial

variable {Item Terminal : Type}

inductive Request (Item : Type) where
  | next
  | accept (item : Item)

inductive NextReply (Item Terminal : Type) where
  | returned (item : Item)
  | paused
  | terminal (reason : Terminal)

/-- The terminal payload can distinguish exhaustion, handoff, interruption
and their completion reasons. Refusal is a separate Boolean accept reply. -/
abbrev protocol (Item Terminal : Type) :
    IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Request Item
  Position request := match request with
    | .next => NextReply Item Terminal
    | .accept _ => Bool
  next _ _ := ()

structure Result (Item Terminal : Type) where
  terminal : Option Terminal
  pending : Option Item
  accepted : Nat
  deriving DecidableEq, Repr

inductive Control (Item Terminal : Type) where
  | running (allowance : Nat) (pending : Option Item) (accepted : Nat)
  | stopped (result : Result Item Terminal)

/-- This is the existing indexed-polynomial client, not a second evaluator.
The private accumulator and callback caches belong to the provider's state. -/
abbrev client (Item Terminal : Type) :
    Client (P := protocol Item Terminal) (Return := fun _ _ => Result Item Terminal) where
  V _ _ := Control Item Terminal
  str := fun _ _ => ↾(fun control => match control with
    | .stopped result => ⟨.inl result, fun impossible => nomatch impossible⟩
    | .running 0 pending accepted =>
        ⟨.inl ⟨none,pending,accepted⟩, fun impossible => nomatch impossible⟩
    | .running (allowance+1) (some item) accepted =>
        ⟨.inr (.accept item), fun decision =>
          match decision with
          | true => .running allowance none (accepted+1)
          | false => .stopped ⟨none,some item,accepted⟩⟩
    | .running (allowance+1) none accepted =>
        ⟨.inr .next, fun reply => match reply with
          | .returned item => .running (allowance+1) (some item) accepted
          | .paused => .stopped ⟨none,none,accepted⟩
          | .terminal reason => .stopped ⟨some reason,none,accepted⟩⟩)

variable (M : Provider (protocol Item Terminal)) (charge : Charge M)

def packet (allowance : Nat) (pending : Option Item) (accepted : Nat)
    (state : M.State () ()) : Mettapedia.Machines.Cursor.Packet M (client Item Terminal) () :=
  ⟨(),.running allowance pending accepted,state⟩

/-- Independent callback sequencing follows the ownership boundary's branch
order. An already held return is tried before a producer request; successful
acceptance alone spends the allowance. Every callback's post-state is retained. -/
def fromCallbacks : Nat → Option Item → Nat → M.State () () →
    Nat × (Result Item Terminal × M.State () ())
  | 0, pending, accepted, state => (0,⟨⟨none,pending,accepted⟩,state⟩)
  | allowance+1, some item, accepted, state =>
      let decision := M.step state (.accept item)
      match decision.1 with
      | true =>
          let rest := fromCallbacks allowance none (accepted+1) decision.2
          (charge state (.accept item)+rest.1,rest.2)
      | false => (charge state (.accept item),⟨⟨none,some item,accepted⟩,decision.2⟩)
  | allowance+1, none, accepted, state =>
      let response := M.step state .next
      match response.1 with
      | .paused => (charge state .next,⟨⟨none,none,accepted⟩,response.2⟩)
      | .terminal reason => (charge state .next,⟨⟨some reason,none,accepted⟩,response.2⟩)
      | .returned item =>
          let decision := M.step response.2 (.accept item)
          match decision.1 with
          | true =>
              let rest := fromCallbacks allowance none (accepted+1) decision.2
              (charge state .next+charge response.2 (.accept item)+rest.1,rest.2)
          | false => (charge state .next+charge response.2 (.accept item),
              ⟨⟨none,some item,accepted⟩,decision.2⟩)



private theorem advance_stopped (fuel : Nat) (result : Result Item Terminal)
    (state : M.State () ()) :
    Mettapedia.Machines.Cursor.advance M (client Item Terminal) charge (fuel+1)
      ⟨(),Control.stopped result,state⟩ =
        (0,.done ⟨(),result,state⟩) := rfl

private theorem advance_allowance_zero (fuel accepted : Nat) (pending : Option Item)
    (state : M.State () ()) :
    Mettapedia.Machines.Cursor.advance M (client Item Terminal) charge (fuel+1)
      (packet M 0 pending accepted state) =
        (0,.done ⟨(),⟨none,pending,accepted⟩,state⟩) := rfl

private theorem advance_pending (fuel allowance accepted : Nat) (item : Item)
    (state : M.State () ()) :
    Mettapedia.Machines.Cursor.advance M (client Item Terminal) charge (fuel+1)
      (packet M (allowance+1) (some item) accepted state) =
      let decision := M.step state (.accept item)
      let nextControl := match decision.1 with
        | true => Control.running allowance none (accepted+1)
        | false => Control.stopped ⟨none,some item,accepted⟩
      let later := Mettapedia.Machines.Cursor.advance M (client Item Terminal) charge fuel
        ⟨(),nextControl,decision.2⟩
      (charge state (.accept item)+later.1,later.2) := by
  cases response : M.step state (.accept item) with
  | mk decision after =>
      cases decision <;> simp [Mettapedia.Machines.Cursor.advance,packet,client,response]

private theorem advance_poll (fuel allowance accepted : Nat)
    (state : M.State () ()) :
    Mettapedia.Machines.Cursor.advance M (client Item Terminal) charge (fuel+1)
      (packet M (allowance+1) none accepted state) =
      let reply := M.step state .next
      let nextControl := match reply.1 with
        | .returned item => Control.running (allowance+1) (some item) accepted
        | .paused => Control.stopped ⟨none,none,accepted⟩
        | .terminal reason => Control.stopped ⟨some reason,none,accepted⟩
      let later := Mettapedia.Machines.Cursor.advance M (client Item Terminal) charge fuel
        ⟨(),nextControl,reply.2⟩
      (charge state .next+later.1,later.2) := by
  cases response : M.step state .next with
  | mk reply after =>
      cases reply <;> simp [Mettapedia.Machines.Cursor.advance,packet,client,response]

private theorem inspection_allowance_succ (allowance extra : Nat) :
    2*(allowance+1)+extra+1 = (2*allowance+extra+1)+1+1 := by
  simp only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm 2 extra]

/-- The independently sequenced callback call instantiates the common cursor.
At most two provider requests are inspected per accepted return, plus a final
client inspection. The result preserves the whole provider post-state and
loan even when the callback refuses. The cursor's `done` finishes this
callback call: a nonterminal result can retain a loan or remain paused, so it
does not assert completion of the surrounding computation. This is a
mathematical realization; physical callback lifetime, protected control-state
access and bounded-word overflow need separate evidence. -/
theorem callback_call_instantiates_common_cursor
    (allowance extra accepted : Nat) (pending : Option Item) (state : M.State () ()) :
    Mettapedia.Machines.Cursor.advance M (client Item Terminal) charge
      (2*allowance+extra+1) (packet M allowance pending accepted state) =
      let returned := fromCallbacks M charge allowance pending accepted state
      (returned.1,.done ⟨(),returned.2.1,returned.2.2⟩) := by
  induction allowance generalizing pending accepted state extra with
  | zero =>
      simpa only [Nat.mul_zero, Nat.zero_add, fromCallbacks] using
        advance_allowance_zero M charge extra accepted pending state
  | succ allowance ih =>
      rw [inspection_allowance_succ]
      cases pending with
      | some item =>
          rw [advance_pending]
          cases decision : M.step state (.accept item) with
          | mk acceptedReply after =>
              cases acceptedReply with
              | false =>
                  have halted := advance_stopped M charge (2*allowance+extra+1)
                    ⟨none,some item,accepted⟩ after
                  simp [decision,halted,fromCallbacks]
              | true =>
                  dsimp only
                  have recursion := ih (extra+1) (accepted+1) none after
                  simpa only [packet,fromCallbacks,decision,Nat.add_assoc] using
                    congrArg (fun returned =>
                      (charge state (.accept item)+returned.1,returned.2)) recursion
      | none =>
          rw [advance_poll]
          cases response : M.step state .next with
          | mk reply after =>
              cases reply with
              | paused =>
                  have halted := advance_stopped M charge (2*allowance+extra+1)
                    ⟨none,none,accepted⟩ after
                  simp [response,halted,fromCallbacks]
              | terminal reason =>
                  have halted := advance_stopped M charge (2*allowance+extra+1)
                    ⟨some reason,none,accepted⟩ after
                  simp [response,halted,fromCallbacks]
              | returned item =>
                  dsimp only
                  change (charge state .next +
                    (Mettapedia.Machines.Cursor.advance M (client Item Terminal) charge
                      (2*allowance+extra+1+1)
                      (packet M (allowance+1) (some item) accepted after)).1,
                    (Mettapedia.Machines.Cursor.advance M (client Item Terminal) charge
                      (2*allowance+extra+1+1)
                      (packet M (allowance+1) (some item) accepted after)).2) = _
                  rw [advance_pending M charge (2*allowance+extra+1)
                    allowance accepted item after]
                  cases decision : M.step after (.accept item) with
                  | mk acceptedReply afterAccept =>
                      cases acceptedReply with
                      | false =>
                          have halted := advance_stopped M charge (2*allowance+extra)
                            ⟨none,some item,accepted⟩ afterAccept
                          simp only [Nat.add_assoc] at halted
                          simp [decision,halted,fromCallbacks,response,Nat.add_assoc]
                      | true =>
                          have recursion := ih extra (accepted+1) none afterAccept
                          simpa only [packet,fromCallbacks,response,decision,Nat.add_assoc] using
                            congrArg (fun returned =>
                              (charge state .next+charge after (.accept item)+returned.1,
                                returned.2)) recursion

#print axioms callback_call_instantiates_common_cursor



/-- A terminal call remains inert. A paused call resumes its retained loan and
full provider post-state. This does not restart the producer or erase refusal
side effects. -/
def resumeCall (allowance : Nat)
    (previous : Nat × (Result Item Terminal × M.State () ())) :
    Nat × (Result Item Terminal × M.State () ()) :=
  match previous.2.1.terminal with
  | some _ => previous
  | none =>
      let later := fromCallbacks M charge allowance previous.2.1.pending
        previous.2.1.accepted previous.2.2
      (previous.1+later.1,later.2)

/-- The earlier pure finite boundary is an actual provider instance of this
callback protocol. Only its successful consumer update changes its accumulator;
producer inspection counts exhaustion as well as each returned occurrence. -/
abbrev finite (consume : Accumulator → Item → Option Accumulator) :
    Provider (protocol Item Unit) where
  State _ _ := List Item × Accumulator × Nat
  step := fun state request => match request with
    | .next => match state.1 with
        | [] => ⟨.terminal (),⟨[],state.2.1,state.2.2+1⟩⟩
        | item :: remaining => ⟨.returned item,⟨remaining,state.2.1,state.2.2+1⟩⟩
    | .accept item => match consume state.2.1 item with
        | none => ⟨false,state⟩
        | some accumulator => ⟨true,⟨state.1,accumulator,state.2.2⟩⟩

abbrev finiteCharge (consume : Accumulator → Item → Option Accumulator) :
    Charge (finite consume) := fun _ request => match request with
  | .next => 1
  | .accept _ => 0

def finiteResult (consume : Accumulator → Item → Option Accumulator)
    (result : Result Item Unit × (finite consume).State () ()) :
    Stop × OwnedSequence.Packet Item Accumulator :=
  (match result.1.terminal with
    | some _ => .complete
    | none => .paused,
    ⟨result.2.1,result.1.pending,result.2.2.1,result.1.accepted,result.2.2.2⟩)

private theorem prepend_request_account (expense requested : Nat) :
    1+expense+requested = expense+(requested+1) := by
  rw [Nat.add_comm 1 expense,Nat.add_assoc,Nat.add_comm 1 requested]

/-- The generic callback implementation agrees with the pre-existing owned
finite boundary, including duplicate occurrences, retained accumulator, pending
loan, accepted count and complete producer-request account. -/
theorem finite_callbacks_agree_with_owned_sequence
    (consume : Accumulator → Item → Option Accumulator) (allowance : Nat)
    (state : OwnedSequence.Packet Item Accumulator) :
    let actual := fromCallbacks (finite consume) (finiteCharge consume) allowance
      state.pending state.accepted ⟨state.remaining,state.accumulator,state.requested⟩
    (actual.1+state.requested,finiteResult consume actual.2) =
      ((sequence consume allowance state).2.requested,sequence consume allowance state) := by
  induction allowance generalizing state with
  | zero => simp [fromCallbacks,finiteResult,sequence]
  | succ allowance ih =>
      rcases state with ⟨remaining,pending,accumulator,accepted,requested⟩
      cases pending with
      | some item =>
          cases decision : consume accumulator item with
          | none => simp [fromCallbacks,finite,finiteCharge,sequence,finiteResult,decision]
          | some next =>
              simpa [fromCallbacks,finite,finiteCharge,sequence,finiteResult,decision] using
                ih ⟨remaining,none,next,accepted+1,requested⟩
      | none =>
          cases remaining with
          | nil => simp [fromCallbacks,finite,finiteCharge,sequence,finiteResult,Nat.add_comm 1 requested]
          | cons item rest =>
              cases decision : consume accumulator item with
              | none => simp [fromCallbacks,finite,finiteCharge,sequence,finiteResult,decision,Nat.add_comm 1 requested]
              | some next =>
                  simpa only [fromCallbacks,finite,finiteCharge,sequence,finiteResult,decision,
                    Nat.zero_add,Nat.add_zero,prepend_request_account] using
                    ih ⟨rest,none,next,accepted+1,requested+1⟩

namespace CallbackControls

structure Cache where
  remaining : List Nat
  delivered : List Nat
  requested : Nat
  warmed : Bool
  deriving DecidableEq, Repr

/-- Refusing the first callback warms a private cache. A retry can therefore
accept the same held item. Equal items remain distinct producer occurrences. -/
abbrev warming : Provider (protocol Nat String) where
  State _ _ := Cache
  step := fun state request => match request with
    | .next => match state.remaining with
        | [] => ⟨.terminal "complete",{state with requested := state.requested+1}⟩
        | item :: rest => ⟨.returned item,
            {state with remaining := rest, requested := state.requested+1}⟩
    | .accept item =>
        if state.warmed then
          ⟨true,{state with delivered := state.delivered++[item]}⟩
        else ⟨false,{state with warmed := true}⟩

def cold : Cache := ⟨[7,7],[],0,false⟩
def refused : Nat × (Result Nat String × Cache) :=
  ⟨2,⟨⟨none,some 7,0⟩,⟨[7],[],1,true⟩⟩⟩

theorem refusal_keeps_full_poststate :
    fromCallbacks warming (fun _ _ => 1) 1 none 0 cold = refused := rfl

theorem retry_uses_pending_without_repolling :
    resumeCall warming (fun _ _ => 1) 1 refused =
      ⟨3,⟨⟨none,none,1⟩,⟨[7],[7],1,true⟩⟩⟩ := rfl

/-- An allowance split can retry a state-changing refusal, whereas one larger
call stops at that refusal. The pure finite-consumer cone does not license
moving callback effects or replacing this retained state with its input. -/
theorem stateful_refusal_breaks_naive_allowance_add :
    (resumeCall warming (fun _ _ => 1) 1
      (fromCallbacks warming (fun _ _ => 1) 1 none 0 cold)).2.1.accepted ≠
      (fromCallbacks warming (fun _ _ => 1) 2 none 0 cold).2.1.accepted := by decide

theorem duplicate_returns_keep_two_deliveries :
    fromCallbacks warming (fun _ _ => 1) 2 none 0 ⟨[7,7],[],0,true⟩ =
      ⟨4,⟨⟨none,none,2⟩,⟨[],[7,7],2,true⟩⟩⟩ := rfl

theorem terminal_call_never_repolls :
    let completed := fromCallbacks warming (fun _ _ => 1) 1 none 2 ⟨[],[7,7],2,true⟩
    resumeCall warming (fun _ _ => 1) 9 completed =
      ⟨1,⟨⟨some "complete",none,2⟩,⟨[],[7,7],3,true⟩⟩⟩ := rfl

end CallbackControls

#print axioms finite_callbacks_agree_with_owned_sequence
#print axioms CallbackControls.stateful_refusal_breaks_naive_allowance_add

end CallbackBoundary

end OwnedSequence


#print axioms prefix_exact
#print axioms complete_exact
#print axioms resumed_prefix_completes
#print axioms count_without_collection

end Mettapedia.Machines.Cursor.Fold
