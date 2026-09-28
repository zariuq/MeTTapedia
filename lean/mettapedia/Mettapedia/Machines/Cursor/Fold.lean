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

#print axioms prefix_exact
#print axioms complete_exact
#print axioms resumed_prefix_completes
#print axioms count_without_collection

end Mettapedia.Machines.Cursor.Fold
