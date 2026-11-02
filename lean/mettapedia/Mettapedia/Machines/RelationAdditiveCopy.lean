import Mettapedia.Machines.RelationBagTransfer

/-!
# Additive copying into private relation storage

This is copying, not row take-over. Each source occurrence contributes once
to a new destination. A unique kept entry may accept it; refusal, including
a duplicate, appends that occurrence as a raw row. Giving back a destination
representation during copying is permitted without losing its bag.

Preparation returns a destination only after the entire source sequence has
been copied. A later recoverable failure does not publish a copied prefix.
The heap publication model installs only at a fresh destination address, so
neither source container nor any pre-existing source reader is replaced.

Facts are copied as values without rewriting their resource references.
Native code must additionally preserve those references' lifetimes, enumerate
the actual source sequence and implement the private construction boundary.
No C root discovery, allocation, concurrency or iterator refinement is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationAdditiveCopy

open RelationBagTransfer

variable {Fact : Type} [DecidableEq Fact]

def empty : Store Fact := ⟨[], ⟨[], [], true⟩⟩

/-- Refusal keeps the destination's representation change, but spills the
copied occurrence. It never removes the corresponding source occurrence. -/
def copyOne (action : Action) (destination : Store Fact) (fact : Fact) : Store Fact :=
  let attempted := offer action destination.target fact
  ⟨if attempted.1 then destination.rows else destination.rows ++ [fact], attempted.2⟩

theorem copyOne_count (action : Action) (destination : Store Fact) (fact observed : Fact) :
    ((copyOne action destination fact).bag).count observed =
      destination.bag.count observed + if fact = observed then 1 else 0 := by
  have offered := offer_count action destination.target fact observed
  by_cases same : fact = observed
  · subst observed
    cases accepted : (offer action destination.target fact).1 <;>
      simp [copyOne, Store.bag, Target.count, accepted] at offered ⊢ <;> omega
  · cases accepted : (offer action destination.target fact).1 <;>
      simp [copyOne, Store.bag, Target.count, accepted, same] at offered ⊢ <;>
        omega

def copyMany (choose : Nat → Fact → Action) : Nat → Store Fact → List Fact → Store Fact
  | _, destination, [] => destination
  | index, destination, fact :: rest =>
      copyMany choose (index + 1) (copyOne (choose index fact) destination fact) rest

theorem copyMany_count (choose : Nat → Fact → Action) (index : Nat)
    (destination : Store Fact) (source : List Fact) (observed : Fact) :
    ((copyMany choose index destination source).bag).count observed =
      destination.bag.count observed + source.count observed := by
  induction source generalizing index destination with
  | nil => simp [copyMany]
  | cons fact rest ih =>
      rw [copyMany, ih, copyOne_count]
      by_cases same : fact = observed <;>
        simp [same, Nat.add_assoc, Nat.add_comm]

theorem copyMany_bag (choose : Nat → Fact → Action) (index : Nat)
    (destination : Store Fact) (source : List Fact) :
    (copyMany choose index destination source).bag = destination.bag + (source : Multiset Fact) := by
  ext observed
  simpa using copyMany_count choose index destination source observed

/-- Batching the same occurrence sequence does not replay or drop a prefix. -/
theorem copyMany_append (choose : Nat → Fact → Action) (index : Nat)
    (destination : Store Fact) (first later : List Fact) :
    copyMany choose index destination (first ++ later) =
      copyMany choose (index + first.length)
        (copyMany choose index destination first) later := by
  induction first generalizing index destination with
  | nil => simp [copyMany]
  | cons fact rest ih =>
      simpa [copyMany, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (index + 1) (copyOne (choose index fact) destination fact)

def snapshot (source : Store Fact) : List Fact :=
  source.rows ++ source.target.dense ++ source.target.spilled

omit [DecidableEq Fact] in
theorem snapshot_bag (source : Store Fact) : (snapshot source : Multiset Fact) = source.bag := by
  simp [snapshot, Store.bag]

def additiveCopy (choose : Nat → Fact → Action) (left right : Store Fact) : Store Fact :=
  copyMany choose 0 empty (snapshot left ++ snapshot right)

/-- The source stores are read, not consumed. Both source multiplicities
contribute to the destination even when their values are identical. -/
theorem additiveCopy_bag (choose : Nat → Fact → Action) (left right : Store Fact) :
    (additiveCopy choose left right).bag = left.bag + right.bag := by
  unfold additiveCopy
  rw [copyMany_bag]
  simp [empty, Store.bag, snapshot]

/-- Any observation on fact values, including a resource-address projection,
sees the same complete bag. This does not replace native lifetime controls. -/
theorem additiveCopy_observe {Observed : Type} (observe : Fact → Observed)
    (choose : Nat → Fact → Action) (left right : Store Fact) :
    ((additiveCopy choose left right).bag).map observe =
      left.bag.map observe + right.bag.map observe := by
  rw [additiveCopy_bag, Multiset.map_add]

theorem copyOne_ordered_rows (ordered : Fact → Bool) (action : Action)
    (destination : Store Fact) (fact : Fact)
    (notKept : ordered fact = true → action.mayStore = false) :
    (copyOne action destination fact).rows.filter ordered =
      destination.rows.filter ordered ++ ([fact].filter ordered) := by
  cases accepted : (offer action destination.target fact).1
  · simp [copyOne, accepted, List.filter_append]
  · have cannotBeOrdered : ordered fact = false := by
      have admits := offer_accepts_only_store action destination.target fact accepted
      cases present : ordered fact
      · rfl
      · have refuses := notKept present
        rw [refuses] at admits
        contradiction
    simp [copyOne, accepted, cannotBeOrdered]

/-- Program/declaration rows remain in their authored relative order when
they are excluded from unique kept admission. Unordered data may compact. -/
theorem copyMany_ordered_rows (ordered : Fact → Bool)
    (choose : Nat → Fact → Action) (index : Nat) (destination : Store Fact)
    (source : List Fact)
    (notKept : ∀ index fact, ordered fact = true → (choose index fact).mayStore = false) :
    (copyMany choose index destination source).rows.filter ordered =
      destination.rows.filter ordered ++ source.filter ordered := by
  induction source generalizing index destination with
  | nil => simp [copyMany]
  | cons fact rest ih =>
      rw [copyMany, ih, copyOne_ordered_rows ordered _ _ _ (notKept index fact)]
      cases value : ordered fact <;> simp [value, List.append_assoc]

theorem additiveCopy_ordered_rows (ordered : Fact → Bool)
    (choose : Nat → Fact → Action) (left right : Store Fact)
    (notKept : ∀ index fact, ordered fact = true → (choose index fact).mayStore = false) :
    (additiveCopy choose left right).rows.filter ordered =
      (snapshot left).filter ordered ++ (snapshot right).filter ordered := by
  unfold additiveCopy
  rw [copyMany_ordered_rows ordered choose 0 empty _ notKept]
  simp [empty, List.filter_append]

/-- Readiness may fail after a private prefix was copied. Failure returns
no destination; it never exposes that prefix as an empty or partial result. -/
def prepare (ready : Nat → Bool) (choose : Nat → Fact → Action) :
    Nat → Store Fact → List Fact → Option (Store Fact)
  | _, destination, [] => some destination
  | index, destination, fact :: rest =>
      if ready index then
        prepare ready choose (index + 1) (copyOne (choose index fact) destination fact) rest
      else none

theorem prepare_some (ready : Nat → Bool) (choose : Nat → Fact → Action)
    (index : Nat) (destination : Store Fact) (source : List Fact) (result : Store Fact)
    (returned : prepare ready choose index destination source = some result) :
    result = copyMany choose index destination source := by
  induction source generalizing index destination with
  | nil => simpa [prepare, copyMany] using returned.symm
  | cons fact rest ih =>
      simp only [prepare] at returned
      split at returned
      · exact ih _ _ returned
      · contradiction

theorem prepare_failure_after_prefix (ready : Nat → Bool) (choose : Nat → Fact → Action)
    (index : Nat) (destination : Store Fact) (past : List Fact) (fact : Fact) (later : List Fact)
    (failed : ready (index + past.length) = false) :
    prepare ready choose index destination (past ++ fact :: later) = none := by
  induction past generalizing index destination with
  | nil =>
      simp only [List.length_nil, Nat.add_zero] at failed
      simp [prepare, failed]
  | cons previous rest ih =>
      simp only [List.cons_append, prepare]
      split
      · apply ih
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using failed
      · rfl

section Publication

variable {Address : Type} [DecidableEq Address]

abbrev Heap (Address Fact : Type) := Address → Option (Store Fact)

/-- A failed private build leaves the heap unchanged. A successful build
is installed only at an address that did not already name a Space. -/
def publishCopy (ready : Nat → Bool) (choose : Nat → Fact → Action)
    (ownershipReady : Bool) (heap : Heap Address Fact)
    (left right destination : Address) : Heap Address Fact × Option Address :=
  match heap left, heap right with
  | some first, some second =>
      if heap destination = none ∧ ownershipReady = true then
        match prepare ready choose 0 empty (snapshot first ++ snapshot second) with
        | some result => (Function.update heap destination (some result), some destination)
        | none => (heap, none)
      else (heap, none)
  | _, _ => (heap, none)

theorem publishCopy_cases (ready : Nat → Bool) (choose : Nat → Fact → Action)
    (ownershipReady : Bool) (heap : Heap Address Fact) (left right destination : Address) :
    publishCopy ready choose ownershipReady heap left right destination = (heap, none) ∨
      ∃ first second result,
        heap left = some first ∧ heap right = some second ∧ heap destination = none ∧
        prepare ready choose 0 empty (snapshot first ++ snapshot second) = some result ∧
        publishCopy ready choose ownershipReady heap left right destination =
          (Function.update heap destination (some result), some destination) := by
  unfold publishCopy
  split
  · rename_i first second leftPresent rightPresent
    split
    · rename_i admitted
      split
      · rename_i result prepared
        exact Or.inr ⟨first, second, result, leftPresent, rightPresent,
          admitted.1, prepared, rfl⟩
      · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem publishCopy_failure_atomic (ready : Nat → Bool) (choose : Nat → Fact → Action)
    (ownershipReady : Bool) (heap : Heap Address Fact) (left right destination : Address)
    (failed : (publishCopy ready choose ownershipReady heap left right destination).2 = none) :
    (publishCopy ready choose ownershipReady heap left right destination).1 = heap := by
  rcases publishCopy_cases ready choose ownershipReady heap left right destination with unchanged |
    ⟨first, second, result, _, _, _, _, installed⟩
  · rw [unchanged]
  · simp [installed] at failed

theorem publishCopy_frame (ready : Nat → Bool) (choose : Nat → Fact → Action)
    (ownershipReady : Bool) (heap : Heap Address Fact) (left right destination other : Address)
    (distinct : other ≠ destination) :
    (publishCopy ready choose ownershipReady heap left right destination).1 other = heap other := by
  rcases publishCopy_cases ready choose ownershipReady heap left right destination with unchanged |
    ⟨first, second, result, _, _, _, _, installed⟩
  · rw [unchanged]
  · simp [installed, distinct]

/-- Fresh publication cannot overwrite either source, including when both
operands refer to the same source address. -/
theorem publishCopy_sources_unchanged (ready : Nat → Bool) (choose : Nat → Fact → Action)
    (ownershipReady : Bool) (heap : Heap Address Fact) (left right destination : Address) :
    (publishCopy ready choose ownershipReady heap left right destination).1 left = heap left ∧
      (publishCopy ready choose ownershipReady heap left right destination).1 right = heap right := by
  rcases publishCopy_cases ready choose ownershipReady heap left right destination with unchanged |
    ⟨first, second, result, leftPresent, rightPresent, fresh, _, installed⟩
  · simp [unchanged]
  · have leftDifferent : left ≠ destination := by
      intro same
      subst left
      rw [fresh] at leftPresent
      contradiction
    have rightDifferent : right ≠ destination := by
      intro same
      subst right
      rw [fresh] at rightPresent
      contradiction
    simp [installed, leftDifferent, rightDifferent]

theorem publishCopy_captured_source (ready : Nat → Bool) (choose : Nat → Fact → Action)
    (ownershipReady : Bool) (heap : Heap Address Fact) (left right destination : Address)
    (before : Store Fact) (present : heap left = some before) (revision : Nat)
    (reader : CapturedRowReaders.Cursor Fact) :
    ((publishCopy ready choose ownershipReady heap left right destination).1 left).map
      (fun source => CapturedRowReaders.remaining (source.view revision) reader) =
        some (CapturedRowReaders.remaining (before.view revision) reader) := by
  rw [(publishCopy_sources_unchanged ready choose ownershipReady heap left right destination).1,
    present]
  rfl

theorem published_copy_bag (ready : Nat → Bool) (choose : Nat → Fact → Action)
    (ownershipReady : Bool) (heap : Heap Address Fact) (left right destination : Address)
    (returned : (publishCopy ready choose ownershipReady heap left right destination).2 =
      some destination) :
    ∃ first second result,
      heap left = some first ∧ heap right = some second ∧
      (publishCopy ready choose ownershipReady heap left right destination).1 destination =
        some result ∧ result.bag = first.bag + second.bag := by
  rcases publishCopy_cases ready choose ownershipReady heap left right destination with unchanged |
    ⟨first, second, result, leftPresent, rightPresent, _, prepared, installed⟩
  · simp [unchanged] at returned
  · refine ⟨first, second, result, leftPresent, rightPresent, ?_, ?_⟩
    · simp [installed]
    · have complete := prepare_some ready choose 0 empty _ result prepared
      rw [complete]
      exact additiveCopy_bag choose first second

end Publication

namespace Controls

def initial : Store Nat := ⟨[7, 7, 9], ⟨[], [], true⟩⟩

example : (additiveCopy (fun _ _ => .store) initial empty).bag.count 7 = 2 ∧
    (additiveCopy (fun _ _ => .store) initial empty).rows = [7] := by decide

example : (additiveCopy (fun _ _ => .store) initial initial).bag.count 7 = 4 := by decide

example : (copyMany (fun n _ => if n = 0 then .storeThenGiveBack else .store)
    0 empty [7, 7, 9]).bag = initial.bag := by decide

example : prepare (fun n => decide (n < 2)) (fun _ _ => .store)
    0 empty [7, 7, 9] = none := by decide

/-- Set union would erase a copied occurrence. -/
example : (([7, 9] : List Nat) : Multiset Nat) ≠ initial.bag := by decide

def sourceHeap : Heap Nat Nat
  | 0 => some initial
  | 1 => some (⟨[11], ⟨[], [], true⟩⟩ : Store Nat)
  | _ => none

example : (publishCopy (fun _ => true) (fun _ _ => .store) true
    sourceHeap 0 0 2).2 = some 2 ∧
    ((publishCopy (fun _ => true) (fun _ _ => .store) true
      sourceHeap 0 0 2).1 2).map (fun result => result.bag.count 7) = some 4 ∧
    (publishCopy (fun _ => true) (fun _ _ => .store) true
      sourceHeap 0 0 2).1 0 = some initial := by decide

/-- Publishing over a source address is rejected. -/
example : (publishCopy (fun _ => true) (fun _ _ => .store) true
    sourceHeap 0 1 0).2 = none := by decide

/-- Failure after two real copied occurrences publishes no result and
leaves the source objects and the fresh destination unchanged. -/
example : (publishCopy (fun n => decide (n < 2)) (fun _ _ => .store) true
      sourceHeap 0 1 2).2 = none ∧
    (publishCopy (fun n => decide (n < 2)) (fun _ _ => .store) true
      sourceHeap 0 1 2).1 0 = some initial ∧
    (publishCopy (fun n => decide (n < 2)) (fun _ _ => .store) true
      sourceHeap 0 1 2).1 2 = none := by decide

structure ManagedFact where
  payload : Nat
  endpoint : Nat
  deriving DecidableEq

/-- Equal printed payloads cannot certify shared mutable identity. -/
example : ([⟨42, 7⟩, ⟨42, 7⟩] : List ManagedFact).map ManagedFact.payload =
      ([⟨42, 8⟩, ⟨42, 8⟩] : List ManagedFact).map ManagedFact.payload ∧
    ([⟨42, 7⟩, ⟨42, 7⟩] : List ManagedFact).map ManagedFact.endpoint ≠
      ([⟨42, 8⟩, ⟨42, 8⟩] : List ManagedFact).map ManagedFact.endpoint := by decide

end Controls

#print axioms copyMany_bag
#print axioms additiveCopy_bag
#print axioms copyMany_ordered_rows
#print axioms prepare_some
#print axioms prepare_failure_after_prefix
#print axioms publishCopy_failure_atomic
#print axioms publishCopy_sources_unchanged
#print axioms publishCopy_captured_source
#print axioms published_copy_bag

end Mettapedia.Machines.RelationAdditiveCopy
