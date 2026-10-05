import Mettapedia.GSLT.LanguageDef.NativeOpsCPostIndex
import Mettapedia.Machines.OrderedDependencyBatch
import Mathlib.Data.List.Nodup

/-!
# Finite-width forward and reverse dependency publication

The implementation writes UInt32-counted slot arrays, forward first and reverse
second, in pending-list order. The specification independently appends to
unbounded active lists. The relation observes both directions, not just queries.

Undefined slot accesses have no completed transition; `none` is not rollback.
The existence law uses independently stated capacities and distinct pending
identities. Field separation is represented structurally here. Relating these
fields and opaque identities to a physical C heap, the reservation procedure,
and the enclosing read window remains a separate realization obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyCArray

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.PostIndex
open OrderedDependencyStore

universe u
variable {Ptr : Type u} [DecidableEq Ptr]

@[ext] structure Links (Ptr : Type u) where
  forward : Ptr → List Ptr
  reverse : Ptr → List Ptr

@[ext] structure Heap (Ptr : Type u) where
  forward : Ptr → Array32 Ptr
  reverse : Ptr → Array32 Ptr

def Heap.Sized (heap : Heap Ptr) : Prop :=
  (∀ owner, (heap.forward owner).Sized) ∧ (∀ owner, (heap.reverse owner).Sized)

def observe (heap : Heap Ptr) : Links Ptr :=
  ⟨fun owner => (heap.forward owner).active, fun owner => (heap.reverse owner).active⟩

def appendLink (links : Links Ptr) (reader source : Ptr) : Links Ptr :=
  ⟨Function.update links.forward reader (links.forward reader ++ [source]),
    Function.update links.reverse source (links.reverse source ++ [reader])⟩

def appendBatch (links : Links Ptr) (reader : Ptr) : List Ptr → Links Ptr
  | [] => links
  | source :: rest => appendBatch (appendLink links reader source) reader rest

def writeLink (heap : Heap Ptr) (reader source : Ptr) : Option (Heap Ptr) := do
  let forward ← store (heap.forward reader) source
  let forwardOnly : Heap Ptr := { heap with forward := Function.update heap.forward reader forward }
  let reverse ← store (forwardOnly.reverse source) reader
  some { forwardOnly with reverse := Function.update forwardOnly.reverse source reverse }

def writeBatch (heap : Heap Ptr) (reader : Ptr) : List Ptr → Option (Heap Ptr)
  | [] => some heap
  | source :: rest => (writeLink heap reader source).bind fun next => writeBatch next reader rest

theorem writeLink_fields {heap after : Heap Ptr} {reader source : Ptr}
    (defined : writeLink heap reader source = some after) :
    ∃ forward reverse,
      store (heap.forward reader) source = some forward ∧
      store (heap.reverse source) reader = some reverse ∧
      after = ⟨Function.update heap.forward reader forward,
        Function.update heap.reverse source reverse⟩ := by
  cases first : store (heap.forward reader) source with
  | none => simp [writeLink, first] at defined
  | some forward =>
    cases second : store (heap.reverse source) reader with
    | none => simp [writeLink, first, second] at defined
    | some reverse =>
      exact ⟨forward, reverse, rfl, rfl,
        (Option.some.inj (by simpa [writeLink, first, second] using defined)).symm⟩

theorem writeLink_refines {heap after : Heap Ptr} {reader source : Ptr}
    (sized : heap.Sized) (defined : writeLink heap reader source = some after) :
    observe after = appendLink (observe heap) reader source ∧ after.Sized := by
  obtain ⟨forward, reverse, first, second, rfl⟩ := writeLink_fields defined
  have forwardLaw := store_realizes_append (sized.1 reader) first
  have reverseLaw := store_realizes_append (sized.2 source) second
  constructor
  · apply Links.ext <;> funext owner
    · by_cases same : owner = reader
      · subst owner
        simpa [observe, appendLink] using forwardLaw.1
      · simp [observe, appendLink, Function.update_of_ne same]
    · by_cases same : owner = source
      · subst owner
        simpa [observe, appendLink] using reverseLaw.1
      · simp [observe, appendLink, Function.update_of_ne same]
  · constructor
    · intro owner
      by_cases same : owner = reader
      · subst owner
        simpa using forwardLaw.2.2.2
      · simpa [Function.update_of_ne same] using sized.1 owner
    · intro owner
      by_cases same : owner = source
      · subst owner
        simpa using reverseLaw.2.2.2
      · simpa [Function.update_of_ne same] using sized.2 owner

theorem writeBatch_refines {heap after : Heap Ptr} (reader : Ptr) (pending : List Ptr)
    (sized : heap.Sized) (defined : writeBatch heap reader pending = some after) :
    observe after = appendBatch (observe heap) reader pending ∧ after.Sized := by
  induction pending generalizing heap with
  | nil =>
    have same : heap = after := Option.some.inj defined
    subst after
    exact ⟨rfl, sized⟩
  | cons source rest ih =>
    cases first : writeLink heap reader source with
    | none => simp [writeBatch, first] at defined
    | some middle =>
      have remaining : writeBatch middle reader rest = some after := by
        simpa [writeBatch, first] using defined
      have firstLaw := writeLink_refines sized first
      have restLaw := ih firstLaw.2 remaining
      exact ⟨by simpa [appendBatch, firstLaw.1] using restLaw.1, restLaw.2⟩

theorem appendBatch_forward (links : Links Ptr) (reader owner : Ptr) (pending : List Ptr) :
    (appendBatch links reader pending).forward owner =
      if owner = reader then links.forward owner ++ pending else links.forward owner := by
  induction pending generalizing links with
  | nil => simp [appendBatch]
  | cons source rest ih =>
    rw [appendBatch, ih]
    by_cases same : owner = reader
    · subst owner
      simp [appendLink, List.append_assoc]
    · simp [appendLink, same]

theorem appendBatch_reverse_membership (links : Links Ptr) (reader owner observer : Ptr)
    (pending : List Ptr) :
    observer ∈ (appendBatch links reader pending).reverse owner ↔
      observer ∈ links.reverse owner ∨ (observer = reader ∧ owner ∈ pending) := by
  induction pending generalizing links with
  | nil => simp [appendBatch]
  | cons source rest ih =>
    rw [appendBatch, ih]
    by_cases same : owner = source
    · subst owner
      simp [appendLink, List.mem_append, List.mem_cons]
      tauto
    · simp [appendLink, List.mem_cons, same]

/-- Capacities are tested before any target execution. Reverse room is required
only for prepared identities; distinctness ensures it is consumed once each. -/
def Ready (heap : Heap Ptr) (reader : Ptr) (pending : List Ptr) : Prop :=
  heap.Sized ∧ pending.Nodup ∧
    (heap.forward reader).count.toNat + pending.length ≤ (heap.forward reader).slots.length ∧
    (∀ source ∈ pending, (heap.reverse source).Room)

theorem writeLink_exists (heap : Heap Ptr) (reader source : Ptr)
    (forwardRoom : (heap.forward reader).Room) (reverseRoom : (heap.reverse source).Room) :
    ∃ after, writeLink heap reader source = some after := by
  refine ⟨⟨Function.update heap.forward reader
      ⟨(heap.forward reader).slots.set (heap.forward reader).count.toNat source,
        (heap.forward reader).count + 1⟩,
    Function.update heap.reverse source
      ⟨(heap.reverse source).slots.set (heap.reverse source).count.toNat reader,
        (heap.reverse source).count + 1⟩⟩, ?_⟩
  simp [writeLink, store_defined _ _ forwardRoom, store_defined _ _ reverseRoom]

theorem ready_after_first {heap after : Heap Ptr} {reader source : Ptr} {rest : List Ptr}
    (ready : Ready heap reader (source :: rest))
    (defined : writeLink heap reader source = some after) : Ready after reader rest := by
  obtain ⟨forward, reverse, first, second, same⟩ := writeLink_fields defined
  have law := writeLink_refines ready.1 defined
  have forwardLaw := store_realizes_append (ready.1.1 reader) first
  refine ⟨law.2, ready.2.1.of_cons, ?_, ?_⟩
  · rw [same]
    simpa [forwardLaw.2.1, forwardLaw.2.2.1, List.length_cons,
      Nat.add_assoc, Nat.add_comm] using ready.2.2.1
  · intro owner included
    have different : owner ≠ source := by
      intro equal
      subst owner
      exact (List.nodup_cons.mp ready.2.1).1 included
    rw [same]
    simpa [Function.update_of_ne different] using ready.2.2.2 owner (List.mem_cons_of_mem _ included)

theorem writeBatch_exists (heap : Heap Ptr) (reader : Ptr) (pending : List Ptr)
    (ready : Ready heap reader pending) : ∃ after, writeBatch heap reader pending = some after := by
  induction pending generalizing heap with
  | nil => exact ⟨heap, rfl⟩
  | cons source rest ih =>
    have forwardRoom : (heap.forward reader).Room := by
      have capacity := ready.2.2.1
      simp only [List.length_cons] at capacity
      exact Nat.lt_of_lt_of_le (by omega) capacity
    obtain ⟨middle, first⟩ := writeLink_exists heap reader source forwardRoom
      (ready.2.2.2 source List.mem_cons_self)
    obtain ⟨after, remaining⟩ := ih middle (ready_after_first ready first)
    exact ⟨after, by simp [writeBatch, first, remaining]⟩

/-- Both topology directions are represented. Revisions and own contents belong
to the store, but this relation does not claim that the C loop updates them. -/
def Represents {Entry : Type*} {size : Nat} (heap : Heap (Fin size))
    (state : Store Entry size) : Prop :=
  (∀ owner, (observe heap).forward owner = (state.members owner).deps) ∧
  (∀ source reader, reader ∈ (observe heap).reverse source ↔ reader ∈ state.observers source)

theorem prepared_publication_represents_topology {Entry : Type*} {size : Nat}
    (state : Store Entry size) (heap : Heap (Fin size)) (reader : Fin size)
    (sources : List (Fin size))
    (represented : Represents heap state) (observers : ObserverInvariant state)
    (ready : Ready heap reader (OrderedDependencyBatch.collectMissing
      (state.members reader).deps [] sources)) :
    ∃ after, writeBatch heap reader (OrderedDependencyBatch.collectMissing
        (state.members reader).deps [] sources) = some after ∧
      Represents after (OrderedDependencyBatch.publish state reader sources) := by
  let pending := OrderedDependencyBatch.collectMissing (state.members reader).deps [] sources
  obtain ⟨after, written⟩ := writeBatch_exists heap reader pending ready
  have refinement := (writeBatch_refines reader pending ready.1 written).1
  refine ⟨after, written, ?_, ?_⟩
  · intro owner
    rw [refinement, appendBatch_forward]
    by_cases same : owner = reader
    · subst owner
      simp only [↓reduceIte, represented.1]
      change _ = ((setDependencies state reader ((state.members reader).deps ++ pending)).members reader).deps
      exact (setDependencies_deps state reader _).symm
    · rw [if_neg same, represented.1]
      change _ = ((setDependencies state reader ((state.members reader).deps ++ pending)).members owner).deps
      simp only [setDependencies]
      split
      · rfl
      · simp [Function.update_of_ne same]
  · intro source owner
    rw [refinement, appendBatch_reverse_membership, represented.2]
    have afterInvariant := OrderedDependencyBatch.publish_observers state observers reader sources
    rw [afterInvariant source owner]
    change _ ↔ source ∈ ((setDependencies state reader ((state.members reader).deps ++ pending)).members owner).deps
    by_cases same : owner = reader
    · subst owner
      rw [setDependencies_deps]
      simp only [List.mem_append, observers source reader, true_and]
    · have old : ((setDependencies state reader ((state.members reader).deps ++ pending)).members owner).deps =
          (state.members owner).deps := by
        simp only [setDependencies]
        split
        · rfl
        · simp [Function.update_of_ne same]
      rw [old]
      simpa [same] using observers source owner

namespace Controls

def emptyWithRoom : Array32 (Fin 3) := ⟨[2, 2, 2], 0⟩
def base : Heap (Fin 3) := ⟨fun _ => emptyWithRoom, fun _ => emptyWithRoom⟩
def after : Option (Heap (Fin 3)) := writeBatch base 0 [1, 2]

theorem two_way_ordered_publication :
    after.map (fun heap => ((observe heap).forward 0,
      (observe heap).reverse 1, (observe heap).reverse 2)) = some ([1, 2], [0], [0]) := by decide

theorem intermediate_forward_is_not_atomic_publication :
    let forwardOnly : Heap (Fin 3) :=
      ⟨Function.update base.forward 0 ⟨[1, 2, 2], 1⟩, base.reverse⟩
    (observe forwardOnly).forward 0 = [1] ∧ (observe forwardOnly).reverse 1 = [] := by decide

theorem dropping_reverse_is_observable :
    (appendLink (observe base) 0 1).reverse 1 ≠ (observe base).reverse 1 := by decide

theorem duplicate_prepared_id_adds_duplicate_occurrence :
    (writeBatch base 0 [1, 1]).map (fun heap => (observe heap).forward 0) = some [1, 1] := by decide

end Controls

#print axioms writeLink_fields
#print axioms writeLink_refines
#print axioms writeBatch_refines
#print axioms appendBatch_forward
#print axioms appendBatch_reverse_membership
#print axioms writeLink_exists
#print axioms ready_after_first
#print axioms writeBatch_exists
#print axioms prepared_publication_represents_topology
#print axioms Controls.two_way_ordered_publication
#print axioms Controls.intermediate_forward_is_not_atomic_publication
#print axioms Controls.dropping_reverse_is_observable
#print axioms Controls.duplicate_prepared_id_adds_duplicate_occurrence

end Mettapedia.Machines.OrderedDependencyCArray
