import Mettapedia.Machines.OrderedDependencyStore

/-!
# Atomic batches of ordered dependency links

The preparation loop compares each input identity with the old forward list
and the pending list. It has no observable store writes. Publication changes
both directions once, after storage reservations succeed. The specification
uses ordered identity insertion independently of the preparation loop.

This is the allocation/publication model, not a proof about a C allocator.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyBatch

open OrderedDependencyIds OrderedDependencyStore

universe u v
variable {Id : Type u} [DecidableEq Id]

def collectMissing (existing : List Id) : List Id → List Id → List Id
  | pending, [] => pending
  | pending, source :: rest =>
      if source ∈ existing ∨ source ∈ pending then collectMissing existing pending rest
      else collectMissing existing (pending ++ [source]) rest

theorem collectMissing_realizes_insertion (existing pending sources : List Id) :
    existing ++ collectMissing existing pending sources =
      insertDeps (existing ++ pending) sources := by
  induction sources generalizing pending with
  | nil => rfl
  | cons source rest ih =>
      by_cases present : source ∈ existing ∨ source ∈ pending
      · have included : source ∈ existing ++ pending := List.mem_append.mpr present
        rw [collectMissing, if_pos present, insertDeps_cons, insertDep_of_mem included]
        exact ih pending
      · have absent : source ∉ existing ++ pending := by
          simpa only [List.mem_append] using present
        rw [collectMissing, if_neg present, insertDeps_cons, insertDep_of_not_mem absent]
        simpa only [List.append_assoc] using ih (pending ++ [source])

theorem prepared_realizes_insertion (existing sources : List Id) :
    existing ++ collectMissing existing [] sources = insertDeps existing sources := by
  simpa using collectMissing_realizes_insertion existing [] sources

theorem prepared_distinct (existing sources : List Id) (distinct : existing.Nodup) :
    (existing ++ collectMissing existing [] sources).Nodup := by
  rw [prepared_realizes_insertion]
  exact nodup_insertDeps sources distinct

theorem prepared_membership (existing sources : List Id) (member : Id) :
    member ∈ existing ++ collectMissing existing [] sources ↔
      member ∈ existing ∨ member ∈ sources := by
  rw [prepared_realizes_insertion]
  exact mem_insertDeps

theorem already_present_needs_no_reservation (existing sources : List Id)
    (present : ∀ source ∈ sources, source ∈ existing) :
    collectMissing existing [] sources = [] := by
  have same := prepared_realizes_insertion existing sources
  rw [insertDeps_of_forall_mem present] at same
  have lengths := congrArg List.length same
  simp only [List.length_append] at lengths
  have zero : (collectMissing existing [] sources).length = 0 := by omega
  cases found : collectMissing existing [] sources with
  | nil => rfl
  | cons head rest => simp [found] at zero

variable {Entry : Type v} {size : Nat}

def publish (s : Store Entry size) (reader : Fin size)
    (sources : List (Fin size)) : Store Entry size :=
  let old := (s.members reader).deps
  setDependencies s reader (old ++ collectMissing old [] sources)

/-- Declarative identity insertion and the two-list preparation algorithm
produce the same entire published store, not just the flattened answer. -/
theorem publish_realizes_specification (s : Store Entry size) (reader : Fin size)
    (sources : List (Fin size)) :
    publish s reader sources =
      setDependencies s reader (insertDeps (s.members reader).deps sources) := by
  simp only [publish, prepared_realizes_insertion]

theorem publish_observers (s : Store Entry size) (h : ObserverInvariant s)
    (reader : Fin size) (sources : List (Fin size)) :
    ObserverInvariant (publish s reader sources) :=
  setDependencies_observers s h reader _

theorem publish_distinct (s : Store Entry size) (h : DistinctDependencies s)
    (reader : Fin size) (sources : List (Fin size)) :
    DistinctDependencies (publish s reader sources) :=
  setDependencies_distinct s h reader _ (prepared_distinct _ sources (h reader))

theorem publish_keeps_own (s : Store Entry size) (reader member : Fin size)
    (sources : List (Fin size)) :
    ((publish s reader sources).members member).own = (s.members member).own :=
  setDependencies_own s reader member _

theorem publish_keeps_old_order (s : Store Entry size) (reader : Fin size)
    (sources : List (Fin size)) :
    (s.members reader).deps <+: ((publish s reader sources).members reader).deps := by
  rw [publish_realizes_specification, setDependencies_deps]
  exact prefix_insertDeps _ _

theorem publish_repeat (s : Store Entry size) (reader : Fin size)
    (sources : List (Fin size)) :
    publish (publish s reader sources) reader sources = publish s reader sources := by
  have included : ∀ source ∈ sources,
      source ∈ ((publish s reader sources).members reader).deps := by
    intro source present
    rw [publish_realizes_specification, setDependencies_deps]
    exact mem_insertDeps.mpr (.inr present)
  change setDependencies (publish s reader sources) reader
    (((publish s reader sources).members reader).deps ++
      collectMissing ((publish s reader sources).members reader).deps [] sources) = _
  rw [already_present_needs_no_reservation _ _ included, List.append_nil]
  simp only [setDependencies, ↓reduceIte]

/-- Failed reservations and invalid self-links never publish a partial batch.
For an already linked batch, no reservation is necessary. -/
def tryPublish (s : Store Entry size) (reader : Fin size)
    (sources : List (Fin size)) (reservationsSucceeded : Bool) : Option (Store Entry size) :=
  if reader ∈ sources then none else
  if collectMissing (s.members reader).deps [] sources = [] then some s else
  if reservationsSucceeded then some (publish s reader sources) else none

def afterAttempt (s : Store Entry size) (result : Option (Store Entry size)) :
    Store Entry size := result.getD s

theorem failed_attempt_is_identity (s : Store Entry size) :
    afterAttempt s none = s := rfl

theorem reservation_failure_does_not_publish (s : Store Entry size)
    (reader : Fin size) (sources : List (Fin size))
    (newLink : collectMissing (s.members reader).deps [] sources ≠ []) :
    afterAttempt s (tryPublish s reader sources false) = s := by
  by_cases self : reader ∈ sources <;>
    simp [tryPublish, afterAttempt, self, newLink]

theorem self_link_is_rejected (s : Store Entry size) (reader : Fin size)
    (sources : List (Fin size)) (included : reader ∈ sources) (success : Bool) :
    tryPublish s reader sources success = none := by simp [tryPublish, included]

theorem tryPublish_observers (s : Store Entry size) (h : ObserverInvariant s)
    (reader : Fin size) (sources : List (Fin size)) (success : Bool) :
    ObserverInvariant (afterAttempt s (tryPublish s reader sources success)) := by
  unfold tryPublish
  split
  · exact h
  · split
    · exact h
    · cases success
      · exact h
      · exact publish_observers s h reader sources

theorem tryPublish_distinct (s : Store Entry size) (h : DistinctDependencies s)
    (reader : Fin size) (sources : List (Fin size)) (success : Bool) :
    DistinctDependencies (afterAttempt s (tryPublish s reader sources success)) := by
  unfold tryPublish
  split
  · exact h
  · split
    · exact h
    · cases success
      · exact h
      · exact publish_distinct s h reader sources

namespace Controls

def own : Fin 4 → List Nat
  | 0 => [10]
  | 1 => [20, 20]
  | 2 => [30]
  | _ => [40]

def base : Store Nat 4 := initial 17 own
def linked : Store Nat 4 := afterAttempt base (tryPublish base 0 [1, 2, 1] true)

theorem published_order_and_duplicates : query linked 0 = [10, 20, 20, 30] := by decide

theorem reverse_publication_is_complete :
    0 ∈ linked.observers 1 ∧ 0 ∈ linked.observers 2 ∧
      (linked.members 0).deps = [1, 2] := by decide

theorem failure_leaves_whole_store_unchanged :
    afterAttempt base (tryPublish base 0 [1, 2, 1] false) = base := by
  exact reservation_failure_does_not_publish base 0 [1, 2, 1] (by decide)

theorem unchanged_batch_needs_no_allocation :
    tryPublish linked 0 [1, 2, 1] false = some linked := by
  have self : (0 : Fin 4) ∉ [1, 2, 1] := by decide
  have present : collectMissing (linked.members 0).deps [] [1, 2, 1] = [] := by decide
  simp only [tryPublish, if_neg self, if_pos present]

def partialForwardOnly : Store Nat 4 :=
  { base with members := Function.update base.members 0 { base.members 0 with deps := [1] } }

theorem partial_forward_publication_breaks_observers :
    ¬ ObserverInvariant partialForwardOnly := by
  intro invariant
  have wrong := (invariant 1 0).mpr (by decide)
  simp [partialForwardOnly, base, initial] at wrong

end Controls
end Mettapedia.Machines.OrderedDependencyBatch
