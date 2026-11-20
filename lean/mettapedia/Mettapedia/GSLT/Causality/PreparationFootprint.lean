import Mettapedia.GSLT.Causality.ResourceWaves

/-!
# The resource footprint of parallel task preparation

An owner prepares tasks from a catalogue of its occurrences. Preparing a task
takes that occurrence and one of the owner's worker credits, and reads one
version of the shared source, identified by an instance and a revision.
The read is persistent: any number of tasks share it.

Wave admission over this footprint is exactly capacity: a selection of tasks
is enabled iff it is a sub-multiset of the catalogue and it has at most as
many tasks as there are worker credits (`enabled_iff`). The read never limits
the wave, and reusing one occurrence needs two copies of it
(`Controls.occurrence_and_shared_read`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.PreparationFootprint

open ResourceInteraction

variable {K : Type} [DecidableEq K]

/-- The three kinds of resource in the footprint. -/
inductive Resource (K : Type) where
  | occurrence (owner item : K)
  | source (instanceId revision : K)
  | worker (owner : K)
  deriving DecidableEq

/-- Preparing item `item` consumes its occurrence and a worker credit, and
reads the source version. It produces nothing. -/
def system (owner instanceId revision : K) : System (Resource K) where
  Site := Unit
  Instance := fun _ => K
  consume := fun item => {.occurrence owner item, .worker owner}
  read := fun _ => {.source instanceId revision}
  produce := fun _ => 0

def entry (owner instanceId revision item : K) : (system owner instanceId revision).Entry :=
  ⟨(), item⟩

def entries (owner instanceId revision : K) (items : List K) :
    List (system owner instanceId revision).Entry :=
  items.map (entry owner instanceId revision)

/-- The supply: one occurrence per catalogue item, the source version and the
available worker credits. -/
def supply (owner instanceId revision : K) (catalogue : List K) (workers : Nat) :
    Multiset (Resource K) :=
  (catalogue.map (Resource.occurrence owner) : Multiset (Resource K)) +
    {Resource.source instanceId revision} + Multiset.replicate workers (.worker owner)

omit [DecidableEq K] in
theorem consumption (owner instanceId revision : K) (items : List K) :
    (system owner instanceId revision).stepConsume (entries owner instanceId revision items) =
      (items.map (Resource.occurrence owner) : Multiset (Resource K)) +
        Multiset.replicate items.length (.worker owner) := by
  induction items with
  | nil => simp [entries, System.stepConsume]
  | cons item rest ih =>
      change (system owner instanceId revision).consume item +
          (system owner instanceId revision).stepConsume (entries owner instanceId revision rest) = _
      rw [ih]
      simp only [system, List.map_cons, ← Multiset.cons_coe, List.length_cons,
        Multiset.replicate_succ, ← Multiset.singleton_add]
      rw [Multiset.insert_eq_cons, ← Multiset.singleton_add]
      ac_rfl

theorem persistent_read (owner instanceId revision : K) (items : List K) :
    (system owner instanceId revision).stepRead (entries owner instanceId revision items) =
      if items = [] then 0 else {Resource.source instanceId revision} := by
  induction items with
  | nil => simp [entries, System.stepRead]
  | cons item rest ih =>
      change (system owner instanceId revision).read item ∪
          (system owner instanceId revision).stepRead (entries owner instanceId revision rest) = _
      rw [ih]
      by_cases empty : rest = []
      · simp [system, empty]
      · simpa [system, empty] using
          (Multiset.eq_union_left (s := {Resource.source instanceId revision}) le_rfl)

@[simp] theorem occurrence_count (owner item : K) (items : List K) :
    (items.map (Resource.occurrence owner)).count (.occurrence owner item) = items.count item :=
  List.count_map_of_injective items (Resource.occurrence owner)
    (fun _ _ same => (Resource.occurrence.inj same).2) item

@[simp] theorem occurrence_other_count (owner other item : K) (items : List K)
    (different : other ≠ owner) :
    (items.map (Resource.occurrence owner)).count (.occurrence other item) = 0 := by
  apply List.count_eq_zero.mpr
  simp only [List.mem_map]
  rintro ⟨found, _, same⟩
  exact different (Resource.occurrence.inj same).1.symm

/-- Admission of a preparation wave is exactly catalogue availability and
worker capacity; the shared read imposes no further bound. -/
theorem enabled_iff (owner instanceId revision : K) (catalogue selected : List K)
    (workers : Nat) :
    (system owner instanceId revision).StepEnables
        (supply owner instanceId revision catalogue workers)
        (entries owner instanceId revision selected) ↔
      (selected : Multiset K) ≤ catalogue ∧ selected.length ≤ workers := by
  rw [System.StepEnables, consumption, persistent_read, Multiset.le_iff_count]
  by_cases empty : selected = []
  · subst selected
    simp [supply]
  rw [if_neg empty]
  constructor
  · intro fits
    refine ⟨Multiset.le_iff_count.mpr ?_, ?_⟩
    · intro item
      simpa [supply, Multiset.count_replicate] using fits (.occurrence owner item)
    · simpa [supply, Multiset.count_replicate] using fits (.worker owner)
  · rintro ⟨owned, capacity⟩ resource
    cases resource with
    | occurrence other item =>
        by_cases sameOwner : other = owner
        · subst other
          simpa [supply, Multiset.count_replicate] using (Multiset.le_iff_count.mp owned) item
        · simp [supply, Multiset.count_replicate, sameOwner]
    | source otherInstance otherRevision =>
        simp [supply, Multiset.count_replicate]
    | worker other =>
        by_cases sameOwner : other = owner
        · subst other
          simpa [supply, Multiset.count_replicate] using capacity
        · simp [supply, Multiset.count_replicate, Ne.symm sameOwner]

namespace Controls

/-- `consumption`: a repeated item consumes two copies of its occurrence and
two worker credits ... -/
theorem repeated_item_consumes_twice :
    (system 7 9 11).stepConsume (entries 7 9 11 [1, 1]) =
      ({.occurrence 7 1, .occurrence 7 1, .worker 7, .worker 7} : Multiset (Resource ℕ)) := by
  rw [consumption]
  decide

/-- `persistent_read`: ... while two tasks read the source once, and an empty
selection reads nothing. -/
theorem shared_read_once :
    (system 7 9 11).stepRead (entries 7 9 11 [1, 2]) = {Resource.source 9 11} ∧
      (system 7 9 11).stepRead (entries 7 9 11 []) = 0 := by
  rw [persistent_read, persistent_read]
  decide

/-- `occurrence_count`, `occurrence_other_count`: occurrences are counted per
owner; the distinct-owner hypothesis is needed, since the owner's own
occurrence is counted. -/
theorem occurrence_counts :
    ([1, 2, 1].map (Resource.occurrence 7)).count (.occurrence 7 1) = 2 ∧
      ([1, 2, 1].map (Resource.occurrence 7)).count (.occurrence 8 1) = 0 := by
  decide

/-- `enabled_iff`: two distinct tasks on two worker credits share the one
source read; reusing one occurrence twice needs two copies of it even with two
credits; and two tasks need two credits. -/
theorem occurrence_and_shared_read :
    (system 7 9 11).StepEnables (supply 7 9 11 [1, 2] 2) (entries 7 9 11 [1, 2]) ∧
      ¬ (system 7 9 11).StepEnables (supply 7 9 11 [1] 2) (entries 7 9 11 [1, 1]) ∧
      ¬ (system 7 9 11).StepEnables (supply 7 9 11 [1, 2] 1) (entries 7 9 11 [1, 2]) := by
  rw [enabled_iff, enabled_iff, enabled_iff]
  decide

end Controls

end Mettapedia.GSLT.Causality.PreparationFootprint
