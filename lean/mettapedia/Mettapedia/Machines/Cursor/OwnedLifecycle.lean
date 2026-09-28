import Mettapedia.Machines.ResourceOwnership

/-!
# Publication and cancellation of owned answer cursors

Answer occurrences are kept in a list; ownership roots are a finite set of
owner/address pairs. Publishing duplicate occurrences therefore retains one
physical graph without erasing either occurrence. A bounded observation may
retain the residual. Commitment instead exports the selected answer roots,
removes the delimited owners, and collects the graph those remaining roots
can reach.

The resource graph is the finite heap of `ResourceOwnership`, whose liveness
uses the existing store-reachability judgment. Cancellation does not evaluate
the abandoned continuation and does not roll back the supplied world. Native
finalizer effects and relocation require their own implementation comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.OwnedLifecycle

open Mettapedia.Machines.ResourceOwnership

variable {Owner Address Value World : Type}
  [DecidableEq Owner] [DecidableEq Address]

/-- Root ownership is shared; answer occurrence multiplicity remains separate. -/
def answerRoots (owner : Owner) (answers : List Address) : Roots Owner Address :=
  (answers.map (fun address => (owner, address))).toFinset

@[simp] theorem mem_answerRoots (owner other : Owner)
    (answers : List Address) (address : Address) :
    (other, address) ∈ answerRoots owner answers ↔
      other = owner ∧ address ∈ answers := by
  simp only [answerRoots, List.mem_toFinset, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨source, member, sameOwner, sameAddress⟩
    exact ⟨sameOwner.symm, sameAddress ▸ member⟩
  · rintro ⟨rfl, member⟩
    exact ⟨address, member, rfl, rfl⟩

def publish (roots : Roots Owner Address) (owner : Owner)
    (answers : List Address) : Roots Owner Address :=
  roots ∪ answerRoots owner answers

theorem publish_mono (roots : Roots Owner Address) (owner : Owner)
    (answers : List Address) : roots ⊆ publish roots owner answers :=
  Finset.subset_union_left

/-- The output owner is a caller outside the delimiter being cancelled. -/
def commitRoots (roots : Roots Owner Address) (dead : Finset Owner)
    (output : Owner) (answers : List Address) : Roots Owner Address :=
  cancel (publish roots output answers) dead

theorem commitRoots_eq (roots : Roots Owner Address) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead) :
    commitRoots roots dead output answers =
      cancel roots dead ∪ answerRoots output answers := by
  ext pair
  rcases pair with ⟨owner, address⟩
  simp only [commitRoots, publish, mem_cancel, Finset.mem_union, mem_answerRoots]
  constructor
  · rintro ⟨old | ⟨rfl, selected⟩, surviving⟩
    · exact Or.inl ⟨old, surviving⟩
    · exact Or.inr ⟨rfl, selected⟩
  · rintro (⟨old, surviving⟩ | ⟨rfl, selected⟩)
    · exact ⟨Or.inl old, surviving⟩
    · exact ⟨Or.inr ⟨rfl, selected⟩, outside⟩

theorem retained_roots_subset_commit (roots : Roots Owner Address)
    (dead : Finset Owner) (output : Owner) (answers : List Address)
    (outside : output ∉ dead) :
    cancel roots dead ⊆ commitRoots roots dead output answers := by
  rw [commitRoots_eq roots dead output answers outside]
  exact Finset.subset_union_left

theorem answer_roots_subset_commit (roots : Roots Owner Address)
    (dead : Finset Owner) (output : Owner) (answers : List Address)
    (outside : output ∉ dead) :
    answerRoots output answers ⊆ commitRoots roots dead output answers := by
  rw [commitRoots_eq roots dead output answers outside]
  exact Finset.subset_union_right

/-- Selection exports a root before cancellation, including a root that was
previously reachable only through the abandoned cursor's internal graph. -/
theorem selected_live_after_commit (heap : Heap Address Value)
    (roots : Roots Owner Address) (dead : Finset Owner) (output : Owner)
    (answers : List Address) (outside : output ∉ dead)
    {address : Address} (selected : address ∈ answers)
    (allocated : address ∈ heap.allocated) :
    Live heap (commitRoots roots dead output answers) address := by
  apply live_of_root heap (commitRoots roots dead output answers)
  · apply answer_roots_subset_commit roots dead output answers outside
    exact (mem_answerRoots output output answers address).mpr ⟨rfl, selected⟩
  · exact allocated

/-- Every descendant of an exported answer survives, not just its top node. -/
theorem answer_graph_live_after_commit (heap : Heap Address Value)
    (roots : Roots Owner Address) (dead : Finset Owner) (output : Owner)
    (answers : List Address) (outside : output ∉ dead) {address : Address}
    (live : Live heap (answerRoots output answers) address) :
    Live heap (commitRoots roots dead output answers) address :=
  live_mono heap (answer_roots_subset_commit roots dead output answers outside) live

/-- The caller's surviving roots retain their entire reachable graphs. -/
theorem outer_graph_live_after_commit (heap : Heap Address Value)
    (roots : Roots Owner Address) (dead : Finset Owner) (output : Owner)
    (answers : List Address) (outside : output ∉ dead) {address : Address}
    (live : Live heap (cancel roots dead) address) :
    Live heap (commitRoots roots dead output answers) address :=
  live_mono heap (retained_roots_subset_commit roots dead output answers outside) live

/-- Publication followed by cancellation retains exactly the union of the
caller graph and exported answer graphs. No other old owner remains a root. -/
theorem live_commit_iff (heap : Heap Address Value)
    (roots : Roots Owner Address) (dead : Finset Owner) (output : Owner)
    (answers : List Address) (outside : output ∉ dead) (address : Address) :
    Live heap (commitRoots roots dead output answers) address ↔
      Live heap (cancel roots dead) address ∨
      Live heap (answerRoots output answers) address := by
  rw [commitRoots_eq roots dead output answers outside]
  rw [live_iff_root heap (cancel roots dead ∪ answerRoots output answers) address,
    live_iff_root heap (cancel roots dead) address,
    live_iff_root heap (answerRoots output answers) address]
  simp only [Finset.mem_union]
  constructor
  · rintro ⟨pair, retained | exported, live⟩
    · exact Or.inl ⟨pair, retained, live⟩
    · exact Or.inr ⟨pair, exported, live⟩
  · rintro (⟨pair, retained, live⟩ | ⟨pair, exported, live⟩)
    · exact ⟨pair, Or.inl retained, live⟩
    · exact ⟨pair, Or.inr exported, live⟩

/-- Resource collection operates below the semantic world. -/
structure Session (Owner Address Value World : Type)
    [DecidableEq Owner] [DecidableEq Address] where
  heap : Heap Address Value
  roots : Roots Owner Address
  world : World

noncomputable def closeScope (state : Session Owner Address Value World)
    (dead : Finset Owner) : Session Owner Address Value World :=
  let roots := cancel state.roots dead
  ⟨collect state.heap roots, roots, state.world⟩

noncomputable def commit (state : Session Owner Address Value World)
    (dead : Finset Owner) (output : Owner) (answers : List Address) :
    Session Owner Address Value World :=
  let roots := commitRoots state.roots dead output answers
  ⟨collect state.heap roots, roots, state.world⟩

@[simp] theorem closeScope_world (state : Session Owner Address Value World)
    (dead : Finset Owner) : (closeScope state dead).world = state.world := rfl

@[simp] theorem commit_world (state : Session Owner Address Value World)
    (dead : Finset Owner) (output : Owner) (answers : List Address) :
    (commit state dead output answers).world = state.world := rfl

/-- Complete cell lookup exposes payload, references and accounting size. -/
def observe (heap : Heap Address Value) (answers : List Address) :
    List (Option (Cell Address Value)) := answers.map heap.lookup

theorem commit_preserves_selected_observation
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead)
    (allocated : ∀ address ∈ answers, address ∈ state.heap.allocated) :
    observe (commit state dead output answers).heap answers =
      observe state.heap answers := by
  apply List.map_congr_left
  intro address selected
  exact lookup_collect_of_live state.heap _ (selected_live_after_commit
    state.heap state.roots dead output answers outside selected
      (allocated address selected))

theorem commit_preserves_answer_graph
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead)
    {address : Address} (live : Live state.heap (answerRoots output answers) address) :
    (commit state dead output answers).heap.lookup address = state.heap.lookup address :=
  lookup_collect_of_live state.heap _ (answer_graph_live_after_commit
    state.heap state.roots dead output answers outside live)

theorem commit_preserves_outer_graph
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead)
    {address : Address} (live : Live state.heap (cancel state.roots dead) address) :
    (commit state dead output answers).heap.lookup address = state.heap.lookup address :=
  lookup_collect_of_live state.heap _ (outer_graph_live_after_commit
    state.heap state.roots dead output answers outside live)

/-- Garbage from the abandoned search is reclaimed unless either an outer
owner or a published answer still reaches it, possibly through a cycle. -/
theorem commit_reclaims_unprotected
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead)
    (address : Address)
    (notOuter : ¬ Live state.heap (cancel state.roots dead) address)
    (notAnswer : ¬ Live state.heap (answerRoots output answers) address) :
    (commit state dead output answers).heap.lookup address = none := by
  apply lookup_collect_of_not_live state.heap _
  rw [live_commit_iff state.heap state.roots dead output answers outside address]
  exact not_or.mpr ⟨notOuter, notAnswer⟩

theorem closeScope_reclaims_final_owner
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (address : Address)
    (lastOwners : ∀ pair ∈ state.roots,
      Live state.heap {pair} address → pair.1 ∈ dead) :
    (closeScope state dead).heap.lookup address = none :=
  final_owners_reclaimed state.heap state.roots dead address lastOwners

/-- The output list is not quotiented by the root set. -/
theorem duplicate_answer_observation
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (output : Owner) (address : Address) (outside : output ∉ dead)
    (allocated : address ∈ state.heap.allocated) :
    observe (commit state dead output [address, address]).heap [address, address] =
      [state.heap.lookup address, state.heap.lookup address] := by
  rw [commit_preserves_selected_observation state dead output [address, address]
    outside (by
      intro other member
      have same : other = address := by simpa using member
      simpa [same] using allocated)]
  rfl

theorem answerRoots_card_le (owner : Owner) (answers : List Address) :
    (answerRoots owner answers).card ≤ answers.length := by
  simpa only [answerRoots, List.length_map] using
    List.toFinset_card_le (answers.map (fun address => (owner, address)))

theorem commit_root_count (roots : Roots Owner Address) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead) :
    (commitRoots roots dead output answers).card ≤ roots.card + answers.length := by
  rw [commitRoots_eq roots dead output answers outside]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (Finset.card_le_card (cancel_subset roots dead))
      (answerRoots_card_le output answers))

/-- Bounded publication has a bounded retained heap only when the transitive
footprint and cell-size hypotheses also hold. An answer count alone is not a
bound on the graph behind those answers. Shared graphs are counted only once
by the actual collector; the right side is a conservative upper bound. -/
theorem commit_byte_bound (state : Session Owner Address Value World)
    (dead : Finset Owner) (output : Owner) (answers : List Address)
    (outside : output ∉ dead) (perRoot bytes : Nat)
    (bounded : ∀ pair ∈ commitRoots state.roots dead output answers,
      (footprint state.heap {pair}).card ≤ perRoot)
    (weights : ∀ address ∈ footprint state.heap
      (commitRoots state.roots dead output answers),
      cellBytes state.heap address ≤ bytes) :
    allocatedBytes (commit state dead output answers).heap ≤
      (state.roots.card + answers.length) * perRoot * bytes := by
  change allocatedBytes (collect state.heap _) ≤ _
  rw [allocatedBytes_collect]
  exact retainedBytes_le_root_footprints state.heap _ _ perRoot bytes
    (commit_root_count state.roots dead output answers outside) bounded weights

namespace Examples

open ResourceOwnership.Examples

def cursorSession : Session Nat (Fin 3) Nat Nat :=
  ⟨cyclicHeap, {(0, 0)}, 7⟩

/-- The yielded value is a descendant of the cursor's old root. Publishing
it to the caller preserves both it and its shared cyclic successor. -/
theorem export_before_close_survives :
    (commit cursorSession {0} 1 [1]).heap.lookup 1 = some (cyclicCell 1) ∧
    (commit cursorSession {0} 1 [1]).heap.lookup 2 = some (cyclicCell 2) := by
  have root : Live cyclicHeap (answerRoots 1 [1]) 1 :=
    live_of_root cyclicHeap _ (owner := 1) (by simp) (by decide)
  constructor
  · exact commit_preserves_answer_graph cursorSession {0} 1 [1] (by decide) root
  · exact commit_preserves_answer_graph cursorSession {0} 1 [1] (by decide)
      (live_step cyclicHeap _ root rfl (by decide))

/-- Closing before publishing an escaping answer destroys the cell that its
pointer used to denote. Publishing the answer before closing preserves it. -/
theorem close_before_export_loses_answer :
    (closeScope cursorSession {0}).heap.lookup 1 = none ∧
    (commit cursorSession {0} 1 [1]).heap.lookup 1 ≠ none := by
  constructor
  · apply closeScope_reclaims_final_owner
    intro pair member _
    have same : pair = (0, 0) := by simpa [cursorSession] using member
    simp [same]
  · rw [export_before_close_survives.1]
    exact Option.some_ne_none _

/-- Publishing into the very scope being cancelled cannot export a value. -/
theorem canceled_output_owner_is_not_export :
    (commit cursorSession {0} 0 [1]).heap.lookup 1 = none := by
  have cleared : commitRoots cursorSession.roots {0} 0 [1] = ∅ := by decide
  change (collect cyclicHeap _).lookup 1 = none
  rw [cleared]
  exact lookup_collect_of_not_live cyclicHeap _ (not_live_empty cyclicHeap 1)

end Examples

end Mettapedia.Machines.Cursor.OwnedLifecycle
