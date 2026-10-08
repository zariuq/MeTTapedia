import Mettapedia.Machines.ResourceOwnership
import Mettapedia.Algebra.OccurrenceIdentity
import Mettapedia.Machines.Cursor.TailSummary

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
the abandoned continuation and does not roll back the supplied world. A checked
address and payload relocation preserves publication, selected observations and
retained bytes, including duplicate answer occurrences. Native root discovery,
finalizers and the implementation of that copy remain separate obligations.
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

/-- Publishing the starts of the captured paths protects their whole
reachable graphs. Failed paths and duplicated observations remain unchanged. -/
theorem commit_preserves_paths
    (state : Session Owner Address Value World) (dead : Finset Owner)
    (output : Owner) (paths : List (Address × List Address)) (outside : output ∉ dead)
    (allocated : ∀ query ∈ paths, query.1 ∈ state.heap.allocated) :
    RequestBorrow.observe (commit state dead output (paths.map Prod.fst)).heap paths =
      RequestBorrow.observe state.heap paths := by
  apply List.map_congr_left
  intro query member
  exact walk_collect state.heap _ (selected_live_after_commit state.heap state.roots dead
    output (paths.map Prod.fst) outside (List.mem_map.mpr ⟨query, member, rfl⟩)
      (allocated query member)) query.2

section Relocation

variable {DestinationAddress DestinationValue : Type}
variable [DecidableEq DestinationAddress]

/-- Copying resource storage keeps the actual semantic world. Host authority
must be checked separately before a runtime installs this session. -/
def relocateSession (state : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation state.heap destination) :
    Session Owner DestinationAddress DestinationValue World :=
  ⟨destination, copy.roots state.roots, state.world⟩

theorem relocate_answerRoots {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (owner : Owner) (answers : List Address) :
    copy.roots (answerRoots owner answers) =
      answerRoots owner (answers.map copy.address) := by
  ext pair
  rcases pair with ⟨other, address⟩
  rw [mem_answerRoots]
  constructor
  · intro member
    obtain ⟨⟨originalOwner, original⟩, present, same⟩ := Finset.mem_image.mp member
    have selected := (mem_answerRoots owner originalOwner answers original).mp present
    exact ⟨(congrArg Prod.fst same).symm.trans selected.1,
      List.mem_map.mpr ⟨original, selected.2, congrArg Prod.snd same⟩⟩
  · rintro ⟨sameOwner, member⟩
    obtain ⟨original, present, sameAddress⟩ := List.mem_map.mp member
    exact Finset.mem_image.mpr ⟨(owner, original),
      (mem_answerRoots owner owner answers original).mpr ⟨rfl, present⟩,
      Prod.ext sameOwner.symm sameAddress⟩

/-- Publication and delimiter cancellation commute with the checked copy.
Owner identities are kept; selected occurrence order remains in the list. -/
theorem relocate_commitRoots {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (dead : Finset Owner) (output : Owner) (answers : List Address) :
    copy.roots (commitRoots roots dead output answers) =
      commitRoots (copy.roots roots) dead output (answers.map copy.address) := by
  have publication : copy.roots (publish roots output answers) =
      publish (copy.roots roots) output (answers.map copy.address) := by
    unfold publish
    rw [show copy.roots (roots ∪ answerRoots output answers) =
      copy.roots roots ∪ copy.roots (answerRoots output answers) from Finset.image_union _ _]
    rw [relocate_answerRoots copy]
  unfold commitRoots
  rw [copy.roots_cancel, publication]

omit [DecidableEq Address] in
/-- Complete cells are read from destination storage. No equality of payloads
substitutes for transporting their outgoing references. -/
theorem relocate_observation {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (answers : List Address) :
    observe destination (answers.map copy.address) =
      (observe source answers).map (Option.map (Cell.relocate copy.address copy.payload)) := by
  simp only [observe, List.map_map]
  apply List.map_congr_left
  intro address _
  exact copy.lookup_eq address

/-- An exported answer survives cancellation in either representation, with
the same ordered occurrence list and transported complete cells. -/
theorem relocate_commit_observation
    (state : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation state.heap destination) (dead : Finset Owner)
    (output : Owner) (answers : List Address) (outside : output ∉ dead)
    (allocated : ∀ address ∈ answers, address ∈ state.heap.allocated) :
    observe (commit (relocateSession state destination copy) dead output
      (answers.map copy.address)).heap (answers.map copy.address) =
      (observe (commit state dead output answers).heap answers).map
        (Option.map (Cell.relocate copy.address copy.payload)) := by
  rw [commit_preserves_selected_observation state dead output answers outside allocated]
  rw [commit_preserves_selected_observation]
  · exact relocate_observation copy answers
  · exact outside
  · intro address member
    obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
    exact (copy.allocated_iff original).mpr (allocated original selected)

/-- A copied capture can be read after retiring its source scope. The reads
use the destination graph, with every ordered path and alias transported. -/
theorem relocate_commit_paths
    (state : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation state.heap destination) (dead : Finset Owner)
    (output : Owner) (paths : List (Address × List Address)) (outside : output ∉ dead)
    (allocated : ∀ query ∈ paths, query.1 ∈ state.heap.allocated) :
    RequestBorrow.observe (commit (relocateSession state destination copy) dead output
        ((RequestBorrow.relocatePaths copy.address paths).map Prod.fst)).heap
      (RequestBorrow.relocatePaths copy.address paths) =
      (RequestBorrow.observe state.heap paths).map (Option.map fun pair =>
        (copy.address pair.1, pair.2.relocate copy.address copy.payload)) := by
  rw [commit_preserves_paths]
  · exact copy.observe_paths_eq paths
  · exact outside
  · intro query member
    obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
    exact (copy.allocated_iff original.1).mpr (allocated original selected)

/-- Cursor publication supplies the destination roots for a checked borrow.
Source refusal is preserved, and an accepted view reads only the graph left
after publication and cancellation. Repeated and failed paths stay ordered. -/
theorem relocate_commit_checked_borrow
    (state : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation state.heap destination) (dead : Finset Owner)
    (output : Owner) (epoch : Nat) (sourceStamp : RequestBorrow.Stamp Owner)
    (view : RequestBorrow.View Owner Address) (outside : output ∉ dead)
    (allocated : ∀ query ∈ view.paths, query.1 ∈ state.heap.allocated) :
    (RequestBorrow.transport ⟨sourceStamp, state.heap⟩
        ⟨⟨output, epoch⟩, destination⟩ copy view).bind
      (RequestBorrow.read ⟨⟨output, epoch⟩,
        (commit (relocateSession state destination copy) dead output
          ((RequestBorrow.relocatePaths copy.address view.paths).map Prod.fst)).heap⟩) =
      (RequestBorrow.read ⟨sourceStamp, state.heap⟩ view).map
        (List.map (Option.map fun pair =>
          (copy.address pair.1, pair.2.relocate copy.address copy.payload))) := by
  by_cases issued : view.stamp = sourceStamp
  · simp only [RequestBorrow.transport, RequestBorrow.View.transportIfCurrent, if_pos issued, Option.bind_some,
      RequestBorrow.read, ↓reduceIte, Option.map_some]
    congr 1
    exact relocate_commit_paths state destination copy dead output view.paths outside allocated
  · simp only [RequestBorrow.transport, RequestBorrow.View.transportIfCurrent, Option.bind_none, RequestBorrow.read,
      if_neg issued, Option.map_none]

/-- The copied and original published graphs have equal retained byte
weights. Copying and speculative execution work are separate charges. -/
theorem relocate_commit_storage
    (state : Session Owner Address Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation state.heap destination) (dead : Finset Owner)
    (output : Owner) (answers : List Address) :
    allocatedBytes (commit (relocateSession state destination copy) dead output
      (answers.map copy.address)).heap = allocatedBytes (commit state dead output answers).heap := by
  change allocatedBytes (collect destination
    (commitRoots (copy.roots state.roots) dead output (answers.map copy.address))) =
      allocatedBytes (collect state.heap (commitRoots state.roots dead output answers))
  rw [allocatedBytes_collect, allocatedBytes_collect,
    ← relocate_commitRoots copy state.roots dead output answers, copy.retainedBytes_eq]

end Relocation

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

/-! ## Amortized transport for useful collections

The native single-frontier collector publishes a fresh copy only when at least
one quarter of the old arena is discarded. The following account uses measured
byte counts, separate from producer firings and answer multiplicities. It bounds
the bytes copied by successful collections in terms of ordinary allocation;
declined copy attempts and copy-table metadata are separate implementation costs.
-/

namespace CollectionAccounting

/-- Allocation since the previous collection, followed by the bytes retained
in the freshly published region. These counts need not count answer occurrences. -/
structure Cycle where
  allocated : Nat
  retained : Nat

def copiedBytes (cycles : List Cycle) : Nat :=
  (cycles.map Cycle.retained).sum

def allocatedBetween (cycles : List Cycle) : Nat :=
  (cycles.map Cycle.allocated).sum

def endingBytes (initial : Nat) : List Cycle → Nat
  | [] => initial
  | cycle :: rest => endingBytes cycle.retained rest

/-- Integer-rounded quarter reclamation, with a nontrivial collection floor.
The native floor of 64 KiB is stronger than the twelve bytes needed here. -/
def Useful (initial : Nat) : List Cycle → Prop
  | [] => True
  | cycle :: rest =>
      12 ≤ initial + cycle.allocated ∧
      cycle.retained ≤ initial + cycle.allocated - (initial + cycle.allocated) / 4 ∧
      Useful cycle.retained rest

theorem retained_le_four_discarded (before after : Nat)
    (floor : 12 ≤ before) (useful : after ≤ before - before / 4) :
    after ≤ 4 * (before - after) := by
  omega

/-- The retained heap is a potential. Each accepted copy spends at most four
times the potential released by reclamation, including integer rounding. -/
theorem copied_with_potential_le (cycles : List Cycle) (initial : Nat)
    (useful : Useful initial cycles) :
    copiedBytes cycles + 4 * endingBytes initial cycles ≤
      4 * (initial + allocatedBetween cycles) := by
  induction cycles generalizing initial with
  | nil => simp [copiedBytes, allocatedBetween, endingBytes]
  | cons cycle rest ih =>
      obtain ⟨floor, reclaimed, remaining⟩ := useful
      have step := retained_le_four_discarded
        (initial + cycle.allocated) cycle.retained floor reclaimed
      have tail := ih cycle.retained remaining
      simp only [copiedBytes, allocatedBetween, List.map_cons, List.sum_cons,
        endingBytes] at *
      omega

/-- Arbitrarily many successful collections cannot repeatedly charge the same
unchanged live graph: cumulative copied bytes are bounded by incoming storage. -/
theorem copied_le_allocated (cycles : List Cycle) (initial : Nat)
    (useful : Useful initial cycles) :
    copiedBytes cycles ≤ 4 * (initial + allocatedBetween cycles) := by
  have bound := copied_with_potential_le cycles initial useful
  omega

/-- A real sequence allocates 100 bytes per interval, retains ten, and copies
only thirty across its three successful collections. -/
theorem repeated_small_frontier :
    Useful 0 [⟨100, 10⟩, ⟨100, 10⟩, ⟨100, 10⟩] ∧
    copiedBytes [⟨100, 10⟩, ⟨100, 10⟩, ⟨100, 10⟩] = 30 := by
  simp [Useful, copiedBytes]

/-- Without the useful-reclamation check, repeated copies of the unchanged
graph violate the allocation bound. This is rejected by the actual policy. -/
theorem full_copy_is_not_useful :
    let cycles : List Cycle := List.replicate 5 ⟨0, 100⟩
    ¬ Useful 100 cycles ∧
    copiedBytes cycles > 4 * (100 + allocatedBetween cycles) := by
  simp [Useful, copiedBytes, allocatedBetween, List.replicate_succ]

end CollectionAccounting

namespace SpeculativeBudget

/-- Storage relocation is not a new execution allowance. These mathematical
events do not prescribe a native history allocation. The graph preservation
obligations of collection are established separately above. -/
inductive Event where
  | transition | collection
  deriving DecidableEq

def transitions : List Event → Nat
  | [] => 0
  | .transition :: rest => 1 + transitions rest
  | .collection :: rest => transitions rest

/-- The native cursor checks the transition purse before executing the next
step. Collection may reclaim storage but leaves this purse unchanged. -/
def spend : Nat → List Event → Option Nat
  | remaining, [] => some remaining
  | 0, .transition :: _ => none
  | remaining + 1, .transition :: rest => spend remaining rest
  | remaining, .collection :: rest => spend remaining rest

/-- The operational purse agrees with the independently counted transitions,
including traces with arbitrarily many intervening collections. -/
theorem spend_eq_some_iff (events : List Event) (budget remaining : Nat) :
    spend budget events = some remaining ↔ transitions events + remaining = budget := by
  induction events generalizing budget with
  | nil => simp [spend, transitions, eq_comm]
  | cons event rest ih =>
      cases event with
      | collection => exact ih budget
      | transition =>
          cases budget with
          | zero => simp [spend, transitions]
          | succ budget =>
              simp only [spend, transitions]
              rw [ih]
              omega

/-- An accepted attempt never executes more transitions than originally
granted, even when dead storage is repeatedly reclaimed. -/
theorem accepted_work_bound (events : List Event) (budget remaining : Nat)
    (accepted : spend budget events = some remaining) : transitions events ≤ budget := by
  have exactCount := (spend_eq_some_iff events budget remaining).mp accepted
  omega

/-- Splitting execution for observation does not invent another allowance. -/
theorem spend_append (first second : List Event) (budget : Nat) :
    spend budget (first ++ second) =
      (spend budget first).bind (fun remaining => spend remaining second) := by
  induction first generalizing budget with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | collection => exact ih budget
      | transition =>
          cases budget with
          | zero => rfl
          | succ budget => exact ih budget

theorem collections_preserve_remaining (count budget : Nat) :
    spend budget (List.replicate count .collection) = some budget := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [List.replicate_succ, spend] using ih

/-- Collection cannot make a second step legal under a one-step purse;
a separately granted two-step purse admits the same execution. -/
theorem reclamation_is_not_reauthorization :
    spend 1 [.transition, .collection, .transition] = none ∧
    spend 2 [.transition, .collection, .transition] = some 0 := by decide

end SpeculativeBudget

/-! ## Suspended multi-frame frontiers -/

namespace Frontier

/-- Continuation identity and its instruction position survive storage moves.
The locals are roots, even when no current argument refers to them. -/
structure Capture (Address : Type) where
  identity : Nat
  equation : Nat
  step : Nat
  slot : Nat
  locals : List Address
  deriving DecidableEq, Repr

structure Frame (Address : Type) where
  identity : Nat
  nextEquation : Nat
  arguments : List Address
  continuations : List (Capture Address)
  deriving DecidableEq, Repr

/-- Pending delivery and an undo frontier are retained until their boundary
is discharged. A collector that cannot enumerate them must decline there. -/
structure State (Address : Type) where
  frames : List (Frame Address)
  pending : List Address
  undo : List (Frame Address)
  deriving DecidableEq, Repr

def Capture.map {B : Type} (f : Address → B) (capture : Capture Address) : Capture B :=
  ⟨capture.identity, capture.equation, capture.step, capture.slot, capture.locals.map f⟩

def Frame.map {B : Type} (f : Address → B) (frame : Frame Address) : Frame B :=
  ⟨frame.identity, frame.nextEquation, frame.arguments.map f,
    frame.continuations.map (Capture.map f)⟩

def State.map {B : Type} (f : Address → B) (state : State Address) : State B :=
  ⟨state.frames.map (Frame.map f), state.pending.map f,
    state.undo.map (Frame.map f)⟩

def captureRoots : List (Capture Address) → List Address
  | [] => []
  | capture :: rest => capture.locals ++ captureRoots rest

def Frame.roots (frame : Frame Address) : List Address :=
  frame.arguments ++ captureRoots frame.continuations

def frameRoots : List (Frame Address) → List Address
  | [] => []
  | frame :: rest => frame.roots ++ frameRoots rest

def State.rootList (state : State Address) : List Address :=
  frameRoots state.frames ++ state.pending ++ frameRoots state.undo

def State.roots (state : State Address) (owner : Owner) : Roots Owner Address :=
  answerRoots owner state.rootList

omit [DecidableEq Owner] [DecidableEq Address] in
theorem captureRoots_map {B : Type} (f : Address → B)
    (captures : List (Capture Address)) :
    captureRoots (captures.map (Capture.map f)) = (captureRoots captures).map f := by
  induction captures with
  | nil => rfl
  | cons capture rest ih => simp [captureRoots, Capture.map, ih]

omit [DecidableEq Owner] [DecidableEq Address] in
theorem Frame.roots_map {B : Type} (f : Address → B) (frame : Frame Address) :
    (frame.map f).roots = frame.roots.map f := by
  simp [Frame.map, Frame.roots, captureRoots_map]

omit [DecidableEq Owner] [DecidableEq Address] in
theorem frameRoots_map {B : Type} (f : Address → B) (frames : List (Frame Address)) :
    frameRoots (frames.map (Frame.map f)) = (frameRoots frames).map f := by
  induction frames with
  | nil => rfl
  | cons frame rest ih => simp [frameRoots, Frame.roots_map, ih]

omit [DecidableEq Owner] [DecidableEq Address] in
theorem State.rootList_map {B : Type} (f : Address → B) (state : State Address) :
    (state.map f).rootList = state.rootList.map f := by
  simp [State.map, State.rootList, frameRoots_map]

section Copy

variable {B W : Type} [DecidableEq B]
variable {source : Heap Address Value} {destination : Heap B W}

/-- One injective relocation is shared by arguments, saved locals, pending
delivery and undo roots. Separate copy episodes need not preserve aliases. -/
theorem relocated_roots (copy : Relocation source destination)
    (state : State Address) (owner : Owner) :
    (state.map copy.address).roots owner = copy.roots (state.roots owner) := by
  rw [State.roots, State.rootList_map, ← relocate_answerRoots]
  rfl

omit [DecidableEq Address] in
theorem saved_observations (copy : Relocation source destination)
    (state : State Address) :
    observe destination (state.map copy.address).rootList =
      (observe source state.rootList).map
        (Option.map (Cell.relocate copy.address copy.payload)) := by
  rw [State.rootList_map]
  exact relocate_observation copy state.rootList

/-- This includes aliases between a current argument and a continuation
local, and shared descendants reached by different captured paths. -/
theorem saved_aliases (copy : Relocation source destination)
    (argument saved : Address) (argumentPath localPath : List Address) :
    Aliases destination (copy.address argument) (argumentPath.map copy.address)
        (copy.address saved) (localPath.map copy.address) ↔
      Aliases source argument argumentPath saved localPath :=
  copy.aliases_iff argument saved argumentPath localPath

omit [DecidableEq Address] in
/-- Ordered equation positions are not inferred again after copying. -/
theorem equation_positions (copy : Relocation source destination) (state : State Address) :
    (state.map copy.address).frames.map (fun frame => (frame.identity, frame.nextEquation)) =
      state.frames.map (fun frame => (frame.identity, frame.nextEquation)) := by
  simp [State.map, List.map_map, Frame.map]

theorem retirement_preserves_saved_graph (copy : Relocation source destination)
    (state : State Address) (oldOwner nextOwner : Owner) (different : nextOwner ≠ oldOwner)
    (address : Address) (live : Live source (state.roots oldOwner) address) :
    Live destination
      (release (transfer ((state.map copy.address).roots oldOwner) oldOwner nextOwner)
        oldOwner) (copy.address address) := by
  rw [relocated_roots copy]
  apply copy.live_after_source_retirement _ oldOwner nextOwner different _ address live
  intro pair member
  exact ((mem_answerRoots oldOwner pair.1 state.rootList pair.2).mp member).1

end Copy

/-- The native collector copies the live projection, not every allocation
ever made in the source arena. Closing that projection before relocation
preserves every enumerated root observation while discarding old garbage. -/
theorem collected_saved_observations (heap : Heap Address Value)
    (state : State Address) (owner : Owner) {B W : Type} [DecidableEq B]
    (destination : Heap B W)
    (copy : Relocation (collect heap (state.roots owner)) destination)
    (allocated : ∀ address ∈ state.rootList, address ∈ heap.allocated) :
    observe destination (state.map copy.address).rootList =
      (observe heap state.rootList).map (Option.map (Cell.relocate copy.address copy.payload)) := by
  rw [saved_observations copy]
  congr 1
  apply List.map_congr_left
  intro address member
  exact lookup_collect_of_live heap _ (live_of_root heap _
    ((mem_answerRoots owner owner state.rootList address).mpr ⟨rfl, member⟩)
    (allocated address member))



/-- The graph bound counts all transitive storage beneath each live root.
The metadata term accounts separately for frames and continuation records.
There is no completed-iteration term; bounding root count alone is insufficient. -/
theorem storage_bound (heap : Heap Address Value) (state : State Address) (owner : Owner)
    (rootLimit perRoot cellSize metadata metadataLimit : Nat)
    (rootCount : state.rootList.length ≤ rootLimit)
    (bounded : ∀ pair ∈ state.roots owner, (footprint heap {pair}).card ≤ perRoot)
    (weights : ∀ address ∈ footprint heap (state.roots owner),
      cellBytes heap address ≤ cellSize)
    (metadataBound : metadata ≤ metadataLimit) :
    allocatedBytes (collect heap (state.roots owner)) + metadata ≤
      rootLimit * perRoot * cellSize + metadataLimit := by
  rw [allocatedBytes_collect]
  apply Nat.add_le_add _ metadataBound
  apply retainedBytes_le_root_footprints heap _ rootLimit perRoot cellSize _ bounded weights
  exact (List.toFinset_card_le _).trans (by simpa [State.roots, answerRoots] using rootCount)

namespace Controls

def savedOnly : State (Fin 3) :=
  ⟨[⟨4, 1, [0], [⟨8, 2, 3, 0, [2, 2]⟩]⟩], [1], []⟩

theorem omitted_saved_local_is_missing :
    savedOnly.rootList = [0, 2, 2, 1] ∧
      (2 : Fin 3) ∉ frameRoots [⟨4, 1, [0], []⟩] := by decide

theorem shared_saved_root_remains_two_occurrences :
    (savedOnly.map (fun address => address.val + 10)).rootList = [10, 12, 12, 11] :=
  by decide

end Controls

end Frontier

/-! ## Authentication and transport of issued returns

An issued handle is authenticated against four independent registry fields.
Physical store identity is separate from logical occurrence identity; the
parent lineage stays with the external continuation owner. The executable
scan below exposes its visited-row cost and is checked against membership,
not defined by that membership judgment. Payload relocation and complete
root discovery remain separate from registry authentication.
-/

namespace IssuedReturn

open Mettapedia.Algebra

variable {Provider : Type} [DecidableEq Provider]

structure Row (Address Provider : Type) where
  occurrence : Nat
  token : Nat
  payload : Address
  provider : Provider
  deriving DecidableEq, Repr

structure Handle (Address Provider : Type) where
  store : Nat
  parent : Nat
  row : Row Address Provider
  deriving DecidableEq, Repr

structure Registry (Address Provider : Type) where
  identity : Nat
  rows : List (Row Address Provider)
  deriving DecidableEq, Repr

def rowMatches (row wanted : Row Address Provider) : Bool :=
  row.occurrence == wanted.occurrence && row.token == wanted.token &&
    row.payload == wanted.payload && row.provider == wanted.provider

theorem rowMatches_iff (row wanted : Row Address Provider) :
    rowMatches row wanted = true ↔ row = wanted := by
  cases row
  cases wanted
  simp [rowMatches, Row.mk.injEq, and_assoc]

/-- Linear search returns the first matching physical slot and charges each
row it actually visits. A refusal after exhausting the rows keeps that cost. -/
def scan (wanted : Row Address Provider) : List (Row Address Provider) → Option Nat × Nat
  | [] => (none, 0)
  | row :: rest =>
      if rowMatches row wanted then (some 0, 1)
      else
        let tail := scan wanted rest
        (tail.1.map Nat.succ, tail.2 + 1)

theorem scan_none_iff (wanted : Row Address Provider) (rows : List (Row Address Provider)) :
    (scan wanted rows).1 = none ↔ wanted ∉ rows := by
  induction rows with
  | nil => simp [scan]
  | cons row rest ih =>
      by_cases same : row = wanted
      · subst row
        simp [scan, (rowMatches_iff wanted wanted).mpr rfl]
      · have different : rowMatches row wanted = false := by
          cases found : rowMatches row wanted with
          | false => rfl
          | true => exact (same ((rowMatches_iff row wanted).mp found)).elim
        simp [scan, different, ih, Ne.symm same]

theorem scan_selected (wanted : Row Address Provider) (rows : List (Row Address Provider))
    (index : Nat) (selected : (scan wanted rows).1 = some index) :
    rows[index]? = some wanted ∧ (scan wanted rows).2 = index + 1 := by
  induction rows generalizing index with
  | nil => simp [scan] at selected
  | cons row rest ih =>
      by_cases found : rowMatches row wanted = true
      · have same := (rowMatches_iff row wanted).mp found
        simp only [scan, found, if_true, Option.some.injEq] at selected
        subst index
        constructor
        · exact congrArg some same
        · simp only [scan, found, if_true]
      · have different : rowMatches row wanted = false := Bool.eq_false_iff.mpr found
        simp only [scan, different, Bool.false_eq_true, if_false] at selected
        obtain ⟨tailIndex, accepted, rfl⟩ := Option.map_eq_some_iff.mp selected
        obtain ⟨lookup, visits⟩ := ih tailIndex accepted
        constructor
        · simpa only [List.getElem?_cons_succ] using lookup
        · simp only [scan, different, Bool.false_eq_true, if_false]
          rw [visits]

theorem scan_refused_cost (wanted : Row Address Provider)
    (rows : List (Row Address Provider)) (refused : (scan wanted rows).1 = none) :
    (scan wanted rows).2 = rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      have absent := (scan_none_iff wanted (row :: rest)).mp refused
      have different : rowMatches row wanted = false := by
        apply Bool.eq_false_iff.mpr
        intro found
        exact absent (List.mem_cons.mpr (Or.inl ((rowMatches_iff row wanted).mp found).symm))
      have tailRefused : (scan wanted rest).1 = none :=
        (scan_none_iff wanted rest).mpr (fun member => absent (List.mem_cons_of_mem _ member))
      simp only [scan, different, Bool.false_eq_true, if_false,
        List.length_cons, ih tailRefused]

theorem scan_visits_le (wanted : Row Address Provider) (rows : List (Row Address Provider)) :
    (scan wanted rows).2 ≤ rows.length := by
  induction rows with
  | nil => exact Nat.le_refl _
  | cons row rest ih =>
      simp only [scan]
      split
      · exact Nat.succ_le_succ (Nat.zero_le rest.length)
      · simp only [List.length_cons]
        exact Nat.succ_le_succ ih

/-- Store and token zero are refusal sentinels. Parent lineage is not a
registry field and cannot be authenticated by this lookup alone. -/
def lookup (registry : Registry Address Provider) (handle : Handle Address Provider) :
    Option Nat × Nat :=
  if handle.store = 0 ∨ handle.store ≠ registry.identity ∨ handle.row.token = 0 then
    (none, 0)
  else scan handle.row registry.rows

def Authenticated (registry : Registry Address Provider)
    (handle : Handle Address Provider) : Prop :=
  handle.store ≠ 0 ∧ handle.store = registry.identity ∧
    handle.row.token ≠ 0 ∧ handle.row ∈ registry.rows

theorem lookup_authenticates (registry : Registry Address Provider)
    (handle : Handle Address Provider) :
    (lookup registry handle).1 ≠ none ↔ Authenticated registry handle := by
  by_cases invalid : handle.store = 0 ∨ handle.store ≠ registry.identity ∨ handle.row.token = 0
  · simp only [lookup, if_pos invalid, ne_eq, not_true_eq_false]
    simp only [Authenticated]
    tauto
  · simp only [lookup, if_neg invalid, Authenticated, ne_eq, scan_none_iff]
    tauto

theorem lookup_wrong_store (registry : Registry Address Provider)
    (handle : Handle Address Provider) (wrong : handle.store ≠ registry.identity) :
    lookup registry handle = (none, 0) := by
  simp [lookup, wrong]

theorem lookup_selected (registry : Registry Address Provider)
    (handle : Handle Address Provider) (index : Nat)
    (selected : (lookup registry handle).1 = some index) :
    registry.rows[index]? = some handle.row ∧ (lookup registry handle).2 = index + 1 := by
  by_cases invalid : handle.store = 0 ∨ handle.store ≠ registry.identity ∨ handle.row.token = 0
  · simp [lookup, invalid] at selected
  · simpa only [lookup, if_neg invalid] using
      scan_selected handle.row registry.rows index (by simpa only [lookup, if_neg invalid] using selected)

theorem lookup_visits_le (registry : Registry Address Provider) (handle : Handle Address Provider) :
    (lookup registry handle).2 ≤ registry.rows.length := by
  simp only [lookup]
  split
  · exact Nat.zero_le _
  · exact scan_visits_le handle.row registry.rows

def Row.map {B : Type} (address : Address → B) (row : Row Address Provider) : Row B Provider :=
  ⟨row.occurrence, row.token, address row.payload, row.provider⟩

omit [DecidableEq Address] [DecidableEq Provider] in
theorem Row.map_injective {B : Type} (address : Address → B)
    (injective : Function.Injective address) : Function.Injective (Row.map (Provider := Provider) address) := by
  intro left right same
  cases left
  cases right
  simp only [Row.map, Row.mk.injEq] at same ⊢
  exact ⟨same.1, same.2.1, injective same.2.2.1, same.2.2.2⟩

theorem rowMatches_map {B : Type} [DecidableEq B] (address : Address → B)
    (injective : Function.Injective address) (row wanted : Row Address Provider) :
    rowMatches (row.map address) (wanted.map address) = rowMatches row wanted := by
  apply Bool.eq_iff_iff.mpr
  rw [rowMatches_iff, rowMatches_iff]
  exact ⟨fun same => Row.map_injective address injective same, congrArg (Row.map address)⟩

/-- A single injective relocation keeps the actual slot and its lookup cost.
Equal values at different addresses are not coalesced. -/
theorem scan_map {B : Type} [DecidableEq B] (address : Address → B)
    (injective : Function.Injective address) (wanted : Row Address Provider)
    (rows : List (Row Address Provider)) :
    scan (wanted.map address) (rows.map (Row.map address)) = scan wanted rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [List.map_cons, scan, rowMatches_map address injective, ih]

def Registry.relocate {B : Type} (fresh : Nat) (address : Address → B)
    (registry : Registry Address Provider) : Registry B Provider :=
  ⟨fresh, registry.rows.map (Row.map address)⟩

def Handle.relocate {B : Type} (fresh : Nat) (address : Address → B)
    (handle : Handle Address Provider) : Handle B Provider :=
  ⟨fresh, handle.parent, handle.row.map address⟩

/-- Only handles already owned by the source store enter this transport.
Blindly rekeying a foreign handle would discard that authentication premise. -/
theorem lookup_relocate {B : Type} [DecidableEq B] (address : Address → B)
    (injective : Function.Injective address) (registry : Registry Address Provider)
    (handle : Handle Address Provider) (fresh : Nat)
    (owned : handle.store = registry.identity) (sourceLive : registry.identity ≠ 0)
    (destinationLive : fresh ≠ 0) :
    lookup (registry.relocate fresh address) (handle.relocate fresh address) =
      lookup registry handle := by
  have sourceGuard :
      (handle.store = 0 ∨ handle.store ≠ registry.identity ∨ handle.row.token = 0) ↔
        handle.row.token = 0 := by
    rw [owned]
    simp [sourceLive]
  have destinationGuard :
      ((handle.relocate fresh address).store = 0 ∨
        (handle.relocate fresh address).store ≠ (registry.relocate fresh address).identity ∨
        (handle.relocate fresh address).row.token = 0) ↔ handle.row.token = 0 := by
    simp [Handle.relocate, Registry.relocate, Row.map, destinationLive]
  simp only [lookup, sourceGuard, destinationGuard]
  split
  · rfl
  · exact scan_map address injective handle.row registry.rows

theorem transported_authentication {B : Type} [DecidableEq B] (address : Address → B)
    (injective : Function.Injective address) (registry : Registry Address Provider)
    (handle : Handle Address Provider) (fresh : Nat)
    (owned : handle.store = registry.identity) (sourceLive : registry.identity ≠ 0)
    (destinationLive : fresh ≠ 0) :
    Authenticated (registry.relocate fresh address) (handle.relocate fresh address) ↔
      Authenticated registry handle := by
  rw [← lookup_authenticates, lookup_relocate address injective registry handle fresh
    owned sourceLive destinationLive, lookup_authenticates]

omit [DecidableEq Address] in
theorem old_return_refused {B : Type} [DecidableEq B] (address : Address → B)
    (registry : Registry Address Provider) (handle : Handle B Provider) (fresh : Nat)
    (old : handle.store = registry.identity) (different : registry.identity ≠ fresh) :
    lookup (registry.relocate fresh address) handle = (none, 0) := by
  apply lookup_wrong_store
  simpa only [Registry.relocate, old] using different

/-- Checked complete preparation preserves every issued-handle membership.
The prepared enumeration may change its scan positions and lookup costs. -/
theorem coverage_authentication (registry : Registry Address Provider)
    (proposed : List (Row Address Provider))
    (checked : OccurrenceIdentity.coverageCheck Row.occurrence registry.rows proposed = true)
    (handle : Handle Address Provider) :
    Authenticated { registry with rows := proposed } handle ↔ Authenticated registry handle := by
  have complete := (OccurrenceIdentity.coverageCheck_iff Row.occurrence registry.rows proposed).mp checked
  simp only [Authenticated, complete.1.mem_iff]

/-- Payload root discovery keeps one physical root for aliases without
forgetting the logical occurrences checked by complete coverage. -/
theorem coverage_payload_roots (actual proposed : List (Row Address Provider))
    (checked : OccurrenceIdentity.coverageCheck Row.occurrence actual proposed = true)
    (owner : Owner) :
    answerRoots owner (proposed.map Row.payload) = answerRoots owner (actual.map Row.payload) := by
  have complete := (OccurrenceIdentity.coverageCheck_iff Row.occurrence actual proposed).mp checked
  ext pair
  rw [mem_answerRoots, mem_answerRoots]
  exact and_congr_right (fun _ => (complete.1.map Row.payload).mem_iff)

section GraphTransport

variable {B W : Type} [DecidableEq B]
variable {source : Heap Address Value} {destination : Heap B W}

/-- Authentication and liveness are distinct premises. One injective graph
copy preserves the issued slot, lookup work and every reachable payload path
after publication to a different owner and retirement of the original. -/
theorem transported_return_retirement (copy : Relocation source destination)
    (registry : Registry Address Provider) (handle : Handle Address Provider) (fresh : Nat)
    (owned : handle.store = registry.identity) (sourceLive : registry.identity ≠ 0)
    (destinationLive : fresh ≠ 0) (roots : Roots Owner Address)
    (originalOwner nextOwner : Owner) (different : nextOwner ≠ originalOwner)
    (ownedRoots : ∀ pair ∈ roots, pair.1 = originalOwner)
    (rooted : Live source roots handle.row.payload) (path : List Address) :
    lookup (registry.relocate fresh copy.address) (handle.relocate fresh copy.address) =
        lookup registry handle ∧
      walk (collect destination
        (release (transfer (copy.roots roots) originalOwner nextOwner) originalOwner))
        (copy.address handle.row.payload) (path.map copy.address) =
        (walk source handle.row.payload path).map (fun result =>
          (copy.address result.1, result.2.relocate copy.address copy.payload)) := by
  constructor
  · exact lookup_relocate copy.address copy.injective registry handle fresh
      owned sourceLive destinationLive
  · rw [walk_collect destination _
      (copy.live_after_source_retirement roots originalOwner nextOwner different ownedRoots _ rooted)]
    exact copy.walk_eq handle.row.payload path

end GraphTransport

namespace Controls

def source : Registry Nat Nat := ⟨17, [⟨7, 41, 0, 5⟩, ⟨8, 42, 0, 5⟩]⟩
def first : Handle Nat Nat := ⟨17, 6, ⟨7, 41, 0, 5⟩⟩
def second : Handle Nat Nat := ⟨17, 6, ⟨8, 42, 0, 5⟩⟩

/-- The target table is independently authored, with a relocated shared
payload and fresh physical store identity. Logical occurrences stay distinct. -/
def destination : Registry Nat Nat := ⟨31, [⟨7, 41, 10, 5⟩, ⟨8, 42, 10, 5⟩]⟩
def firstCopied : Handle Nat Nat := ⟨31, 6, ⟨7, 41, 10, 5⟩⟩
def secondCopied : Handle Nat Nat := ⟨31, 6, ⟨8, 42, 10, 5⟩⟩

theorem distinct_occurrences_share_payload :
    lookup source first = (some 0, 1) ∧ lookup source second = (some 1, 2) ∧
      lookup destination firstCopied = (some 0, 1) ∧
      lookup destination secondCopied = (some 1, 2) ∧
      firstCopied.row.payload = secondCopied.row.payload ∧
      firstCopied.row.occurrence ≠ secondCopied.row.occurrence := by decide

theorem exact_fields_and_fresh_store_are_required :
    lookup destination { firstCopied with store := 17 } = (none, 0) ∧
      lookup destination { firstCopied with row.token := 42 } = (none, 2) ∧
      lookup destination { firstCopied with row.occurrence := 8 } = (none, 2) ∧
      lookup destination { firstCopied with row.payload := 11 } = (none, 2) ∧
      lookup destination { firstCopied with row.provider := 9 } = (none, 2) := by decide

theorem zero_sentinels_decline_without_scan :
    lookup destination { firstCopied with store := 0 } = (none, 0) ∧
      lookup destination { firstCopied with row.token := 0 } = (none, 0) := by decide

/-- The four-field lease table does not attest to the externally retained
parent lineage. A separately checked parent checkpoint remains necessary. -/
theorem parent_lineage_is_external :
    lookup destination { firstCopied with parent := 999 } = (some 0, 1) := by decide

theorem blindly_rekeying_foreign_handle_authenticates :
    lookup source { first with store := 99 } = (none, 0) ∧
      lookup destination (({ first with store := 99 } : Handle Nat Nat).relocate
        31 (fun address => address + 10)) = (some 0, 1) := by decide

/-- Coalescing distinct payload addresses admits a handle refused at source,
even though occurrence and token have not changed. -/
theorem lossy_payload_map_invents_authentication :
    lookup source { first with row.payload := 1 } = (none, 2) ∧
      lookup (source.relocate 31 (fun _ => 0))
        (({ first with row.payload := 1 } : Handle Nat Nat).relocate 31 (fun _ => 0)) =
        (some 0, 1) := by decide

theorem complete_preparation_keeps_aliases_and_occurrences :
    OccurrenceIdentity.coverageCheck Row.occurrence source.rows [second.row, first.row] = true ∧
      OccurrenceIdentity.coverageCheck Row.occurrence source.rows [first.row, first.row] = false := by decide

open ResourceOwnership.Examples

def rootedRegistry : Registry (Fin 3) Nat := ⟨17, [⟨7, 41, 0, 5⟩]⟩
def rootedHandle : Handle (Fin 3) Nat := ⟨17, 6, ⟨7, 41, 0, 5⟩⟩
def copiedRegistry : Registry (Fin 4) Nat := ⟨31, [⟨7, 41, 1, 5⟩]⟩
def copiedHandle : Handle (Fin 4) Nat := ⟨31, 6, ⟨7, 41, 1, 5⟩⟩

/-- A transferred return remains authenticated and its shared cyclic
descendant can be read after the old owner has retired. -/
theorem transferred_return_keeps_cyclic_payload :
    lookup copiedRegistry copiedHandle = (some 0, 1) ∧
      walk (collect copiedHeap
        (release (transfer (shiftedCopy.roots ({(0, 0)} : Roots Nat (Fin 3))) 0 7) 0))
        1 [2, 3] = some (3, copiedCell 3) := by
  constructor
  · decide
  · have transported := transported_return_retirement shiftedCopy rootedRegistry rootedHandle 31
      (by decide) (by decide) (by decide) ({(0, 0)} : Roots Nat (Fin 3)) 0 7
      (by decide) (by intro pair member; exact congrArg Prod.fst (Finset.mem_singleton.mp member))
      (live_of_root cyclicHeap _ (owner := 0) (by decide) (by decide)) [1, 2]
    exact transported.2

/-- Successful registry lookup alone cannot keep any payload alive. -/
theorem accepted_handle_without_roots_loses_payload :
    lookup copiedRegistry copiedHandle = (some 0, 1) ∧
      walk (collect copiedHeap (∅ : Roots Nat (Fin 4))) 1 [2, 3] = none := by
  constructor
  · decide
  · have absent : (collect copiedHeap (∅ : Roots Nat (Fin 4))).lookup 1 = none :=
      lookup_collect_of_not_live copiedHeap _ (not_live_empty copiedHeap 1)
    simp only [walk, absent, Option.bind_none]

end Controls

/-! ## Issuing, returning and requeueing authenticated occurrences -/

open Mettapedia.Algebra.OccurrenceIdentity
open Mettapedia.Machines.Cursor.TailSummary

/-- Authentication charges the actual visited prefix even when no release
occurs. Success retires exactly that physical registry row and clears only
its issued authority; payload, provider, occurrence and parent are retained. -/
def releaseIssued (registry : Registry Address Provider) (handle : Handle Address Provider) :
    Option (Registry Address Provider × Handle Address Provider) × Nat :=
  let found := lookup registry handle
  let reply := do
    let index ← found.1
    let pair ← extractByLast index registry.rows
    some ({ registry with rows := pair.2 },
      { handle with store := 0, row.token := 0 })
  (reply, found.2)

theorem releaseIssued_account (registry : Registry Address Provider)
    (handle : Handle Address Provider) :
    (releaseIssued registry handle).2 = (lookup registry handle).2 := rfl

theorem releaseIssued_refused (registry : Registry Address Provider)
    (handle : Handle Address Provider) (refused : (lookup registry handle).1 = none) :
    releaseIssued registry handle = (none, (lookup registry handle).2) := by
  simp only [releaseIssued, refused, bind, Option.bind_none]

theorem releaseIssued_selected (registry : Registry Address Provider)
    (handle : Handle Address Provider) (index : Nat)
    (accepted : (lookup registry handle).1 = some index) :
    ∃ remaining,
      releaseIssued registry handle =
        (some ({ registry with rows := remaining },
          { handle with store := 0, row.token := 0 }), index + 1) ∧
      (handle.row :: remaining).Perm registry.rows := by
  obtain ⟨atIndex, cost⟩ := lookup_selected registry handle index accepted
  have picked := extractByLast_selected index registry.rows
  rw [atIndex] at picked
  obtain ⟨pair, extraction, same⟩ := Option.map_eq_some_iff.mp picked
  have selected : pair.1 = handle.row := same
  refine ⟨pair.2, ?_, ?_⟩
  · simp only [releaseIssued, accepted, extraction, cost, bind, Option.bind_some]
  · simpa only [← selected] using
      extractByLast_permutation index registry.rows pair.1 pair.2 extraction

theorem releaseIssued_keeps_other (registry : Registry Address Provider)
    (handle survivor : Handle Address Provider)
    (next : Registry Address Provider) (cleared : Handle Address Provider)
    (visits : Nat)
    (released : releaseIssued registry handle = (some (next, cleared), visits))
    (different : survivor.row ≠ handle.row) :
    Authenticated next survivor ↔ Authenticated registry survivor := by
  cases found : (lookup registry handle).1 with
  | none =>
      have failed := releaseIssued_refused registry handle found
      rw [failed] at released
      cases (congrArg (fun result => result.1) released)
  | some index =>
      obtain ⟨remaining, exactRelease, retained⟩ := releaseIssued_selected registry handle index found
      rw [exactRelease] at released
      have equality := Option.some.inj (congrArg Prod.fst released)
      have registryEqual := congrArg Prod.fst equality
      dsimp only at registryEqual
      have sameMembers : survivor.row ∈ remaining ↔ survivor.row ∈ registry.rows := by
        simpa only [List.mem_cons, different, false_or] using
          (retained.mem_iff (a := survivor.row))
      rw [← registryEqual]
      simp only [Authenticated, sameMembers]

theorem releaseIssued_removes_unique (registry : Registry Address Provider)
    (handle : Handle Address Provider) (next : Registry Address Provider)
    (cleared : Handle Address Provider) (visits : Nat)
    (released : releaseIssued registry handle = (some (next, cleared), visits))
    (unique : registry.rows.Nodup) :
    handle.row ∉ next.rows ∧ next.rows.Nodup ∧ next.rows.length + 1 = registry.rows.length := by
  cases found : (lookup registry handle).1 with
  | none =>
      rw [releaseIssued_refused registry handle found] at released
      cases (congrArg (fun result => result.1) released)
  | some index =>
      obtain ⟨remaining, exactRelease, retained⟩ := releaseIssued_selected registry handle index found
      rw [exactRelease] at released
      have equality := Option.some.inj (congrArg Prod.fst released)
      have registryEqual := congrArg Prod.fst equality
      dsimp only at registryEqual
      rw [← registryEqual]
      have nodup := retained.nodup_iff.mpr unique
      obtain ⟨removed, survivors⟩ := List.nodup_cons.mp nodup
      exact ⟨removed, survivors, retained.length_eq⟩



/-- Relocation commutes with physical-row release, including its visited-prefix
account and the complete surviving registry order. Only the issued handle is
rekeyed; clearing its authority remains clearing, rather than a new issue. -/
theorem releaseIssued_relocate {B : Type} [DecidableEq B]
    (address : Address → B) (injective : Function.Injective address)
    (registry : Registry Address Provider) (handle : Handle Address Provider)
    (fresh : Nat) (owned : handle.store = registry.identity)
    (sourceLive : registry.identity ≠ 0) (destinationLive : fresh ≠ 0) :
    releaseIssued (registry.relocate fresh address) (handle.relocate fresh address) =
      ((releaseIssued registry handle).1.map (fun pair =>
        (pair.1.relocate fresh address, pair.2.relocate 0 address)),
        (releaseIssued registry handle).2) := by
  unfold releaseIssued
  rw [lookup_relocate address injective registry handle fresh owned sourceLive destinationLive]
  cases found : (lookup registry handle).1 with
  | none => simp only [found, bind, Option.bind_none, Option.map_none]
  | some index =>
      simp only [found, Registry.relocate, bind, Option.bind_some, extractByLast_map]
      cases extractByLast index registry.rows with
      | none => rfl
      | some pair => rfl


namespace EditControls

def third : Row Nat Nat := ⟨9, 43, 0, 5⟩
def source : Registry Nat Nat := ⟨17, [Controls.first.row, Controls.second.row, third]⟩
def afterRelease : Registry Nat Nat := ⟨17, [third, Controls.second.row]⟩

theorem swapping_changes_later_lookup_cost :
    releaseIssued source Controls.first =
      (some (afterRelease, { Controls.first with store := 0, row.token := 0 }), 1) ∧
      lookup source ⟨17, 6, third⟩ = (some 2, 3) ∧
      lookup afterRelease ⟨17, 6, third⟩ = (some 0, 1) := by decide

theorem refused_authentication_retains_visited_work :
    releaseIssued source { Controls.first with row.provider := 999 } = (none, 3) ∧
      releaseIssued source { Controls.first with store := 999 } = (none, 0) := by decide

theorem release_preserves_payload_parent_and_provider :
    (releaseIssued source Controls.first).1.map (fun pair =>
      (pair.2.parent, pair.2.row.payload, pair.2.row.provider, pair.2.row.occurrence)) =
        some (6, 0, 5, 7) ∧
      (releaseIssued source { Controls.first with parent := 999 }).1.map (fun pair => pair.2.parent) =
        some 999 := by decide

end EditControls

namespace TransportEditControls

def moved : Registry Nat Nat := EditControls.source.relocate 70 (fun n => n + 10)
def movedFirst : Handle Nat Nat := Controls.first.relocate 70 (fun n => n + 10)

theorem release_keeps_aliases_and_scan_positions :
    releaseIssued moved movedFirst =
      (some (EditControls.afterRelease.relocate 70 (fun n => n + 10),
        ({ Controls.first with store := 0, row.token := 0 }).relocate 0 (fun n => n + 10)), 1) ∧
      lookup (EditControls.afterRelease.relocate 70 (fun n => n + 10))
        ((⟨17, 6, EditControls.third⟩ : Handle Nat Nat).relocate 70 (fun n => n + 10)) =
        (some 0, 1) := by decide

theorem stale_handle_is_not_rekeyed_by_release :
    releaseIssued moved Controls.first = (none, 0) := by decide

end TransportEditControls


/-- Separate issued occurrences and tokens; payloads may be shared. Positive
identity fields are namespace authority, not a pointer-lifetime proof. -/
def Registry.Valid (registry : Registry Address Provider) : Prop :=
  registry.identity ≠ 0 ∧
    (registry.rows.map Row.occurrence).Nodup ∧
    (registry.rows.map Row.token).Nodup ∧
    ∀ row ∈ registry.rows, row.occurrence ≠ 0 ∧ row.token ≠ 0

omit [DecidableEq Address] [DecidableEq Provider] in
theorem Registry.Valid.rows_unique (registry : Registry Address Provider)
    (valid : registry.Valid) : registry.rows.Nodup :=
  List.Nodup.of_map Row.occurrence valid.2.1

theorem releaseIssued_preserves_validity (registry : Registry Address Provider)
    (handle : Handle Address Provider) (next : Registry Address Provider)
    (cleared : Handle Address Provider) (visits : Nat)
    (valid : registry.Valid)
    (released : releaseIssued registry handle = (some (next, cleared), visits)) :
    next.Valid := by
  cases found : (lookup registry handle).1 with
  | none =>
      rw [releaseIssued_refused registry handle found] at released
      cases (congrArg (fun result => result.1) released)
  | some index =>
      obtain ⟨remaining, exactRelease, retained⟩ := releaseIssued_selected registry handle index found
      rw [exactRelease] at released
      have equality := Option.some.inj (congrArg Prod.fst released)
      have sameRegistry := congrArg Prod.fst equality
      dsimp only at sameRegistry
      rw [← sameRegistry]
      refine ⟨valid.1, ?_, ?_, ?_⟩
      · have whole := (retained.map Row.occurrence).nodup_iff.mpr valid.2.1
        exact (List.nodup_cons.mp whole).2
      · have whole := (retained.map Row.token).nodup_iff.mpr valid.2.2.1
        exact (List.nodup_cons.mp whole).2
      · intro row present
        apply valid.2.2.2 row
        apply retained.mem_iff.mp
        exact List.mem_cons_of_mem _ present

theorem releaseIssued_revokes_old_and_cleared (registry : Registry Address Provider)
    (handle : Handle Address Provider) (next : Registry Address Provider)
    (cleared : Handle Address Provider) (visits : Nat)
    (valid : registry.Valid)
    (released : releaseIssued registry handle = (some (next, cleared), visits)) :
    ¬ Authenticated next handle ∧ lookup next cleared = (none, 0) := by
  have removed := releaseIssued_removes_unique registry handle next cleared visits released
    (valid.rows_unique registry)
  have noOld : ¬ Authenticated next handle := by
    intro authorized
    exact removed.1 authorized.2.2.2
  refine ⟨noOld, ?_⟩
  cases found : (lookup registry handle).1 with
  | none =>
      rw [releaseIssued_refused registry handle found] at released
      cases (congrArg (fun result => result.1) released)
  | some index =>
      obtain ⟨remaining, exactRelease, _⟩ := releaseIssued_selected registry handle index found
      rw [exactRelease] at released
      have equality := Option.some.inj (congrArg Prod.fst released)
      have sameHandle := congrArg Prod.snd equality
      dsimp only at sameHandle
      rw [← sameHandle]
      simp [lookup]

namespace ValidEditControls

theorem registry_keys_are_independent_of_aliases :
    EditControls.source.Valid ∧
      EditControls.source.rows.map Row.payload = [0, 0, 0] := by unfold Registry.Valid; decide

theorem duplicate_occurrence_with_different_token_is_invalid :
    ¬ ({ EditControls.source with rows :=
      [Controls.first.row, { Controls.first.row with token := 100 }] }).Valid := by unfold Registry.Valid; decide

theorem duplicate_token_with_different_occurrence_is_invalid :
    ¬ ({ EditControls.source with rows :=
      [Controls.first.row, { Controls.first.row with occurrence := 100 }] }).Valid := by unfold Registry.Valid; decide

end ValidEditControls


/-- A failed complete prefix remains in the charge when a following segment
supplies the first matching row. No membership claim is imported from a
compiled getter. -/
theorem scan_append_of_missing (wanted : Row Address Provider)
    (prior following : List (Row Address Provider)) (absent : wanted ∉ prior) :
    scan wanted (prior ++ following) =
      ((scan wanted following).1.map (fun index => prior.length + index),
        prior.length + (scan wanted following).2) := by
  induction prior with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.zero_add]
      cases result : scan wanted following with
      | mk found visits =>
          cases found <;> rfl
  | cons row rest ih =>
      have different : rowMatches row wanted = false := by
        apply Bool.eq_false_iff.mpr
        intro same
        exact absent (List.mem_cons.mpr (Or.inl ((rowMatches_iff row wanted).mp same).symm))
      have tailAbsent : wanted ∉ rest := fun h => absent (List.mem_cons_of_mem row h)
      rw [List.cons_append, scan, different]
      simp only [Bool.false_eq_true, if_false, ih tailAbsent, List.length_cons,
        Option.map_map, Nat.add_assoc, Nat.add_comm]
      congr 2
      funext index
      simp only [Function.comp_apply]
      omega

/-- Issued-row publication after its reservation and queue-selection boundary.
Only the token and store are new; the parent and payload/provider occurrence
come from the selected handle. Allocation and selection costs are separate. -/
def registerIssued (registry : Registry Address Provider)
    (selected : Handle Address Provider) (token : Nat) :
    Registry Address Provider × Handle Address Provider :=
  let issued := { selected with store := registry.identity, row.token := token }
  ({ registry with rows := registry.rows ++ [issued.row] }, issued)

omit [DecidableEq Address] [DecidableEq Provider] in
theorem registerIssued_authenticates (registry : Registry Address Provider)
    (selected : Handle Address Provider) (token : Nat)
    (live : registry.identity ≠ 0) (positive : token ≠ 0) :
    Authenticated (registerIssued registry selected token).1
      (registerIssued registry selected token).2 := by
  simp [registerIssued, Authenticated, live, positive]

theorem registerIssued_lookup (registry : Registry Address Provider)
    (selected : Handle Address Provider) (token : Nat)
    (live : registry.identity ≠ 0) (positive : token ≠ 0)
    (freshOccurrence : selected.row.occurrence ∉ registry.rows.map Row.occurrence) :
    lookup (registerIssued registry selected token).1
      (registerIssued registry selected token).2 =
      (some registry.rows.length, registry.rows.length + 1) := by
  have absent : { selected.row with token := token } ∉ registry.rows := by
    intro present
    apply freshOccurrence
    exact List.mem_map.mpr ⟨_, present, rfl⟩
  change lookup
    ⟨registry.identity, registry.rows ++ [{ selected.row with token := token }]⟩
    ⟨registry.identity, selected.parent, { selected.row with token := token }⟩ = _
  simp only [lookup, live, positive, ne_eq]
  rw [scan_append_of_missing _ _ _ absent]
  simp [scan, rowMatches]

omit [DecidableEq Address] [DecidableEq Provider] in
theorem registerIssued_preserves_validity (registry : Registry Address Provider)
    (selected : Handle Address Provider) (token : Nat)
    (valid : registry.Valid) (positiveOccurrence : selected.row.occurrence ≠ 0)
    (positiveToken : token ≠ 0)
    (freshOccurrence : selected.row.occurrence ∉ registry.rows.map Row.occurrence)
    (freshToken : token ∉ registry.rows.map Row.token) :
    (registerIssued registry selected token).1.Valid := by
  refine ⟨valid.1, ?_, ?_, ?_⟩
  · simpa only [registerIssued, List.map_append, List.map_cons, List.map_nil,
      List.concat_eq_append] using
      (List.Nodup.concat freshOccurrence valid.2.1)
  · simpa only [registerIssued, List.map_append, List.map_cons, List.map_nil,
      List.concat_eq_append] using
      (List.Nodup.concat freshToken valid.2.2.1)
  · intro row member
    simp only [registerIssued, List.mem_append, List.mem_singleton] at member
    rcases member with before | added
    · exact valid.2.2.2 row before
    · subst row
      exact ⟨positiveOccurrence, positiveToken⟩

namespace IssueEditControls

def selected : Handle Nat Nat := ⟨0, 7, ⟨10, 0, 0, 5⟩⟩

theorem last_token_is_issued_and_looked_up :
    reserveInclusive 255 255 = (some 255, 0) ∧
      lookup (registerIssued EditControls.source selected 255).1
        (registerIssued EditControls.source selected 255).2 = (some 3, 4) ∧
      (registerIssued EditControls.source selected 255).2.parent = 7 := by decide

theorem equal_payloads_do_not_erase_the_new_occurrence :
    (registerIssued EditControls.source selected 44).1.rows.map Row.payload = [0, 0, 0, 0] ∧
      (registerIssued EditControls.source selected 44).1.rows.map Row.occurrence = [7, 8, 9, 10] :=
    by decide

end IssueEditControls

/-- Logical key checks for requeue admission; addresses and provider identities
are not occurrence keys. The charged scan stops at the first duplicate. -/
def missingOccurrenceBits (occurrence : Nat) (queue : List (Handle Address Provider)) : List Bool :=
  queue.map (fun handle => handle.row.occurrence != occurrence)

omit [DecidableEq Address] [DecidableEq Provider] in
theorem missingOccurrenceBits_complete (occurrence : Nat)
    (queue : List (Handle Address Provider)) :
    scanAll (missingOccurrenceBits occurrence queue) = true ↔
      occurrence ∉ queue.map (fun handle => handle.row.occurrence) := by
  rw [scanAll_eq_true_iff]
  simp [missingOccurrenceBits, List.mem_map]

omit [DecidableEq Address] [DecidableEq Provider] in
theorem missingOccurrenceBits_full_cost (occurrence : Nat)
    (queue : List (Handle Address Provider))
    (fresh : occurrence ∉ queue.map (fun handle => handle.row.occurrence)) :
    scanAllCost (missingOccurrenceBits occurrence queue) = queue.length := by
  have all := (scanAll_eq_true_iff _).mp ((missingOccurrenceBits_complete occurrence queue).mpr fresh)
  simpa [missingOccurrenceBits] using scanAllCost_eq_length _ all

/-- The committed store edit after lookup, duplicate refusal, and successful
buffer reservation. The complete queue is retained; returned authority is
cleared. Allocation and layout effects precede this edit and are separate. -/
def commitRequeue (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) : Option (Registry Address Provider × List (Handle Address Provider)) := do
  let pair ← extractByLast index registry.rows
  some ({ registry with rows := pair.2 },
    queue ++ [{ handle with store := 0, row.token := 0 }])

theorem commitRequeue_correspondence (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) (accepted : (lookup registry handle).1 = some index) :
    commitRequeue registry queue handle index =
      (releaseIssued registry handle).1.map (fun pair => (pair.1, queue ++ [pair.2])) := by
  simp only [commitRequeue, releaseIssued, accepted, bind, Option.bind_some]
  cases extractByLast index registry.rows with
  | none => rfl
  | some pair => rfl

theorem commitRequeue_retains_frontier (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) (accepted : (lookup registry handle).1 = some index) :
    ∃ remaining,
      commitRequeue registry queue handle index =
        some ({ registry with rows := remaining },
          queue ++ [{ handle with store := 0, row.token := 0 }]) ∧
      (handle.row :: remaining).Perm registry.rows ∧
      (queue ++ [{ handle with store := 0, row.token := 0 }]).map
        (fun item : Handle Address Provider => item.row.occurrence) =
          queue.map (fun item : Handle Address Provider => item.row.occurrence) ++ [handle.row.occurrence] := by
  obtain ⟨remaining, exactRelease, retained⟩ := releaseIssued_selected registry handle index accepted
  refine ⟨remaining, ?_, retained, ?_⟩
  · rw [commitRequeue_correspondence registry queue handle index accepted, exactRelease]
    rfl
  · simp

omit [DecidableEq Address] [DecidableEq Provider] in
/-- Every previously issued row keeps its authority when a fresh row is
appended. This does not validate the lifetime of its external owner. -/
theorem registerIssued_keeps_other (registry : Registry Address Provider)
    (selected survivor : Handle Address Provider) (token : Nat)
    (authorized : Authenticated registry survivor) :
    Authenticated (registerIssued registry selected token).1 survivor := by
  rcases authorized with ⟨positiveStore, sameStore, positiveToken, present⟩
  exact ⟨positiveStore, sameStore, positiveToken, List.mem_append_left _ present⟩

/-- Extract the committed edit's exact release. No second lookup or issue is
performed by the edit, so the prior scanned prefix is its only lookup charge. -/
theorem commitRequeue_release (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) (accepted : (lookup registry handle).1 = some index)
    (next : Registry Address Provider) (pending : List (Handle Address Provider))
    (committed : commitRequeue registry queue handle index = some (next, pending)) :
    releaseIssued registry handle =
      (some (next, { handle with store := 0, row.token := 0 }), index + 1) ∧
      pending = queue ++ [{ handle with store := 0, row.token := 0 }] := by
  obtain ⟨remaining, edit, _⟩ := commitRequeue_retains_frontier registry queue handle index accepted
  rw [edit] at committed
  have equality := Option.some.inj committed
  have sameRegistry := congrArg Prod.fst equality
  have sameQueue := congrArg Prod.snd equality
  dsimp only at sameRegistry sameQueue
  constructor
  · obtain ⟨remaining', release, _⟩ := releaseIssued_selected registry handle index accepted
    rw [commitRequeue_correspondence registry queue handle index accepted, release] at edit
    have equality' := Option.some.inj edit
    have remainingSame := congrArg (fun pair => pair.1.rows) equality'
    dsimp only at remainingSame
    rw [release, remainingSame, sameRegistry]
  · exact sameQueue.symm

theorem commitRequeue_valid_and_revoked (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) (accepted : (lookup registry handle).1 = some index)
    (next : Registry Address Provider) (pending : List (Handle Address Provider))
    (valid : registry.Valid)
    (committed : commitRequeue registry queue handle index = some (next, pending)) :
    next.Valid ∧ ¬ Authenticated next handle := by
  have release := (commitRequeue_release registry queue handle index accepted next pending committed).1
  exact ⟨releaseIssued_preserves_validity registry handle next _ _ valid release,
    (releaseIssued_revokes_old_and_cleared registry handle next _ _ valid release).1⟩

/-- Conservation as a bag of production fields, including shared payloads.
Registry slot order and authority remain separate observable components. -/
theorem commitRequeue_keyed_values {Value : Type}
    (reading : Nat → Address → Provider → Value)
    (registry : Registry Address Provider) (queue : List (Handle Address Provider))
    (handle : Handle Address Provider) (index : Nat)
    (accepted : (lookup registry handle).1 = some index)
    (next : Registry Address Provider) (pending : List (Handle Address Provider))
    (committed : commitRequeue registry queue handle index = some (next, pending)) :
    ((pending.map (fun item => reading item.row.occurrence item.row.payload item.row.provider)) ++
      next.rows.map (fun row => reading row.occurrence row.payload row.provider)).Perm
      ((queue.map (fun item => reading item.row.occurrence item.row.payload item.row.provider)) ++
        registry.rows.map (fun row => reading row.occurrence row.payload row.provider)) := by
  obtain ⟨remaining, edit, retained, _⟩ := commitRequeue_retains_frontier registry queue handle index accepted
  rw [edit] at committed
  have equality := Option.some.inj committed
  have sameRegistry := congrArg Prod.fst equality
  have sameQueue := congrArg Prod.snd equality
  dsimp only at sameRegistry sameQueue
  rw [← sameRegistry, ← sameQueue]
  simpa only [List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.singleton_append] using
    ((retained.map (fun row => reading row.occurrence row.payload row.provider)).append_left
      (queue.map (fun item => reading item.row.occurrence item.row.payload item.row.provider)))

namespace RequeueEditControls

def queued : List (Handle Nat Nat) := [IssueEditControls.selected]

theorem requeue_retains_order_payload_alias_and_parent :
    commitRequeue EditControls.source queued Controls.first 0 =
      some (EditControls.afterRelease,
        [IssueEditControls.selected, { Controls.first with store := 0, row.token := 0 }]) ∧
      (Controls.first.parent, Controls.first.row.payload) = (6, 0) := by decide

theorem duplicate_occurrence_is_refused_despite_different_payload :
    Mettapedia.Machines.Cursor.TailSummary.scanAll
      (missingOccurrenceBits 7
        [{ Controls.first with store := 0, row.token := 0, row.payload := 100 }]) = false ∧
      Mettapedia.Machines.Cursor.TailSummary.scanAllCost
        (missingOccurrenceBits 7
          [IssueEditControls.selected,
            { Controls.first with store := 0, row.token := 0, row.payload := 100 },
            Controls.second]) = 2 := by decide

end RequeueEditControls

/-- Read-only requeue preflight: authenticate before checking queued keys.
Its receipt contains exactly the rows visited by those two scans. Buffer
reservation and the committed edit are different operations. -/
def preflightRequeue (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider) : Option Nat × Nat :=
  let found := lookup registry handle
  match found.1 with
  | none => (none, found.2)
  | some index =>
      let bits := missingOccurrenceBits handle.row.occurrence queue
      (if scanAll bits then some index else none, found.2 + scanAllCost bits)

theorem preflightRequeue_refused_authority (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (refused : (lookup registry handle).1 = none) :
    preflightRequeue registry queue handle = (none, (lookup registry handle).2) := by
  simp only [preflightRequeue, refused]

theorem preflightRequeue_exact (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) (accepted : (lookup registry handle).1 = some index)
    (fresh : handle.row.occurrence ∉ queue.map (fun item => item.row.occurrence)) :
    preflightRequeue registry queue handle = (some index, index + 1 + queue.length) := by
  have scan := (missingOccurrenceBits_complete handle.row.occurrence queue).mpr fresh
  have cost := missingOccurrenceBits_full_cost handle.row.occurrence queue fresh
  have visited := (lookup_selected registry handle index accepted).2
  simp only [preflightRequeue, accepted, scan, if_true, cost, visited]

theorem preflightRequeue_success_iff (registry : Registry Address Provider)
    (queue : List (Handle Address Provider)) (handle : Handle Address Provider)
    (index : Nat) :
    (preflightRequeue registry queue handle).1 = some index ↔
      (lookup registry handle).1 = some index ∧
        handle.row.occurrence ∉ queue.map (fun item => item.row.occurrence) := by
  unfold preflightRequeue
  cases selected : (lookup registry handle).1 with
  | none => simp [selected]
  | some found =>
      by_cases allowed : scanAll (missingOccurrenceBits handle.row.occurrence queue) = true
      · have fresh := (missingOccurrenceBits_complete handle.row.occurrence queue).mp allowed
        simp [selected, allowed, fresh]
      · have duplicate : ¬ handle.row.occurrence ∉ queue.map (fun item => item.row.occurrence) := by
          intro fresh
          exact allowed ((missingOccurrenceBits_complete handle.row.occurrence queue).mpr fresh)
        constructor
        · intro impossible
          simp [selected, allowed] at impossible
        · rintro ⟨_, fresh⟩
          exact (duplicate fresh).elim

/-- Relocating addresses and the store authority preserves both scan phases.
The queue's occurrence keys and their order remain the same. -/
theorem preflightRequeue_relocate {B : Type} [DecidableEq B]
    (address : Address → B) (injective : Function.Injective address)
    (registry : Registry Address Provider) (queue : List (Handle Address Provider))
    (handle : Handle Address Provider) (fresh : Nat)
    (owned : handle.store = registry.identity)
    (sourceLive : registry.identity ≠ 0) (destinationLive : fresh ≠ 0) :
    preflightRequeue (registry.relocate fresh address)
      (queue.map (Handle.relocate 0 address)) (handle.relocate fresh address) =
        preflightRequeue registry queue handle := by
  unfold preflightRequeue
  rw [lookup_relocate address injective registry handle fresh owned sourceLive destinationLive]
  have bits : missingOccurrenceBits (handle.relocate fresh address).row.occurrence
      (queue.map (Handle.relocate 0 address)) =
        missingOccurrenceBits handle.row.occurrence queue := by
    simp [missingOccurrenceBits, List.map_map, Handle.relocate, Row.map]
  simp only [bits]

namespace PreflightControls

theorem duplicate_refusal_retains_both_scan_prefixes :
    preflightRequeue EditControls.source
      [IssueEditControls.selected, Controls.first, Controls.second] Controls.first = (none, 3) ∧
      preflightRequeue EditControls.source [Controls.first]
        { Controls.first with store := 999 } = (none, 0) := by decide

theorem shared_payload_does_not_refuse_requeue :
    preflightRequeue EditControls.source [IssueEditControls.selected] Controls.first = (some 0, 2) :=
    by decide

end PreflightControls

/-- Every retained token precedes the next token; zero is an exhausted
frontier and cannot be used for a further issue. -/
def Registry.TokensBefore (registry : Registry Address Provider) (next : Nat) : Prop :=
  next = 0 ∨ ∀ row ∈ registry.rows, row.token < next

omit [DecidableEq Address] [DecidableEq Provider] in
theorem issued_token_is_fresh (registry : Registry Address Provider)
    (maximum current issued after : Nat)
    (before : registry.TokensBefore current)
    (reserved : reserveInclusive maximum current = (some issued, after)) :
    issued ≠ 0 ∧ issued ∉ registry.rows.map Row.token := by
  obtain ⟨positive, _, same, _⟩ := (reserveInclusive_issued_iff _ _ _ _).mp reserved
  have rows := before.resolve_left (by omega)
  refine ⟨by omega, ?_⟩
  intro present
  obtain ⟨row, member, equality⟩ := List.mem_map.mp present
  have below := rows row member
  omega

omit [DecidableEq Address] [DecidableEq Provider] in
theorem registerIssued_preserves_token_frontier (registry : Registry Address Provider)
    (selected : Handle Address Provider) (maximum current issued after : Nat)
    (before : registry.TokensBefore current)
    (reserved : reserveInclusive maximum current = (some issued, after)) :
    (registerIssued registry selected issued).1.TokensBefore after := by
  obtain ⟨positive, _, same, next⟩ := (reserveInclusive_issued_iff _ _ _ _).mp reserved
  have rows := before.resolve_left (by omega)
  by_cases final : current = maximum
  · left
    simpa only [final, if_true] using next
  · right
    intro row present
    simp only [registerIssued, List.mem_append, List.mem_singleton] at present
    rcases present with old | new
    · have below := rows row old
      simp only [final, if_false] at next
      omega
    · subst row
      simp only [final, if_false] at next
      dsimp only
      omega

omit [DecidableEq Address] [DecidableEq Provider] in
theorem registerIssued_valid_after_reservation (registry : Registry Address Provider)
    (selected : Handle Address Provider) (maximum current issued after : Nat)
    (valid : registry.Valid) (before : registry.TokensBefore current)
    (positiveOccurrence : selected.row.occurrence ≠ 0)
    (freshOccurrence : selected.row.occurrence ∉ registry.rows.map Row.occurrence)
    (reserved : reserveInclusive maximum current = (some issued, after)) :
    (registerIssued registry selected issued).1.Valid ∧
      (registerIssued registry selected issued).1.TokensBefore after := by
  have fresh := issued_token_is_fresh registry maximum current issued after before reserved
  exact ⟨registerIssued_preserves_validity registry selected issued valid positiveOccurrence
      fresh.1 freshOccurrence fresh.2,
    registerIssued_preserves_token_frontier registry selected maximum current issued after before reserved⟩

namespace TokenFrontierControls

theorem final_issue_keeps_namespace_valid :
    EditControls.source.TokensBefore 255 ∧
      (registerIssued EditControls.source IssueEditControls.selected 255).1.TokensBefore 0 ∧
      (registerIssued EditControls.source IssueEditControls.selected 255).1.Valid := by
  unfold Registry.TokensBefore Registry.Valid
  decide

theorem resetting_frontier_would_reissue_an_old_token :
    reserveInclusive 255 41 = (some 41, 42) ∧
      ¬ EditControls.source.TokensBefore 41 ∧
      ¬ (registerIssued EditControls.source IssueEditControls.selected 41).1.Valid := by
  unfold Registry.TokensBefore Registry.Valid
  decide

end TokenFrontierControls

end IssuedReturn

namespace Examples

open ResourceOwnership.Examples

def cursorSession : Session Nat (Fin 3) Nat Nat :=
  ⟨cyclicHeap, {(0, 0)}, 7⟩

def copiedCursorSession : Session Nat (Fin 4) Nat Nat :=
  relocateSession cursorSession copiedHeap shiftedCopy

def capturedPaths : List (Fin 3 × List (Fin 3)) :=
  [(0, [1, 2]), (0, [1, 2]), (0, [2])]

/-- The capture keeps two successful reads of a shared cyclic descendant
and one failed edge test. Retiring its source owner preserves all three. -/
theorem copied_paths_survive_retirement :
    RequestBorrow.observe (commit copiedCursorSession {0} 7 [1, 1, 1]).heap
      (RequestBorrow.relocatePaths relocationAddress capturedPaths) =
      [some (3, copiedCell 3), some (3, copiedCell 3), none] := by
  have copied := relocate_commit_paths cursorSession copiedHeap shiftedCopy {0} 7
    capturedPaths (by decide) (by intro query _; exact Finset.mem_univ query.1)
  exact copied

/-- The checked view is published to the output lifetime before the cursor
owner retires. Its three occurrences agree with the independent readout. -/
theorem checked_cursor_borrow_survives_retirement :
    (RequestBorrow.transport ⟨⟨0, 3⟩, cursorSession.heap⟩
      ⟨⟨7, 3⟩, copiedHeap⟩ shiftedCopy ⟨⟨0, 3⟩, capturedPaths⟩).bind
      (RequestBorrow.read ⟨⟨7, 3⟩, (commit copiedCursorSession {0} 7 [1, 1, 1]).heap⟩) =
      some [some (3, copiedCell 3), some (3, copiedCell 3), none] := by
  calc
    _ = (RequestBorrow.read ⟨⟨0, 3⟩, cursorSession.heap⟩
        (⟨⟨0, 3⟩, capturedPaths⟩ : RequestBorrow.View Nat (Fin 3))).map
        (List.map (Option.map fun pair =>
          (shiftedCopy.address pair.1,
            pair.2.relocate shiftedCopy.address shiftedCopy.payload))) :=
      relocate_commit_checked_borrow cursorSession copiedHeap shiftedCopy {0} 7 3
        ⟨0, 3⟩ ⟨⟨0, 3⟩, capturedPaths⟩ (by decide)
        (by intro query _; exact Finset.mem_univ query.1)
    _ = _ := by decide

/-- Publishing every path cannot convert an obsolete source generation
into an authorized borrow. The checker refuses before a destination read. -/
theorem checked_cursor_stale_borrow_refused :
    (RequestBorrow.transport ⟨⟨0, 4⟩, cursorSession.heap⟩
      ⟨⟨7, 3⟩, copiedHeap⟩ shiftedCopy ⟨⟨0, 3⟩, capturedPaths⟩).bind
      (RequestBorrow.read ⟨⟨7, 3⟩, (commit copiedCursorSession {0} 7 [1, 1, 1]).heap⟩) =
      none := by
  have different : (⟨0, 3⟩ : RequestBorrow.Stamp Nat) ≠ ⟨0, 4⟩ := by decide
  simp only [RequestBorrow.transport, RequestBorrow.View.transportIfCurrent, if_neg different, Option.bind_none]

/-- Retiring the output owner erases both successful observations, despite
the copied cells having existed before collection. -/
theorem retired_capture_owner_loses_paths :
    RequestBorrow.observe (commit copiedCursorSession {0} 0 [1, 1, 1]).heap
      (RequestBorrow.relocatePaths relocationAddress capturedPaths) = [none, none, none] := by
  have cleared : commitRoots copiedCursorSession.roots {0} 0 [1, 1, 1] = ∅ := by decide
  change RequestBorrow.observe (collect copiedHeap _) _ = _
  rw [cleared]
  have absent : (collect copiedHeap (∅ : Roots Nat (Fin 4))).lookup
      (relocationAddress 0) = none :=
    lookup_collect_of_not_live copiedHeap _ (not_live_empty copiedHeap 1)
  simp only [RequestBorrow.observe, RequestBorrow.relocatePaths, capturedPaths,
    List.map_cons, List.map_nil, walk, absent, Option.bind_none]

/-- Publishing the outer copied node cannot repair missing reference
relocation: the same endpoint payloads no longer provide the same paths. -/
theorem copied_outer_pointer_does_not_certify_capture :
    RequestBorrow.observe unrelocatedReferencesHeap
      (RequestBorrow.relocatePaths relocationAddress capturedPaths) = [none, none, none] ∧
    RequestBorrow.observe copiedHeap
      (RequestBorrow.relocatePaths relocationAddress capturedPaths) =
      [some (3, copiedCell 3), some (3, copiedCell 3), none] := by decide

/-- Two answer occurrences share one copied cyclic graph. Retiring the
cursor retains that graph once, while destination observations keep both
occurrences and the original semantic world. -/
theorem copied_duplicate_answers_survive :
    observe (commit copiedCursorSession {0} 1 [2, 2]).heap [2, 2] =
      [some (copiedCell 2), some (copiedCell 2)] ∧
    allocatedBytes (commit copiedCursorSession {0} 1 [2, 2]).heap = 32 ∧
      (commit copiedCursorSession {0} 1 [2, 2]).world = 7 := by
  constructor
  · exact duplicate_answer_observation copiedCursorSession {0} 1 2 (by decide) (by decide)
  · constructor
    · change allocatedBytes (collect copiedHeap
        (commitRoots copiedCursorSession.roots {0} 1 [2, 2])) = 32
      have rootsExact : commitRoots copiedCursorSession.roots {0} 1 [2, 2] =
          ({(1, 2)} : Roots Nat (Fin 4)) := by decide
      have valid : ValidRoots copiedHeap ({(1, 2)} : Roots Nat (Fin 4)) := by
        intro pair member
        have same := Finset.mem_singleton.mp member
        subst pair
        decide
      rw [rootsExact, allocatedBytes_collect, ← censusBytes_eq_retainedBytes copiedHeap _ valid]
      decide
    · rfl

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
