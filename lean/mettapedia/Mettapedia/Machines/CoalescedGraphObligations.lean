import Mettapedia.Machines.ResourceOwnership
import Mathlib.Tactic

/-!
# Obligations surviving coalesced foreign graph publications

An observer can miss an imported cyclic component when a parent publishes it
and then overwrites that image before the next observation. The latest rooted
graph is small, although the uncollected heap contains all dropped components.

This executable model separates three mechanisms: finite ownership reachability,
pre-publication settled coverage, and a persistent uncovered-publication clock.
The executable finite census is compared with independent inductive reachability
through `ResourceOwnership`; target collection is not defined as the reference.

Each child vertex abstracts one independently owned cyclic component. Its
self-edge is an owning cycle, and its byte weight includes that component's
node/image storage. The parent's immutable current-image path is contracted to
one outgoing edge. Proving this contraction and complete native leaf summaries,
C synchronization, allocation admission, and physical allocator retention are
separate correspondence obligations. No universal RSS bound is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CoalescedGraphObligations

open ResourceOwnership

/-! ## Executable ownership graph and a distinct tracing implementation -/

structure World where
  children : Finset Nat
  current : Option Nat
  current_present : ∀ child, current = some child → child ∈ children

def emptyWorld : World := ⟨∅, none, by simp⟩

def importChild (world : World) (child : Nat) : World :=
  ⟨insert child world.children, some child, by simp⟩

def overwriteScalar (world : World) : World :=
  ⟨world.children, none, by simp⟩

/-- One bounded call imports a cyclic component and drops the parent edge
before returning. Strong-count retirement alone leaves its self-cycle. -/
def foreignCall (world : World) (child : Nat) : World :=
  overwriteScalar (importChild world child)

def foreignCalls : Nat → World
  | 0 => emptyWorld
  | n + 1 => foreignCall (foreignCalls n) n

@[simp] theorem foreignCalls_children (n : Nat) :
    (foreignCalls n).children = Finset.range n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [foreignCalls, foreignCall, overwriteScalar, importChild, ih]
      using (Finset.range_add_one (n := n)).symm

@[simp] theorem foreignCalls_current (n : Nat) :
    (foreignCalls n).current = none := by
  cases n <;> rfl

/-- Address 0 is the parent. Component `child` has address `child + 1`. -/
def parentCell (world : World) (parentBytes : Nat) : Cell Nat Nat :=
  ⟨0, (world.current.toList.map Nat.succ).toFinset, parentBytes⟩

def childCell (child childBytes : Nat) : Cell Nat Nat :=
  ⟨child + 1, {child + 1}, childBytes⟩

def worldHeap (world : World) (parentBytes childBytes : Nat) : Heap Nat Nat where
  lookup
    | 0 => some (parentCell world parentBytes)
    | child + 1 => if child ∈ world.children then some (childCell child childBytes) else none
  allocated := insert 0 (world.children.image Nat.succ)
  allocated_iff := by
    intro address
    cases address with
    | zero => simp
    | succ child => simp
  closed := by
    intro address cell found target edge
    cases address with
    | zero =>
      cases found
      simp only [parentCell] at edge
      cases current : world.current with
      | none => simp [current] at edge
      | some child =>
        simp [current] at edge
        subst target
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨child, world.current_present child current, rfl⟩)
    | succ child =>
      change (if child ∈ world.children then some (childCell child childBytes) else none) =
        some cell at found
      by_cases member : child ∈ world.children
      · rw [if_pos member] at found
        cases found
        change target ∈ ({child + 1} : Finset Nat) at edge
        rw [Finset.mem_singleton] at edge
        subst target
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨child, member, rfl⟩)
      · simp [member] at found

def parentRoots : Roots Unit Nat := {((), 0)}

theorem parentRoots_valid (world : World) (parentBytes childBytes : Nat) :
    ValidRoots (worldHeap world parentBytes childBytes) parentRoots := by
  simp [ValidRoots, parentRoots, worldHeap]

/-- The implementation computes finite closure and restricts actual lookup.
Its correctness is proved against the separately defined reachability collector. -/
def traceSweep {Address Value : Type} [DecidableEq Address]
    (heap : Heap Address Value) (roots : Roots Unit Address)
    (valid : ValidRoots heap roots) : Heap Address Value where
  lookup := fun address => if address ∈ census heap roots then heap.lookup address else none
  allocated := census heap roots
  allocated_iff := by
    intro address
    by_cases member : address ∈ census heap roots
    · simp only [member, if_pos, true_iff]
      exact (heap.allocated_iff address).mp
        (live_allocated heap roots ((mem_census_iff_live heap roots valid address).mp member))
    · simp [member]
  closed := by
    intro address cell found target edge
    split at found
    next member =>
      exact (mem_census_iff_live heap roots valid target).mpr
        (live_step heap roots
          ((mem_census_iff_live heap roots valid address).mp member) found edge)
    next _ => cases found

theorem traceSweep_lookup_eq_reference {Address Value : Type} [DecidableEq Address]
    (heap : Heap Address Value) (roots : Roots Unit Address)
    (valid : ValidRoots heap roots) (address : Address) :
    (traceSweep heap roots valid).lookup address = (collect heap roots).lookup address := by
  classical
  by_cases live : Live heap roots address
  · have member := (mem_census_iff_live heap roots valid address).mpr live
    simp [traceSweep, member, lookup_collect_of_live heap roots live]
  · have absent : address ∉ census heap roots :=
      fun member => live ((mem_census_iff_live heap roots valid address).mp member)
    simp [traceSweep, absent, lookup_collect_of_not_live heap roots live]

theorem traceSweep_walk_eq_reference {Address Value : Type} [DecidableEq Address]
    (heap : Heap Address Value) (roots : Roots Unit Address)
    (valid : ValidRoots heap roots) (address : Address) (path : List Address) :
    walk (traceSweep heap roots valid) address path = walk (collect heap roots) address path := by
  induction path generalizing address with
  | nil => simp [walk, traceSweep_lookup_eq_reference]
  | cons next rest ih => simp [walk, traceSweep_lookup_eq_reference, ih]

theorem traceSweep_preserves_live_observation {Address Value : Type} [DecidableEq Address]
    (heap : Heap Address Value) (roots : Roots Unit Address)
    (valid : ValidRoots heap roots) (address : Address) (path : List Address)
    (live : Live heap roots address) :
    walk (traceSweep heap roots valid) address path = walk heap address path := by
  rw [traceSweep_walk_eq_reference]
  exact walk_collect heap roots live path

theorem traceSweep_preserves_rooted_observation (world : World)
    (parentBytes childBytes : Nat) (path : List Nat) :
    walk (traceSweep (worldHeap world parentBytes childBytes) parentRoots
      (parentRoots_valid world parentBytes childBytes)) 0 path =
      walk (worldHeap world parentBytes childBytes) 0 path := by
  rw [traceSweep_walk_eq_reference]
  apply walk_collect
  exact live_of_root _ _ (owner := ()) (by simp [parentRoots]) (by simp [worldHeap])

theorem scalar_live_iff_parent (world : World) (scalar : world.current = none)
    (parentBytes childBytes address : Nat) :
    Live (worldHeap world parentBytes childBytes) parentRoots address ↔ address = 0 := by
  constructor
  · intro live
    induction live with
    | root root => simpa [rootAddresses, parentRoots] using root.2
    | @step source target _ edge ih =>
      obtain ⟨cell, found, member⟩ := edge
      subst source
      simp only [worldHeap, Option.some.injEq] at found
      subst cell
      simp [parentCell, scalar] at member
  · intro same
    subst address
    exact live_of_root _ _ (owner := ()) (by simp [parentRoots]) (by simp [worldHeap])

theorem scalar_census (world : World) (scalar : world.current = none)
    (parentBytes childBytes : Nat) :
    census (worldHeap world parentBytes childBytes) parentRoots = {0} := by
  ext address
  rw [mem_census_iff_live _ _ (parentRoots_valid world parentBytes childBytes),
    scalar_live_iff_parent world scalar]
  simp

theorem world_allocatedBytes (world : World) (parentBytes childBytes : Nat) :
    allocatedBytes (worldHeap world parentBytes childBytes) =
      parentBytes + world.children.card * childBytes := by
  have absent : 0 ∉ world.children.image Nat.succ := by simp
  simp only [allocatedBytes, worldHeap, Finset.sum_insert absent]
  rw [Finset.sum_image (by intro a _ b _ equal; omega)]
  simp only [cellBytes, parentCell, childCell, Option.map_some, Option.getD_some]
  congr 1
  calc
    _ = ∑ _child ∈ world.children, childBytes := by
      apply Finset.sum_congr rfl
      intro child member
      simp [member]
    _ = _ := by simp

theorem scalar_censusBytes (world : World) (scalar : world.current = none)
    (parentBytes childBytes : Nat) :
    censusBytes (worldHeap world parentBytes childBytes) parentRoots = parentBytes := by
  rw [censusBytes, scalar_census world scalar]
  simp [cellBytes, worldHeap, parentCell]

/-- Latest-root charge alone cannot detect the accumulated dropped cycles. -/
theorem transient_cycle_counterexample (bound parentBytes : Nat) :
    ∃ n, (foreignCalls n).current = none ∧
      censusBytes (worldHeap (foreignCalls n) parentBytes 1) parentRoots = parentBytes ∧
      bound < allocatedBytes (worldHeap (foreignCalls n) parentBytes 1) := by
  refine ⟨bound + 1, foreignCalls_current _,
    scalar_censusBytes _ (foreignCalls_current _) _ _, ?_⟩
  rw [world_allocatedBytes, foreignCalls_children]
  simp
  omega

theorem dropped_cycles_reclaimed (n parentBytes childBytes child : Nat) :
    (traceSweep (worldHeap (foreignCalls n) parentBytes childBytes) parentRoots
      (parentRoots_valid _ _ _)).lookup (child + 1) = none := by
  have census := scalar_census (foreignCalls n) (foreignCalls_current n) parentBytes childBytes
  simp [traceSweep, census]

/-! ## Pre-publication coverage, including the settled self-edge case -/

structure Watch where
  accepted : Bool
  queued : Bool
  inflight : Bool
  capturedVersion : Nat
  currentVersion : Nat
  saturated : Bool
  deriving DecidableEq, Repr

def Watch.covered (watch : Watch) : Bool :=
  watch.accepted && !watch.queued && !watch.inflight && !watch.saturated &&
    decide (watch.capturedVersion = watch.currentVersion)

structure Summary where
  complete : Bool
  mutableLeaves : List Nat
  deriving DecidableEq, Repr

def Summary.uncovered (summary : Summary) (watches : Nat → Watch) : Bool :=
  !summary.complete || summary.mutableLeaves.any (fun leaf => !(watches leaf).covered)

theorem empty_certified_summary_covered (watches : Nat → Watch) :
    Summary.uncovered ⟨true, []⟩ watches = false := by simp [Summary.uncovered]

theorem incomplete_summary_uncovered (leaves : List Nat) (watches : Nat → Watch) :
    Summary.uncovered ⟨false, leaves⟩ watches = true := by simp [Summary.uncovered]

def settledWatch (version : Nat) : Watch := ⟨true, false, false, version, version, false⟩

@[simp] theorem settledWatch_covered (version : Nat) : (settledWatch version).covered = true := by
  simp [settledWatch, Watch.covered]

/-- Membership created by ensure is queued; it is not discovered coverage. -/
example (version : Nat) :
    ({ settledWatch version with queued := true } : Watch).covered = false := by
  simp [Watch.covered]

example (version : Nat) :
    ({ settledWatch version with inflight := true } : Watch).covered = false := by
  simp [Watch.covered]

example (version : Nat) :
    ({ settledWatch version with accepted := false } : Watch).covered = false := by
  simp [Watch.covered]

example (version : Nat) :
    ({ settledWatch version with currentVersion := version + 1 } : Watch).covered = false := by
  simp [Watch.covered, settledWatch]

theorem covered_child_summary (leaf version : Nat) :
    Summary.uncovered ⟨true, [leaf]⟩ (fun _ => settledWatch version) = false := by
  simp [Summary.uncovered]

/-- Evaluating a self-leaf after incrementing its publication version would
spuriously lose coverage. Publication must test the settled OLD version. -/
theorem self_edge_requires_prepublication_coverage (parent version : Nat) :
    Summary.uncovered ⟨true, [parent]⟩ (fun _ => settledWatch version) = false ∧
    Summary.uncovered ⟨true, [parent]⟩
      (fun _ => { settledWatch version with currentVersion := version + 1 }) = true := by
  simp [Summary.uncovered, Watch.covered, settledWatch]

/-! ## Persistent obligation and successful-collection acknowledgement -/

structure Clock where
  noticeEpoch : Nat
  uncoveredEpoch : Nat
  acceptedUncovered : Nat
  rootEpoch : Nat
  discoveryEpoch : Nat
  deferredOffers : Nat
  saturated : Bool
  deriving DecidableEq, Repr

def initialClock : Clock := ⟨0, 0, 0, 0, 0, 0, false⟩

def Clock.due (clock : Clock) : Prop :=
  clock.saturated = true ∨ clock.acceptedUncovered < clock.uncoveredEpoch

def publish (clock : Clock) (uncovered : Bool) : Clock :=
  { clock with
    noticeEpoch := clock.noticeEpoch + 1
    uncoveredEpoch := clock.uncoveredEpoch + (if uncovered then 1 else 0) }

/-- Publication of a distinct prepared image. -/
def publishSummary (clock : Clock) (summary : Summary) (watches : Nat → Watch) : Clock :=
  publish clock (summary.uncovered watches)

/-- Re-publishing the very same immutable image creates no new import edge.
It still changes the ordinary publication epoch and preserves existing debt. -/
def publishImage (clock : Clock) (old replacement : Nat)
    (summary : Summary) (watches : Nat → Watch) : Clock :=
  publish clock (decide (old ≠ replacement) && summary.uncovered watches)

theorem distinct_image_uses_summary (clock : Clock) (old replacement : Nat)
    (different : old ≠ replacement) (summary : Summary) (watches : Nat → Watch) :
    publishImage clock old replacement summary watches = publishSummary clock summary watches := by
  simp [publishImage, publishSummary, different]

theorem same_image_preserves_obligation (clock : Clock) (image : Nat)
    (summary : Summary) (watches : Nat → Watch) :
    (publishImage clock image image summary watches).uncoveredEpoch = clock.uncoveredEpoch ∧
      (publishImage clock image image summary watches).acceptedUncovered = clock.acceptedUncovered ∧
      ((publishImage clock image image summary watches).due ↔ clock.due) := by
  simp [publishImage, publish, Clock.due]

def boundedCall (clock : Clock) : Clock := publish (publish clock true) false

def coalescedClock : Nat → Clock
  | 0 => initialClock
  | n + 1 => boundedCall (coalescedClock n)

@[simp] theorem coalescedClock_uncovered (n : Nat) :
    (coalescedClock n).uncoveredEpoch = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [coalescedClock, boundedCall, publish, ih]

@[simp] theorem coalescedClock_accepted (n : Nat) :
    (coalescedClock n).acceptedUncovered = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [coalescedClock, boundedCall, publish] using ih

@[simp] theorem coalescedClock_saturated (n : Nat) :
    (coalescedClock n).saturated = false := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [coalescedClock, boundedCall, publish] using ih

theorem coalescedClock_due (n : Nat) (positive : 0 < n) : (coalescedClock n).due := by
  exact Or.inr (by simpa using positive)

theorem overwrite_preserves_uncovered (clock : Clock) :
    (publish clock false).uncoveredEpoch = clock.uncoveredEpoch ∧
      (publish clock false).acceptedUncovered = clock.acceptedUncovered := by
  simp [publish]

inductive Maintenance where
  | censusFinished | deltaSettled | restore | deferred
  deriving DecidableEq, Repr

/-- These events make real scheduling/discovery changes. None is a successful
full native collection or has authority to clear an uncovered obligation. -/
def maintain (clock : Clock) : Maintenance → Clock
  | .censusFinished => { clock with discoveryEpoch := clock.discoveryEpoch + 1 }
  | .deltaSettled => { clock with discoveryEpoch := clock.discoveryEpoch + 1 }
  | .restore => { clock with rootEpoch := clock.rootEpoch + 1 }
  | .deferred => { clock with deferredOffers := clock.deferredOffers + 1 }

theorem maintenance_preserves_obligation (clock : Clock) (event : Maintenance) :
    (maintain clock event).uncoveredEpoch = clock.uncoveredEpoch ∧
      (maintain clock event).acceptedUncovered = clock.acceptedUncovered ∧
      ((maintain clock event).due ↔ clock.due) := by
  cases event <;> simp [maintain, Clock.due]

inductive Cleanup where
  | complete | deferred | refused
  deriving DecidableEq, Repr

structure Ticket where
  noticeEpoch : Nat
  uncoveredEpoch : Nat
  rootEpoch : Nat
  fullTrace : Bool
  deriving DecidableEq, Repr

def capture (clock : Clock) (fullTrace : Bool) : Ticket :=
  ⟨clock.noticeEpoch, clock.uncoveredEpoch, clock.rootEpoch, fullTrace⟩

def mayAcknowledge (clock : Clock) (ticket : Ticket) (cleanup : Cleanup) : Prop :=
  ticket.fullTrace = true ∧ cleanup = .complete ∧ clock.saturated = false ∧
    ticket.noticeEpoch = clock.noticeEpoch ∧ ticket.uncoveredEpoch = clock.uncoveredEpoch ∧
    ticket.rootEpoch = clock.rootEpoch

instance (clock : Clock) (ticket : Ticket) (cleanup : Cleanup) :
    Decidable (mayAcknowledge clock ticket cleanup) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def acknowledge (clock : Clock) (ticket : Ticket) (cleanup : Cleanup) : Clock :=
  if mayAcknowledge clock ticket cleanup then
    { clock with acceptedUncovered := clock.uncoveredEpoch }
  else clock

theorem acknowledgement_changed_only_after_complete (clock : Clock) (ticket : Ticket)
    (cleanup : Cleanup)
    (changed : (acknowledge clock ticket cleanup).acceptedUncovered ≠ clock.acceptedUncovered) :
    ticket.fullTrace = true ∧ cleanup = .complete ∧ clock.saturated = false ∧
      ticket.noticeEpoch = clock.noticeEpoch ∧ ticket.uncoveredEpoch = clock.uncoveredEpoch ∧
      ticket.rootEpoch = clock.rootEpoch := by
  unfold acknowledge at changed
  split_ifs at changed with permitted
  · exact permitted
  · exact False.elim (changed rfl)

@[simp] theorem deferred_preserves_clock (clock : Clock) (ticket : Ticket) :
    acknowledge clock ticket .deferred = clock := by
  simp [acknowledge, mayAcknowledge]

@[simp] theorem refused_preserves_clock (clock : Clock) (ticket : Ticket) :
    acknowledge clock ticket .refused = clock := by
  simp [acknowledge, mayAcknowledge]

/-- Full census finish, incremental settlement and continuation restoration
cannot supply the required committed full trace plus completed native cleanup. -/
theorem no_full_trace_preserves_clock (clock : Clock) (ticket : Ticket)
    (notCommitted : ticket.fullTrace = false) (cleanup : Cleanup) :
    acknowledge clock ticket cleanup = clock := by
  simp [acknowledge, mayAcknowledge, notCommitted]

theorem saturated_never_acknowledged (clock : Clock) (ticket : Ticket) (cleanup : Cleanup)
    (saturated : clock.saturated = true) : acknowledge clock ticket cleanup = clock := by
  simp [acknowledge, mayAcknowledge, saturated]

theorem publication_after_capture_refuses_ack (clock : Clock) (uncovered : Bool)
    (cleanup : Cleanup) :
    acknowledge (publish clock uncovered) (capture clock true) cleanup = publish clock uncovered := by
  simp [acknowledge, mayAcknowledge, capture, publish]

theorem same_image_still_invalidates_old_ticket (clock : Clock) (image : Nat)
    (summary : Summary) (watches : Nat → Watch) (cleanup : Cleanup) :
    acknowledge (publishImage clock image image summary watches) (capture clock true) cleanup =
      publishImage clock image image summary watches := by
  simpa [publishImage] using publication_after_capture_refuses_ack clock false cleanup

theorem restore_invalidates_old_trace (clock : Clock) (cleanup : Cleanup) :
    acknowledge (maintain clock .restore) (capture clock true) cleanup =
      maintain clock .restore := by
  simp [acknowledge, mayAcknowledge, capture, maintain]

theorem stable_complete_acknowledges (clock : Clock) (unsaturated : clock.saturated = false) :
    (acknowledge clock (capture clock true) .complete).acceptedUncovered = clock.uncoveredEpoch ∧
      ¬ (acknowledge clock (capture clock true) .complete).due := by
  simp [acknowledge, mayAcknowledge, capture, unsaturated, Clock.due]

theorem covered_publication_no_new_obligation (clock : Clock) (child version : Nat) :
    (publishSummary clock ⟨true, [child]⟩ (fun _ => settledWatch version)).uncoveredEpoch =
      clock.uncoveredEpoch := by
  unfold publishSummary
  rw [covered_child_summary]
  simp [publish]

/-- This narrow atomic target commits the actual finite sweep and its watermark
together. A native implementation must refine this ordering and stable-ticket
check; receiving a COMPLETE enum alone is not a proof of this refinement. -/
def finishCollection (world : World) (parentBytes childBytes : Nat)
    (clock : Clock) (ticket : Ticket) (cleanup : Cleanup) : Heap Nat Nat × Clock :=
  if mayAcknowledge clock ticket cleanup then
    (traceSweep (worldHeap world parentBytes childBytes) parentRoots
      (parentRoots_valid _ _ _), acknowledge clock ticket cleanup)
  else (worldHeap world parentBytes childBytes, clock)

theorem finishCollection_preserves_observations (world : World)
    (parentBytes childBytes : Nat) (clock : Clock) (ticket : Ticket)
    (cleanup : Cleanup) (path : List Nat) :
    walk (finishCollection world parentBytes childBytes clock ticket cleanup).1 0 path =
      walk (worldHeap world parentBytes childBytes) 0 path := by
  unfold finishCollection
  split_ifs
  · exact traceSweep_preserves_rooted_observation _ _ _ _
  · rfl

theorem acknowledged_cycles_actually_removed (n parentBytes childBytes child : Nat)
    (clock : Clock) (ticket : Ticket) (cleanup : Cleanup)
    (changed : Clock.acceptedUncovered
      (finishCollection (foreignCalls n) parentBytes childBytes clock ticket cleanup).2 ≠
        clock.acceptedUncovered) :
    (finishCollection (foreignCalls n) parentBytes childBytes clock ticket cleanup).1.lookup
      (child + 1) = none := by
  unfold finishCollection at changed ⊢
  split_ifs with permitted
  · exact dropped_cycles_reclaimed _ _ _ _
  · simp [permitted] at changed

/-! ## Concrete positive and negative observations -/

def coveredWorld : World := importChild emptyWorld 7

example : walk (worldHeap coveredWorld 256 2097152) 0 [8, 8] =
    some (8, childCell 7 2097152) := by decide

/-- A retained cyclic child remains observable after the actual finite trace. -/
example : walk (traceSweep (worldHeap coveredWorld 256 2097152) parentRoots
    (parentRoots_valid _ _ _)) 0 [8, 8] = some (8, childCell 7 2097152) := by
  rw [traceSweep_preserves_rooted_observation]
  decide

/-- An independent retained reader prevents collection of the dropped cycle;
the finite path observes the same child and its owning self-edge. -/
example :
    let heap := worldHeap (foreignCalls 1) 256 2097152
    let roots : Roots Unit Nat := {((), 0), ((), 1)}
    walk (traceSweep heap roots (by
      simp [ValidRoots, heap, roots, worldHeap, foreignCalls_children])) 1 [1] =
      some (1, childCell 0 2097152) := by
  decide

/-- The coalesced latest image is tiny while 64 dropped 2 MiB cycles remain. -/
example : allocatedBytes (worldHeap (foreignCalls 64) 256 2097152) = 134217984 ∧
    censusBytes (worldHeap (foreignCalls 64) 256 2097152) parentRoots = 256 ∧
    (coalescedClock 64).uncoveredEpoch = 64 ∧ (coalescedClock 64).due := by
  simp only [world_allocatedBytes, foreignCalls_children, Finset.card_range,
    scalar_censusBytes _ (foreignCalls_current _), coalescedClock_uncovered]
  exact ⟨by decide, trivial, trivial, coalescedClock_due 64 (by decide)⟩

example : (acknowledge (coalescedClock 64) (capture (coalescedClock 64) true)
    .deferred).due := by
  rw [deferred_preserves_clock]
  exact coalescedClock_due 64 (by decide)

example : acknowledge (publish initialClock true) (capture initialClock true) .complete =
    publish initialClock true := publication_after_capture_refuses_ack _ _ _

/-- A census-only watermark reset loses the outstanding obligation without
removing any dropped cycle. This is a deliberately wrong consumer. -/
def forgetAtCensus (clock : Clock) : Clock :=
  { maintain clock .censusFinished with acceptedUncovered := clock.uncoveredEpoch }

example : ¬ (forgetAtCensus (coalescedClock 64)).due ∧
    allocatedBytes (worldHeap (foreignCalls 64) 256 2097152) > 134217728 := by
  constructor
  · simp [forgetAtCensus, maintain, Clock.due]
  · rw [world_allocatedBytes, foreignCalls_children, Finset.card_range]
    decide

example (clock : Clock) (watches : Nat → Watch) :
    (publishSummary clock ⟨false, []⟩ watches).uncoveredEpoch = clock.uncoveredEpoch + 1 := by
  simp [publishSummary, publish, Summary.uncovered]

/-- Multiple uncovered leaves produce one obligation increment per publication,
not one increment per edge or one increment only while previously clean. -/
example (clock : Clock) :
    (publishSummary clock ⟨true, [3, 5, 3]⟩
      (fun _ => { settledWatch 0 with queued := true })).uncoveredEpoch =
        clock.uncoveredEpoch + 1 := by
  simp [publishSummary, Summary.uncovered, Watch.covered, publish]

#print axioms traceSweep_lookup_eq_reference
#print axioms traceSweep_preserves_rooted_observation
#print axioms transient_cycle_counterexample
#print axioms acknowledgement_changed_only_after_complete
#print axioms publication_after_capture_refuses_ack
#print axioms stable_complete_acknowledges
#print axioms maintenance_preserves_obligation
#print axioms restore_invalidates_old_trace
#print axioms finishCollection_preserves_observations
#print axioms acknowledged_cycles_actually_removed
#print axioms same_image_preserves_obligation
#print axioms same_image_still_invalidates_old_ticket

end Mettapedia.Machines.CoalescedGraphObligations
