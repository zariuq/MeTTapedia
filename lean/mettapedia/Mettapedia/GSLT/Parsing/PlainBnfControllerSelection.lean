import Mettapedia.GSLT.Parsing.PlainBnfRunIndexedInputs

/-!
# Selection and progress of the authored discovery controller

The existing heap, finite frontier, and ordered-scan observations are connected
at a controller boundary. Coordinates are constrained on live heap contents;
there is no rank decoder with a default for malformed values. The selected
publication is enabled and strictly decreases the unpublished-definition
count. These are local progress laws, not a whole-run termination assertion.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerSelection

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Batteries.PairingHeapImp (Heap)
open PlainBnfSourceRank (Rank value)
open PlainBnfHeapSourceExecution (itemLE)
open PlainBnfWakeSourceExecution (HeapItem Queues Ordered WellPlaced pending)
open PlainBnfOrderedGraphDiscovery (Grammar Known Event ready nextEvent)
open PlainBnfStructuredDiscoveryGraph
open PlainBnfReferenceCollectionSourceExecution (text)

variable {size : Nat}

theorem live_order (coordinate : HeapItem → Fin size) (heap : Heap HeapItem)
    (ranks : ∀ item ∈ PlainBnfPairingHeapObservation.contents heap,
      (coordinate item).val = value item.1) :
    ∀ a ∈ PlainBnfPairingHeapObservation.contents heap,
      ∀ b ∈ PlainBnfPairingHeapObservation.contents heap,
      itemLE a b = true → coordinate a ≤ coordinate b := by
  intro a ha b hb before
  change (coordinate a).val ≤ (coordinate b).val
  rw [ranks a ha, ranks b hb]
  exact (PlainBnfSourceRank.rankLE_iff a.1 b.1).mp before

/-- Current-round work takes priority over the entire following-round heap,
even if that second heap contains a numerically smaller source position. -/
theorem selection_eq_nextEvent (coordinate : HeapItem → Fin size)
    (grammar : Grammar size) (known : Known size) (round : Nat)
    (origin : Option Rank) (queues : Queues) (ordered : Ordered queues)
    (placed : WellPlaced coordinate origin queues)
    (frontier : pending coordinate queues = PlainBnfDependencyWorklist.initialQueue grammar known)
    (ranks : ∀ item ∈ PlainBnfWakeSourceExecution.contents queues,
      (coordinate item).val = value item.1) :
    (match queues.1.head?.map coordinate with
      | some p => some (⟨round, p⟩ : Event size)
      | none => (queues.2.1.head?.map coordinate).map fun p => ⟨round + 1, p⟩) =
      nextEvent grammar known round (PlainBnfScheduleWorklistBridge.cursor origin) := by
  apply PlainBnfTwoHeapWorklist.select_eq_nextEvent coordinate itemLE
    (fun first second => PlainBnfSourceRank.rankLE_trans first second)
    queues.1 queues.2.1 ordered.1 ordered.2
  · apply live_order coordinate queues.1
    intro item member
    exact ranks item (Multiset.mem_add.mpr (Or.inl member))
  · apply live_order coordinate queues.2.1
    intro item member
    exact ranks item (Multiset.mem_add.mpr (Or.inr member))
  · simpa only [WellPlaced, frontier] using placed

theorem nextEvent_ready (grammar : Grammar size) (known : Known size)
    (round cursor : Nat) (event : Event size)
    (selected : nextEvent grammar known round cursor = some event) :
    ready grammar known event.position = true := by
  rw [← PlainBnfDependencyWorklist.select_eq_nextEvent] at selected
  exact (Finset.mem_filter.mp (PlainBnfDependencyWorklist.selected_mem_queue
    (PlainBnfDependencyWorklist.initialQueue grammar known) round cursor selected)).2

theorem nextEvent_unpublished (grammar : Grammar size) (known : Known size)
    (round cursor : Nat) (event : Event size)
    (selected : nextEvent grammar known round cursor = some event) :
    known event.position = false := by
  have enabled := nextEvent_ready grammar known round cursor event selected
  simp only [ready, Bool.and_eq_true] at enabled
  simpa using enabled.1

theorem current_selected (coordinate : HeapItem → Fin size)
    (grammar : Grammar size) (known : Known size) (round : Nat) (origin : Option Rank)
    (item : HeapItem) (children : Heap HeapItem) (following : Heap HeapItem)
    (scheduled : PlainBnfWakeContextualExecution.NameIndex)
    (ordered : Ordered (.node item children .nil, following, scheduled))
    (placed : WellPlaced coordinate origin (.node item children .nil, following, scheduled))
    (frontier : pending coordinate (.node item children .nil, following, scheduled) =
      PlainBnfDependencyWorklist.initialQueue grammar known)
    (ranks : ∀ payload ∈ PlainBnfWakeSourceExecution.contents
      (.node item children .nil, following, scheduled),
      (coordinate payload).val = value payload.1) :
    nextEvent grammar known round (PlainBnfScheduleWorklistBridge.cursor origin) =
      some ⟨round, coordinate item⟩ := by
  exact (selection_eq_nextEvent coordinate grammar known round origin
    (.node item children .nil, following, scheduled) ordered placed frontier ranks).symm

/-- A valid publication prepends the exact source name to the existing
history, and does not turn the history into a set. -/
theorem selected_history_progress (definitions : Definitions)
    (unique : (names definitions).Nodup) (grammar : Grammar definitions.length)
    (history : List SExpr) (historyScoped : HistoryScoped definitions history)
    (noRepeats : history.Nodup) (round cursor : Nat) (event : Event definitions.length)
    (selected : nextEvent grammar (graphKnown definitions history) round cursor = some event) :
    HistoryScoped definitions (text (nameAt definitions event.position) :: history) ∧
    (text (nameAt definitions event.position) :: history).Nodup ∧
    (PlainBnfDependencyWorklist.unpublished
      (graphKnown definitions (text (nameAt definitions event.position) :: history))).card + 1 =
        (PlainBnfDependencyWorklist.unpublished (graphKnown definitions history)).card := by
  have fresh := nextEvent_unpublished grammar (graphKnown definitions history)
    round cursor event selected
  have absent : text (nameAt definitions event.position) ∉ history := by
    simpa [graphKnown, PlainBnfProductiveSourceExecution.member] using fresh
  refine ⟨history_publish_scoped definitions history historyScoped event.position,
    List.nodup_cons.mpr ⟨absent, noRepeats⟩, ?_⟩
  rw [graphKnown_publish definitions unique history event.position]
  exact PlainBnfDependencyWorklist.publication_decreases_count
    (graphKnown definitions history) event.position fresh

/-- Both empty heaps imply that no definition is newly enabled; this is a
semantic stopping condition, not an exhausted search bound. -/
theorem empty_frontier_saturated (coordinate : HeapItem → Fin size)
    (grammar : Grammar size) (known : Known size)
    (scheduled : PlainBnfWakeContextualExecution.NameIndex)
    (frontier : pending coordinate (.nil, .nil, scheduled) =
      PlainBnfDependencyWorklist.initialQueue grammar known) :
    ∀ position, ready grammar known position = false := by
  intro position
  have absent : position ∉ PlainBnfDependencyWorklist.initialQueue grammar known := by
    rw [← frontier]
    simp [pending, PlainBnfTwoHeapWorklist.positions_nil]
  simpa [PlainBnfDependencyWorklist.initialQueue] using absent

/-- Rollover does not publish a definition: the known packet and all heap
contents are unchanged, while the cursor returns to the beginning. -/
theorem rollover_placement (coordinate : HeapItem → Fin size) (origin : Option Rank)
    (following : Heap HeapItem) (scheduled : PlainBnfWakeContextualExecution.NameIndex)
    (placed : WellPlaced coordinate origin (.nil, following, scheduled)) :
    WellPlaced coordinate none (following, .nil, scheduled) := by
  have partition := PlainBnfTwoHeapWorklist.rollover_partition coordinate
    (pending coordinate (.nil, following, scheduled))
    (PlainBnfScheduleWorklistBridge.cursor origin) following placed
  simpa only [WellPlaced, PlainBnfScheduleWorklistBridge.cursor, pending,
    PlainBnfTwoHeapWorklist.positions_nil, Finset.empty_union, Finset.union_empty] using partition

theorem exhausted_fuel_is_not_saturation :
    let grammar : Grammar 1 := fun _ => [⟨[], true⟩]
    PlainBnfOrderedGraphDiscovery.runEvents grammar 0 (fun _ => false) 0 0 = [] ∧
      ready grammar (fun _ => false) 0 = true := by decide

theorem published_name_is_not_ready_again :
    let grammar : Grammar 1 := fun _ => [⟨[], true⟩]
    ready grammar (PlainBnfOrderedGraphDiscovery.publish (fun _ => false) 0) 0 = false := by
  decide

#print axioms selection_eq_nextEvent
#print axioms selected_history_progress
#print axioms empty_frontier_saturated

end Mettapedia.GSLT.Parsing.PlainBnfControllerSelection
