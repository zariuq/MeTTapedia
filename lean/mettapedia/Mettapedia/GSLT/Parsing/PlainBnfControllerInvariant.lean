import Mettapedia.GSLT.Parsing.PlainBnfControllerInitialization
import Mettapedia.GSLT.Parsing.PlainBnfControllerQueuePreservation
import Mettapedia.GSLT.Parsing.PlainBnfControllerPayloadProvenance
import Mettapedia.GSLT.Parsing.PlainBnfControllerSelection

/-!
# Preservation of the discovery controller boundary

This predicate relates the existing source known packet and two heaps to
their grammar observation. It adds no runtime state or transition engine.
Initialization and publication derive the conjuncts from the authored source
components; final execution correctness requires the enclosing Run argument.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerInvariant

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Batteries.PairingHeapImp (Heap)
open PlainBnfStructuredDiscoveryGraph
open PlainBnfStructuredDenotation (LexicalDeclaration)
open PlainBnfSourceRank (Rank value)
open PlainBnfReverseIndexSourceExecution (Item key)
open PlainBnfWakeSourceExecution (HeapItem heapItem Queues Ordered WellPlaced pending)
open PlainBnfWakeContextualExecution (NameIndex meaning)
open PlainBnfRunSourceExecution (publishedHistory publishedIndex publishedQueues initialQueues)
open PlainBnfControllerPublicationFrontier (graph)
open PlainBnfControllerPayloadProvenance (FromCandidates)
open PlainBnfStructuredEnumeration (candidates)
open PlainBnfWakeFrontierExactness (ExactMarks)
open PlainBnfReferenceCollectionSourceExecution (text)
open PlainBnfHeapSourceExecution (itemLE)

def completed (definitions : Definitions) (history : List SExpr) : Finset (Fin definitions.length) :=
  Finset.univ.filter fun p => graphKnown definitions history p

structure Invariant (productive : Bool) (definitions : Definitions)
    (lexicals : List LexicalDeclaration) (coordinate : HeapItem → Fin definitions.length)
    (index : NameIndex) (history : List SExpr) (origin : Option Rank) (queues : Queues) : Prop where
  valid : PlainBnfKnownNamesSourceExecution.Valid index history
  historyScoped : HistoryScoped definitions history
  historyNodup : history.Nodup
  payloads : FromCandidates (candidates definitions) queues
  ordered : Ordered queues
  placed : WellPlaced coordinate origin queues
  unique : PlainBnfTwoHeapWorklist.UniquePositions coordinate queues.1 queues.2.1
  marks : ExactMarks coordinate (fun p => key (nameAt definitions p)) (completed definitions history) queues
  frontier : pending coordinate queues =
    PlainBnfDependencyWorklist.initialQueue (graph productive definitions lexicals) (graphKnown definitions history)

theorem completed_empty (definitions : Definitions) : completed definitions [] = ∅ := by
  simp [completed, graphKnown, PlainBnfProductiveSourceExecution.member]

theorem completed_publish (definitions : Definitions) (unique : (names definitions).Nodup)
    (history : List SExpr) (position : Fin definitions.length) :
    completed definitions (text (nameAt definitions position) :: history) =
      insert position (completed definitions history) := by
  unfold completed
  rw [graphKnown_publish definitions unique history position]
  ext p
  by_cases same : p = position <;> simp [PlainBnfOrderedGraphDiscovery.publish, same]

theorem initial_invariant (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (liveRanks : ∀ item ∈ candidates (definitionsFromDocument admitted.document),
      (coordinate (heapItem item)).val = value item.1) :
    Invariant productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations
      coordinate .empty [] none
      (initialQueues productive (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations) := by
  have enumeration := (PlainBnfStructuredEnumeration.source_decoded_step_iff
    PlainBnfTrieSourceExecution.scalarRelations (definitionsFromDocument admitted.document) (candidates _)).mpr rfl
  obtain ⟨ordered, placed, unique, marks, frontier, valid, historyScoped⟩ :=
    PlainBnfControllerInitialization.initialQueues_invariants productive admitted (candidates _)
      enumeration coordinate liveRanks
  exact ⟨valid, historyScoped, List.nodup_nil,
    PlainBnfControllerPayloadProvenance.initialQueues productive _ _, ordered, placed, unique,
    by simpa only [completed_empty] using marks, frontier⟩

theorem rollover (productive : Bool) (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (coordinate : HeapItem → Fin definitions.length) (index : NameIndex) (history : List SExpr)
    (origin : Option Rank) (following : Heap HeapItem) (scheduled : NameIndex)
    (before : Invariant productive definitions lexicals coordinate index history origin
      (.nil, following, scheduled)) :
    Invariant productive definitions lexicals coordinate index history none (following, .nil, scheduled) := by
  have samePending : pending coordinate (following, .nil, scheduled) =
      pending coordinate (.nil, following, scheduled) := by
    simp [pending, PlainBnfTwoHeapWorklist.positions_nil]
  refine ⟨before.valid, before.historyScoped, before.historyNodup,
    PlainBnfControllerPayloadProvenance.rollover_preserves _ following scheduled before.payloads,
    ⟨before.ordered.2, .nil⟩,
    PlainBnfControllerSelection.rollover_placement coordinate origin following scheduled before.placed,
    PlainBnfTwoHeapWorklist.rollover_unique coordinate before.unique, ?_, samePending.trans before.frontier⟩
  simpa only [ExactMarks, samePending] using before.marks

theorem live_ranks (productive : Bool) (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (coordinate : HeapItem → Fin definitions.length)
    (candidateRanks : ∀ item ∈ candidates definitions, (coordinate (heapItem item)).val = value item.1)
    (index : NameIndex) (history : List SExpr) (origin : Option Rank) (queues : Queues)
    (invariant : Invariant productive definitions lexicals coordinate index history origin queues) :
    ∀ item ∈ PlainBnfWakeSourceExecution.contents queues, (coordinate item).val = value item.1 :=
  PlainBnfControllerPayloadProvenance.live_rank_coordinate definitions coordinate candidateRanks
    queues invariant.payloads

theorem publication (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (candidateRanks : ∀ item ∈ candidates (definitionsFromDocument admitted.document),
      (coordinate (heapItem item)).val = value item.1)
    (index : NameIndex) (history : List SExpr) (origin : Option Rank)
    (item : Item) (children following : Heap HeapItem) (scheduled : NameIndex)
    (before : Invariant productive (definitionsFromDocument admitted.document)
      admitted.authority.lexicalDeclarations coordinate index history origin
      (.node (heapItem item) children .nil, following, scheduled)) :
    Invariant productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations
      coordinate (publishedIndex item index) (publishedHistory item history) (some item.1)
      (publishedQueues productive item
        (PlainBnfStructuredReverseDependencies.bucket (candidates (definitionsFromDocument admitted.document))
          item.2.name admitted.authority.lexicalDeclarations)
        history admitted.authority.lexicalDeclarations children following scheduled) := by
  let definitions := definitionsFromDocument admitted.document
  let lexicals := admitted.authority.lexicalDeclarations
  let position := coordinate (heapItem item)
  have uniqueNames := admitted_definition_names_unique admitted
  have disjoint := admitted_names_disjoint admitted
  have live := live_ranks productive definitions lexicals coordinate candidateRanks index history origin
    (.node (heapItem item) children .nil, following, scheduled) before
  have candidate : item ∈ candidates definitions :=
    PlainBnfControllerPayloadProvenance.live_heapItem_member _ _ before.payloads item
      (by simp [PlainBnfWakeSourceExecution.contents, PlainBnfPairingHeapObservation.contents])
  have nameEq := PlainBnfStructuredEnumeration.coordinate_names definitions coordinate candidateRanks item candidate
  have historyEq : publishedHistory item history = text (nameAt definitions position) :: history := by
    rw [nameEq]
    rfl
  have selected := PlainBnfControllerSelection.current_selected coordinate
    (graph productive definitions lexicals) (graphKnown definitions history) 0 origin
    (heapItem item) children following scheduled before.ordered before.placed before.frontier live
  have progress := PlainBnfControllerSelection.selected_history_progress definitions uniqueNames
    (graph productive definitions lexicals) history before.historyScoped before.historyNodup 0
    (PlainBnfScheduleWorklistBridge.cursor origin) ⟨0, position⟩ selected
  have namesInjective := PlainBnfWakeGraphInitialization.nameKey_injective definitions uniqueNames
  have bucketInside : PlainBnfStructuredReverseDependencies.bucket (candidates definitions) item.2.name lexicals ⊆
      candidates definitions := by
    intro next member
    exact (PlainBnfStructuredReverseDependencies.mem_bucket _ _ _ next).mp member |>.1
  have bucketKeys : ∀ next ∈ PlainBnfStructuredReverseDependencies.bucket
      (candidates definitions) item.2.name lexicals,
      key (nameAt definitions (coordinate (heapItem next))) = key next.2.name := by
    intro next member
    exact congrArg key (PlainBnfStructuredEnumeration.coordinate_names definitions coordinate candidateRanks
      next (bucketInside member))
  have structural := PlainBnfControllerQueuePreservation.publishedQueues_invariants productive coordinate
    (fun p => key (nameAt definitions p)) namesInjective (completed definitions history) origin item
    (PlainBnfStructuredReverseDependencies.bucket (candidates definitions) item.2.name lexicals)
    history lexicals children following scheduled before.ordered before.placed before.unique before.marks
    (fun payload member => (live payload (Multiset.mem_add.mpr (Or.inl member))).symm)
    (fun next member => (candidateRanks next (bucketInside member)).symm) bucketKeys
  have marksAfter : completed definitions (publishedHistory item history) =
      insert position (completed definitions history) := by
    rw [historyEq, completed_publish definitions uniqueNames]
  refine ⟨PlainBnfRunSourceExecution.published_valid item index history before.valid,
    historyEq ▸ progress.1, historyEq ▸ progress.2.1,
    PlainBnfControllerPayloadProvenance.publishedQueues productive _ item history lexicals
      children following scheduled before.ordered before.payloads,
    structural.1, structural.2.1, structural.2.2.1, ?_, ?_⟩
  · change ExactMarks coordinate (fun p => key (nameAt definitions p))
      (completed definitions (publishedHistory item history)) _
    rw [marksAfter]
    exact structural.2.2.2.2
  · have poppedOrder := PlainBnfControllerQueuePreservation.pop_ordered
      (heapItem item) children following scheduled before.ordered
    have poppedMarks := PlainBnfControllerQueuePreservation.pop_exact_marks coordinate
      (fun p => key (nameAt definitions p)) (completed definitions history)
      (heapItem item) children following scheduled before.unique before.marks
    have erased := (PlainBnfControllerQueuePreservation.pop_pending_unique coordinate
      (heapItem item) children following scheduled before.unique).1
    rw [before.frontier] at erased
    have refreshed := PlainBnfStructuredReverseDependencies.wake_refresh_frontier definitions lexicals
      uniqueNames disjoint (admitted_references_resolved admitted) (candidates definitions) coordinate
      (fun next member => (PlainBnfStructuredEnumeration.coordinate_payload definitions coordinate
        candidateRanks next member).symm)
      (PlainBnfStructuredEnumeration.coordinate_coverage definitions coordinate candidateRanks)
      position (some item.1) (graph productive definitions lexicals)
      (PlainBnfControllerPublicationFrontier.graph_dependents productive definitions lexicals position)
      (graphKnown definitions history) (insert position (completed definitions history))
      (meaning productive (publishedHistory item history) lexicals)
      (children.combine itemLE, following, scheduled) poppedOrder poppedMarks ?_ erased ?_
    · change pending coordinate (publishedQueues productive item
        (PlainBnfStructuredReverseDependencies.bucket (candidates definitions) item.2.name lexicals)
        history lexicals children following scheduled) =
        PlainBnfDependencyWorklist.initialQueue (graph productive definitions lexicals)
          (graphKnown definitions (publishedHistory item history))
      rw [publishedQueues, historyEq, ← nameEq]
      rw [historyEq, ← graphKnown_publish definitions uniqueNames history position] at refreshed
      exact refreshed
    · intro p
      rw [← completed_publish definitions uniqueNames history position]
      simp only [completed, Finset.mem_filter, Finset.mem_univ, true_and,
        graphKnown_publish definitions uniqueNames history position]
    · intro next member
      rw [← PlainBnfStructuredEnumeration.coordinate_expressions definitions coordinate candidateRanks next member,
        historyEq]
      exact PlainBnfControllerPublicationFrontier.published_readiness_exact productive definitions lexicals
        uniqueNames disjoint history before.historyScoped position (coordinate (heapItem next))

#print axioms initial_invariant
#print axioms rollover
#print axioms publication

end Mettapedia.GSLT.Parsing.PlainBnfControllerInvariant
