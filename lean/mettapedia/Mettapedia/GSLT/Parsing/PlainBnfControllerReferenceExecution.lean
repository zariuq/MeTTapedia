import Mettapedia.GSLT.Parsing.PlainBnfControllerInvariant
import Mettapedia.GSLT.Parsing.PlainBnfControllerReferenceIndex

/-!
# Authored Run returns the exact ordered reference packet

The existing source controller and ordered reference trace have the same
terminal known-name packet. Standard folds apply the trace to the original
trie and reversed history; the trie is never rebuilt from an extensional set.

Reference fuel counts publications. Rollover consumes no publication fuel;
its round counter is a proof observation, not an added runtime field. The
proof unfolds actual source rules and uses the existing controller
invariant, with explicit live coordinates and reverse-index execution.
It does not introduce a second interpreter or establish native correspondence.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerReferenceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Batteries.PairingHeapImp (Heap)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open PlainBnfSourceRank (Rank value)
open PlainBnfStructuredDiscoveryGraph
open PlainBnfStructuredEnumeration (candidates)
open PlainBnfReverseIndexSourceExecution (Item key)
open PlainBnfGraphNameTrie (insertFirst)
open PlainBnfWakeSourceExecution (HeapItem heapItem Queues Ordered WellPlaced pending contents)
open PlainBnfWakeContextualExecution (NameIndex)
open PlainBnfKnownNamesSourceExecution (known)
open PlainBnfControllerInvariant (Invariant)
open PlainBnfControllerPublicationFrontier (graph)
open PlainBnfReferenceCollectionSourceExecution (text)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfTrieSourceExecution (scalarRelations result trie)
open PlainBnfRunSourceFamily (language)
open PlainBnfRunSourceExecution (runCall publishedIndex publishedHistory publishedQueues)
open PlainBnfOrderedGraphDiscovery (Grammar Known Event nextEvent runEvents publish)
open PlainBnfScheduleWorklistBridge (cursor)

/-- Rollover changes only the round/cursor observation. Its next reference
event and entire remaining reference trace are unchanged, without spending
one of the publication steps counted by fuel. -/
theorem rollover_reference_events {size : Nat}
    (coordinate : HeapItem → Fin size) (grammar : Grammar size) (before : Known size)
    (round fuel : Nat) (origin : Option Rank) (following : Heap HeapItem) (scheduled : NameIndex)
    (ordered : Ordered (.nil, following, scheduled))
    (placed : WellPlaced coordinate origin (.nil, following, scheduled))
    (frontier : pending coordinate (.nil, following, scheduled) =
      PlainBnfDependencyWorklist.initialQueue grammar before)
    (ranks : ∀ item ∈ contents (.nil, following, scheduled), (coordinate item).val = value item.1) :
    runEvents grammar fuel before round (cursor origin) =
      runEvents grammar fuel before (round + 1) 0 := by
  have rolledFrontier : pending coordinate (following, .nil, scheduled) =
      PlainBnfDependencyWorklist.initialQueue grammar before := by
    simpa only [pending, PlainBnfTwoHeapWorklist.positions_nil,
      Finset.empty_union, Finset.union_empty] using frontier
  have rolledRanks : ∀ item ∈ contents (following, .nil, scheduled),
      (coordinate item).val = value item.1 := by
    intro item member
    apply ranks item
    simpa only [contents, PlainBnfPairingHeapObservation.contents, zero_add, add_zero] using member
  have first := PlainBnfControllerSelection.selection_eq_nextEvent coordinate grammar before round origin
    (.nil, following, scheduled) ordered placed frontier ranks
  have second := PlainBnfControllerSelection.selection_eq_nextEvent coordinate grammar before (round + 1) none
    (following, .nil, scheduled) ⟨ordered.2, .nil⟩
    (PlainBnfControllerSelection.rollover_placement coordinate origin following scheduled placed)
    rolledFrontier rolledRanks
  simp only [cursor] at second
  have same : nextEvent grammar before round (cursor origin) = nextEvent grammar before (round + 1) 0 := by
    rw [← first, ← second]
    cases following <;> rfl
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [runEvents, same]

/-- An invariant source Run returns exactly the existing ordered reference
trace replayed into its original packet. The fuel bound is sufficient, not
an asserted native work or contextual-depth bound. -/
theorem run_reference_packet_iff (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (candidateRanks : ∀ item ∈ candidates (definitionsFromDocument admitted.document),
      (coordinate (heapItem item)).val = value item.1)
    (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse)))
    (fuel : Nat) (index : NameIndex) (history : List SExpr) (origin : Option Rank) (queues : Queues)
    (round : Nat)
    (invariant : Invariant productive (definitionsFromDocument admitted.document)
      admitted.authority.lexicalDeclarations coordinate index history origin queues)
    (enough : (PlainBnfDependencyWorklist.unpublished
      (graphKnown (definitionsFromDocument admitted.document) history)).card ≤ fuel)
    (target : Pattern) :
    let events := runEvents
      (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
      fuel (graphKnown (definitionsFromDocument admitted.document) history) round (cursor origin)
    Step (engineBasePremises relations) language
      (runCall productive reverse admitted.authority.lexicalDeclarations index history queues) target ↔
      target = result (known
        (events.foldl (fun current event =>
          insertFirst (key (nameAt (definitionsFromDocument admitted.document) event.position))
            (text (nameAt (definitionsFromDocument admitted.document) event.position)) current) index)
        (events.foldl (fun current event =>
          text (nameAt (definitionsFromDocument admitted.document) event.position) :: current) history)) := by
  induction fuel generalizing index history origin queues round with
  | zero =>
      have noEvent := PlainBnfControllerReferenceHistory.zero_sufficient_no_event
        (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
        (graphKnown (definitionsFromDocument admitted.document) history) round (cursor origin) enough
      have selected := PlainBnfControllerSelection.selection_eq_nextEvent coordinate _ _ round origin queues
        invariant.ordered invariant.placed invariant.frontier
        (PlainBnfControllerInvariant.live_ranks productive _ _ coordinate candidateRanks
          index history origin queues invariant)
      rw [noEvent] at selected
      rcases queues with ⟨current, following, scheduled⟩
      cases current with
      | nil =>
          cases following with
          | nil =>
              exact PlainBnfRunSourceExecution.run_done productive reverse
                admitted.authority.lexicalDeclarations index history scheduled target
          | node payload children siblings =>
              change some (⟨round + 1, coordinate payload⟩ : Event _) = none at selected
              cases selected
      | node payload children siblings =>
          change some (⟨round, coordinate payload⟩ : Event _) = none at selected
          cases selected
  | succ fuel ih =>
      have nonempty (thisRound : Nat) (thisOrigin : Option Rank) (payload : HeapItem)
          (children following : Heap HeapItem) (scheduled : NameIndex)
          (before : Invariant productive (definitionsFromDocument admitted.document)
            admitted.authority.lexicalDeclarations coordinate index history thisOrigin
            (.node payload children .nil, following, scheduled)) :
          let events := runEvents
            (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
            (fuel + 1) (graphKnown (definitionsFromDocument admitted.document) history) thisRound (cursor thisOrigin)
          Step (engineBasePremises relations) language
            (runCall productive reverse admitted.authority.lexicalDeclarations index history
              (.node payload children .nil, following, scheduled)) target ↔
            target = result (known
              (events.foldl (fun current event =>
                insertFirst (key (nameAt (definitionsFromDocument admitted.document) event.position))
                  (text (nameAt (definitionsFromDocument admitted.document) event.position)) current) index)
              (events.foldl (fun current event =>
                text (nameAt (definitionsFromDocument admitted.document) event.position) :: current) history)) := by
        obtain ⟨item, member, same⟩ := before.payloads payload
          (by simp [contents, PlainBnfPairingHeapObservation.contents])
        subst payload
        let definitions := definitionsFromDocument admitted.document
        let lexicals := admitted.authority.lexicalDeclarations
        let event : Event definitions.length := ⟨thisRound, coordinate (heapItem item)⟩
        have ranks := PlainBnfControllerInvariant.live_ranks productive definitions lexicals coordinate candidateRanks
          index history thisOrigin _ before
        have selected := PlainBnfControllerSelection.current_selected coordinate
          (graph productive definitions lexicals) (graphKnown definitions history) thisRound thisOrigin
          (heapItem item) children following scheduled before.ordered before.placed before.frontier ranks
        have alignment := (PlainBnfStructuredEnumeration.coordinate_payload definitions coordinate
          candidateRanks item member).symm
        have updates := PlainBnfControllerReferenceIndex.publication_event_update definitions event
          item alignment index history
        have progress := PlainBnfControllerSelection.selected_history_progress definitions
          (admitted_definition_names_unique admitted) (graph productive definitions lexicals)
          history before.historyScoped before.historyNodup thisRound (cursor thisOrigin) event selected
        have enoughAfter : (PlainBnfDependencyWorklist.unpublished
            (graphKnown definitions (publishedHistory item history))).card ≤ fuel := by
          rw [updates.2]
          have decrease := progress.2.2
          change (PlainBnfDependencyWorklist.unpublished (graphKnown definitions history)).card ≤ fuel + 1 at enough
          omega
        have afterInvariant := PlainBnfControllerInvariant.publication productive admitted coordinate candidateRanks
          index history thisOrigin item children following scheduled before
        have recursive := ih (publishedIndex item index) (publishedHistory item history) (some item.1)
          (publishedQueues productive item
            (PlainBnfStructuredReverseDependencies.bucket (candidates definitions) item.2.name lexicals)
            history lexicals children following scheduled) thisRound afterInvariant enoughAfter
        have knownAfter : graphKnown definitions (publishedHistory item history) =
            publish (graphKnown definitions history) event.position := by
          rw [updates.2, graphKnown_publish definitions (admitted_definition_names_unique admitted)]
        have cursorAfter : cursor (some item.1) = event.position.val + 1 := by
          change value item.1 + 1 = (coordinate (heapItem item)).val + 1
          rw [candidateRanks item member]
        have afterEvents : runEvents (graph productive definitions lexicals) fuel
            (graphKnown definitions (publishedHistory item history)) thisRound (cursor (some item.1)) =
            runEvents (graph productive definitions lexicals) fuel
              (publish (graphKnown definitions history) event.position) event.round (event.position.val + 1) := by
          rw [knownAfter, cursorAfter]
        have traceStep := PlainBnfControllerReferenceHistory.runEvents_succ
          (graph productive definitions lexicals) fuel (graphKnown definitions history) thisRound
          (cursor thisOrigin) event selected
        dsimp only [definitions, lexicals, event] at recursive afterEvents traceStep updates
        dsimp only
        rw [PlainBnfRunIndexedInputs.run_publish_indexed_iff productive item _ reverse index history
          lexicals children following scheduled before.valid indexed target]
        apply recursive.trans
        rw [afterEvents, traceStep]
        simp only [List.foldl_cons, updates.1, updates.2]
      rcases queues with ⟨current, following, scheduled⟩
      cases current with
      | nil =>
          cases following with
          | nil =>
              have noEvent := (PlainBnfControllerReferenceHistory.nextEvent_none_iff
                (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
                (graphKnown (definitionsFromDocument admitted.document) history) round (cursor origin)).mpr
                (PlainBnfControllerSelection.empty_frontier_saturated coordinate _ _ scheduled invariant.frontier)
              dsimp only
              rw [runEvents, noEvent]
              exact PlainBnfRunSourceExecution.run_done productive reverse
                admitted.authority.lexicalDeclarations index history scheduled target
          | node payload children siblings =>
              have noSiblings : siblings = .nil := by cases invariant.ordered.2; rfl
              subst siblings
              have rolled := PlainBnfControllerInvariant.rollover productive
                (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations coordinate
                index history origin (.node payload children .nil) scheduled invariant
              have sameEvents := rollover_reference_events coordinate _ _ round (fuel + 1) origin
                (.node payload children .nil) scheduled invariant.ordered invariant.placed invariant.frontier
                (PlainBnfControllerInvariant.live_ranks productive _ _ coordinate candidateRanks
                  index history origin _ invariant)
              dsimp only
              rw [sameEvents, PlainBnfRunSourceExecution.run_rollover_iff]
              exact nonempty (round + 1) none payload children .nil scheduled rolled
      | node payload children siblings =>
          have noSiblings : siblings = .nil := by cases invariant.ordered.1; rfl
          subst siblings
          exact nonempty round origin payload children following scheduled invariant

/-- A newly enabled later rule precedes an independently ready later seed.
Replacing the reference order by a FIFO order would change the trace. -/
theorem cascade_order_control :
    let grammar : Grammar 3 := fun position =>
      if position = 1 then [⟨[0], true⟩] else [⟨[], true⟩]
    runEvents grammar 3 (fun _ => false) 0 0 = [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩] ∧
    runEvents grammar 3 (fun _ => false) 0 0 ≠ [⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 1⟩] := by decide

/-- The terminal source rule preserves reference publication order in
the stored reversed history, including the untouched original suffix. -/
theorem two_event_terminal_packet (productive : Bool) (definitions : Definitions)
    (first second : Event definitions.length) (index : NameIndex) (history : List SExpr) :
    Step (engineBasePremises relations) language
      (runCall productive .empty []
        ([first, second].foldl (fun current event =>
          insertFirst (key (nameAt definitions event.position))
            (text (nameAt definitions event.position)) current) index)
        ([first, second].foldl (fun current event => text (nameAt definitions event.position) :: current) history)
        (.nil, .nil, .empty))
      (result (known
        ([first, second].foldl (fun current event =>
          insertFirst (key (nameAt definitions event.position))
            (text (nameAt definitions event.position)) current) index)
        (text (nameAt definitions second.position) :: text (nameAt definitions first.position) :: history))) := by
  apply (PlainBnfControllerReferenceIndex.terminal_replay_packet_iff productive definitions
    [first, second] index history .empty [] .empty _).mpr
  rfl

theorem two_event_terminal_refuses_forward_history (productive : Bool) (definitions : Definitions)
    (first second : Event definitions.length)
    (different : nameAt definitions first.position ≠ nameAt definitions second.position)
    (index : NameIndex) (history : List SExpr) :
    ¬ Step (engineBasePremises relations) language
      (runCall productive .empty []
        ([first, second].foldl (fun current event =>
          insertFirst (key (nameAt definitions event.position))
            (text (nameAt definitions event.position)) current) index)
        ([first, second].foldl (fun current event => text (nameAt definitions event.position) :: current) history)
        (.nil, .nil, .empty))
      (result (known
        ([first, second].foldl (fun current event =>
          insertFirst (key (nameAt definitions event.position))
            (text (nameAt definitions event.position)) current) index)
        (text (nameAt definitions first.position) :: text (nameAt definitions second.position) :: history))) := by
  intro executed
  have exactPacket := (PlainBnfControllerReferenceIndex.terminal_replay_packet_iff productive definitions
    [first, second] index history .empty [] .empty _).mp executed
  have sameHistory := ((PlainBnfKnownNamesSourceExecution.known_eq_iff _ _ _ _).mp
    (PlainBnfTrieSourceExecution.result_injective exactPacket)).2
  have sameHead := (List.cons.inj sameHistory).1
  exact different (PlainBnfReferenceCollectionSourceExecution.text_injective sameHead)

/-- Publication fuel is not source-contextual fuel: zero events can still
omit an enabled publication, so the theorem's sufficient bound matters. -/
theorem short_reference_fuel_changes_history_length :
    let grammar : Grammar 1 := fun _ => [⟨[], true⟩]
    (runEvents grammar 0 (fun _ => false) 0 0).length = 0 ∧
    (runEvents grammar 1 (fun _ => false) 0 0).length = 1 := by decide

end Mettapedia.GSLT.Parsing.PlainBnfControllerReferenceExecution
