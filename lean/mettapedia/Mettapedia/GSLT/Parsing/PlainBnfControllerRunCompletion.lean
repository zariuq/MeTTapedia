import Mettapedia.GSLT.Parsing.PlainBnfControllerInvariant

/-!
# Whole authored Run completion from the controller invariant

Strong induction counts unpublished definition positions. Publication strictly
decreases that finite measure; rollover only rearranges the existing queues
and is handled before the next publication. The final packet contains the
actual original trie extended by the source's insert-first operations, never
a reconstructed index of an extensionally equal set.

These theorems concern actual contextual source execution. A unique returned
value does not assert a unique proof derivation or generated-backend behavior.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerRunCompletion

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Batteries.PairingHeapImp (Heap)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open PlainBnfSourceRank (Rank value)
open PlainBnfStructuredDiscoveryGraph
open PlainBnfStructuredEnumeration (candidates)
open PlainBnfReverseIndexSourceExecution (Item)
open PlainBnfWakeSourceExecution (HeapItem heapItem Queues)
open PlainBnfWakeContextualExecution (NameIndex)
open PlainBnfKnownNamesSourceExecution (known Valid)
open PlainBnfControllerInvariant (Invariant)
open PlainBnfControllerPublicationFrontier (graph)
open PlainBnfReferenceCollectionSourceExecution (text)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfTrieSourceExecution (scalarRelations result trie)
open PlainBnfRunSourceFamily (language)
open PlainBnfRunSourceExecution (runCall publishedIndex publishedHistory publishedQueues)

private theorem publication_decreases (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (candidateRanks : ∀ item ∈ candidates (definitionsFromDocument admitted.document),
      (coordinate (heapItem item)).val = value item.1)
    (index : NameIndex) (history : List SExpr) (origin : Option Rank)
    (item : Item) (children following : Heap HeapItem) (scheduled : NameIndex)
    (invariant : Invariant productive (definitionsFromDocument admitted.document)
      admitted.authority.lexicalDeclarations coordinate index history origin
      (.node (heapItem item) children .nil, following, scheduled)) :
    (PlainBnfDependencyWorklist.unpublished
      (graphKnown (definitionsFromDocument admitted.document) (publishedHistory item history))).card <
    (PlainBnfDependencyWorklist.unpublished
      (graphKnown (definitionsFromDocument admitted.document) history)).card := by
  let definitions := definitionsFromDocument admitted.document
  let lexicals := admitted.authority.lexicalDeclarations
  have live := PlainBnfControllerInvariant.live_ranks productive definitions lexicals coordinate candidateRanks
    index history origin _ invariant
  have candidate : item ∈ candidates definitions :=
    PlainBnfControllerPayloadProvenance.live_heapItem_member _ _ invariant.payloads item
      (by simp [PlainBnfWakeSourceExecution.contents, PlainBnfPairingHeapObservation.contents])
  have nameEq := PlainBnfStructuredEnumeration.coordinate_names definitions coordinate candidateRanks item candidate
  have selected := PlainBnfControllerSelection.current_selected coordinate
    (graph productive definitions lexicals) (graphKnown definitions history) 0 origin
    (heapItem item) children following scheduled invariant.ordered invariant.placed invariant.frontier live
  have progress := PlainBnfControllerSelection.selected_history_progress definitions
    (admitted_definition_names_unique admitted) (graph productive definitions lexicals)
    history invariant.historyScoped invariant.historyNodup 0 (PlainBnfScheduleWorklistBridge.cursor origin)
    ⟨0, coordinate (heapItem item)⟩ selected
  have historyEq : publishedHistory item history = text (nameAt definitions (coordinate (heapItem item))) :: history := by
    rw [nameEq]
    rfl
  rw [historyEq]
  exact Nat.lt_of_add_one_le (Nat.le_of_eq progress.2.2)

/-- Every invariant controller state has one exact returned known packet.
The final history extends the original occurrence list as a suffix, remains
scoped and duplicate-free, and no rule is newly ready at termination. -/
theorem run_complete (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (candidateRanks : ∀ item ∈ candidates (definitionsFromDocument admitted.document),
      (coordinate (heapItem item)).val = value item.1)
    (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse)))
    (index : NameIndex) (history : List SExpr) (origin : Option Rank) (queues : Queues)
    (invariant : Invariant productive (definitionsFromDocument admitted.document)
      admitted.authority.lexicalDeclarations coordinate index history origin queues) :
    ∃ (finalIndex : NameIndex) (finalHistory : List SExpr),
      Valid finalIndex finalHistory ∧ HistoryScoped (definitionsFromDocument admitted.document) finalHistory ∧
      finalHistory.Nodup ∧ history.IsSuffix finalHistory ∧
      (∀ position, PlainBnfOrderedGraphDiscovery.ready
        (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
        (graphKnown (definitionsFromDocument admitted.document) finalHistory) position = false) ∧
      (∀ target : Pattern,
        Step (engineBasePremises relations) language
          (runCall productive reverse admitted.authority.lexicalDeclarations index history queues) target ↔
          target = result (known finalIndex finalHistory)) := by
  generalize countEq : (PlainBnfDependencyWorklist.unpublished
    (graphKnown (definitionsFromDocument admitted.document) history)).card = count
  induction count using Nat.strong_induction_on generalizing index history origin queues with
  | h count ih =>
    have nonempty (thisOrigin : Option Rank) (payload : HeapItem)
        (children following : Heap HeapItem) (scheduled : NameIndex)
        (before : Invariant productive (definitionsFromDocument admitted.document)
          admitted.authority.lexicalDeclarations coordinate index history thisOrigin
          (.node payload children .nil, following, scheduled)) :
        ∃ (finalIndex : NameIndex) (finalHistory : List SExpr),
          Valid finalIndex finalHistory ∧ HistoryScoped (definitionsFromDocument admitted.document) finalHistory ∧
          finalHistory.Nodup ∧ history.IsSuffix finalHistory ∧
          (∀ position, PlainBnfOrderedGraphDiscovery.ready
            (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
            (graphKnown (definitionsFromDocument admitted.document) finalHistory) position = false) ∧
          (∀ target : Pattern,
            Step (engineBasePremises relations) language
              (runCall productive reverse admitted.authority.lexicalDeclarations index history
                (.node payload children .nil, following, scheduled)) target ↔
              target = result (known finalIndex finalHistory)) := by
      obtain ⟨item, _, same⟩ := before.payloads payload
        (by simp [PlainBnfWakeSourceExecution.contents, PlainBnfPairingHeapObservation.contents])
      subst payload
      have afterInvariant := PlainBnfControllerInvariant.publication productive admitted coordinate candidateRanks
        index history thisOrigin item children following scheduled before
      have decrease := publication_decreases productive admitted coordinate candidateRanks
        index history thisOrigin item children following scheduled before
      obtain ⟨finalIndex, finalHistory, valid, finalScoped, nodup, suffix, saturated, exactAnswer⟩ :=
        ih _ (by omega) (publishedIndex item index) (publishedHistory item history) (some item.1)
          (publishedQueues productive item
            (PlainBnfStructuredReverseDependencies.bucket (candidates (definitionsFromDocument admitted.document))
              item.2.name admitted.authority.lexicalDeclarations)
            history admitted.authority.lexicalDeclarations children following scheduled) afterInvariant rfl
      refine ⟨finalIndex, finalHistory, valid, finalScoped, nodup,
        (List.suffix_cons _ history).trans suffix, saturated, ?_⟩
      intro target
      rw [PlainBnfRunIndexedInputs.run_publish_indexed_iff productive item _ reverse index history
        admitted.authority.lexicalDeclarations children following scheduled before.valid indexed target]
      exact exactAnswer target
    rcases queues with ⟨current, following, scheduled⟩
    cases current with
    | nil =>
      cases following with
      | nil =>
        exact ⟨index, history, invariant.valid, invariant.historyScoped, invariant.historyNodup,
          List.suffix_refl _, PlainBnfControllerSelection.empty_frontier_saturated coordinate
            (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
            (graphKnown (definitionsFromDocument admitted.document) history) scheduled invariant.frontier,
          PlainBnfRunSourceExecution.run_done productive reverse admitted.authority.lexicalDeclarations
            index history scheduled⟩
      | node payload children siblings =>
        have noSiblings : siblings = .nil := by cases invariant.ordered.2; rfl
        subst siblings
        have rolled := PlainBnfControllerInvariant.rollover productive
          (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations coordinate
          index history origin (.node payload children .nil) scheduled invariant
        obtain ⟨finalIndex, finalHistory, valid, finalScoped, nodup, suffix, saturated, exactAnswer⟩ :=
          nonempty none payload children .nil scheduled rolled
        refine ⟨finalIndex, finalHistory, valid, finalScoped, nodup, suffix, saturated, ?_⟩
        intro target
        rw [PlainBnfRunSourceExecution.run_rollover_iff]
        exact exactAnswer target
    | node payload children siblings =>
      have noSiblings : siblings = .nil := by cases invariant.ordered.1; rfl
      subst siblings
      exact nonempty origin payload children following scheduled invariant

/-- Arbitrary successful final targets agree; this is value uniqueness,
not an assertion that distinct proof derivations are identical. -/
theorem returned_answer_unique (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (candidateRanks : ∀ item ∈ candidates (definitionsFromDocument admitted.document),
      (coordinate (heapItem item)).val = value item.1)
    (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse)))
    (index : NameIndex) (history : List SExpr) (origin : Option Rank) (queues : Queues)
    (invariant : Invariant productive (definitionsFromDocument admitted.document)
      admitted.authority.lexicalDeclarations coordinate index history origin queues)
    (first second : Pattern)
    (firstReturned : Step (engineBasePremises relations) language
      (runCall productive reverse admitted.authority.lexicalDeclarations index history queues) first)
    (secondReturned : Step (engineBasePremises relations) language
      (runCall productive reverse admitted.authority.lexicalDeclarations index history queues) second) :
    first = second := by
  obtain ⟨_, _, _, _, _, _, _, exactAnswer⟩ := run_complete productive admitted coordinate candidateRanks
    reverse indexed index history origin queues invariant
  exact ((exactAnswer first).mp firstReturned).trans ((exactAnswer second).mp secondReturned).symm

/-- The complete source controller cannot replace the returned known packet
with an unrelated atom, even if that atom is syntactically valid quoted data. -/
theorem atom_is_not_a_complete_answer (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (candidateRanks : ∀ item ∈ candidates (definitionsFromDocument admitted.document),
      (coordinate (heapItem item)).val = value item.1)
    (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse)))
    (index : NameIndex) (history : List SExpr) (origin : Option Rank) (queues : Queues)
    (invariant : Invariant productive (definitionsFromDocument admitted.document)
      admitted.authority.lexicalDeclarations coordinate index history origin queues)
    (atom : String) :
    ¬ Step (engineBasePremises relations) language
      (runCall productive reverse admitted.authority.lexicalDeclarations index history queues)
      (result (.atom atom)) := by
  obtain ⟨_, _, _, _, _, _, _, exactAnswer⟩ := run_complete productive admitted coordinate candidateRanks
    reverse indexed index history origin queues invariant
  rw [exactAnswer, PlainBnfTrieSourceExecution.result_injective.eq_iff]
  simp [known]

end Mettapedia.GSLT.Parsing.PlainBnfControllerRunCompletion
