import Mettapedia.GSLT.Parsing.PlainBnfStructuredDiscoveryGraph
import Mettapedia.GSLT.Parsing.PlainBnfWakeFrontierExactness

/-!
# Structured grammar initialization through the existing Wake fold

The empty-history expression meanings determine the initial productive and
nullable queues. Name-key injectivity follows from unique source definitions;
it is not a separate authority assumption. Candidate coordinates, source-data
agreement, and complete coverage remain explicit enumeration obligations.
Only the pending-position observation is identified here: source occurrences,
their order, and heap payloads remain unchanged. This is not a source execution,
generated-runtime, rank-enumeration, or full discovery-loop theorem.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfWakeGraphInitialization

open PlainBnfStructuredDenotation (LexicalDeclaration)
open PlainBnfStructuredDiscoveryGraph
open PlainBnfReverseIndexSourceExecution (Item key key_injective)
open PlainBnfSourceRank (Rank)
open PlainBnfWakeSourceExecution (HeapItem heapItem wake pending)
open PlainBnfWakeFrontierExactness (empty_wake_initialQueue)

theorem nameKey_injective (definitions : Definitions) (unique : (names definitions).Nodup) :
    Function.Injective (fun position => key (nameAt definitions position)) :=
  key_injective.comp (nameAt_injective definitions unique)

theorem productive_empty_ready (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (disjoint : NamesDisjoint definitions lexicals) (position : Fin definitions.length) :
    PlainBnfOrderedGraphDiscovery.ready (productiveGrammar definitions lexicals)
      (graphKnown definitions []) position =
      PlainBnfProductiveSourceExecution.expressionMeaning [] lexicals (expressionAt definitions position) := by
  rw [productive_ready_exact definitions [] lexicals (empty_history_scoped definitions) disjoint]
  simp [PlainBnfProductiveSourceExecution.member]

theorem nullable_empty_ready (definitions : Definitions) (position : Fin definitions.length) :
    PlainBnfOrderedGraphDiscovery.ready (nullableGrammar definitions)
      (graphKnown definitions []) position =
      PlainBnfNullableSourceExecution.expressionMeaning [] (expressionAt definitions position) := by
  rw [nullable_ready_exact definitions [] (empty_history_scoped definitions)]
  simp [PlainBnfProductiveSourceExecution.member]

/-- Full candidate coverage uses source positions, not a set of name spellings.
Repeated candidate occurrences are permitted; no input deduplication is added. -/
theorem productive_empty_wake (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (unique : (names definitions).Nodup) (disjoint : NamesDisjoint definitions lexicals)
    (coordinate : HeapItem → Fin definitions.length) (origin : Option Rank) (input : List Item)
    (nameCoordinates : ∀ item ∈ input,
      nameAt definitions (coordinate (heapItem item)) = item.2.name)
    (expressionCoordinates : ∀ item ∈ input,
      expressionAt definitions (coordinate (heapItem item)) = item.2.expression)
    (covers : ∀ position, ∃ item ∈ input, coordinate (heapItem item) = position) :
    pending coordinate (wake (PlainBnfProductiveSourceExecution.expressionMeaning [] lexicals)
      origin input (.nil, .nil, .empty)) =
      PlainBnfDependencyWorklist.initialQueue (productiveGrammar definitions lexicals)
        (graphKnown definitions []) := by
  apply empty_wake_initialQueue coordinate (fun position => key (nameAt definitions position))
    (nameKey_injective definitions unique) _ origin input
    (fun item member => congrArg key (nameCoordinates item member)) _ _ covers
  intro item member
  rw [productive_empty_ready definitions lexicals disjoint,
    expressionCoordinates item member]

theorem nullable_empty_wake (definitions : Definitions) (unique : (names definitions).Nodup)
    (coordinate : HeapItem → Fin definitions.length) (origin : Option Rank) (input : List Item)
    (nameCoordinates : ∀ item ∈ input,
      nameAt definitions (coordinate (heapItem item)) = item.2.name)
    (expressionCoordinates : ∀ item ∈ input,
      expressionAt definitions (coordinate (heapItem item)) = item.2.expression)
    (covers : ∀ position, ∃ item ∈ input, coordinate (heapItem item) = position) :
    pending coordinate (wake (PlainBnfNullableSourceExecution.expressionMeaning [])
      origin input (.nil, .nil, .empty)) =
      PlainBnfDependencyWorklist.initialQueue (nullableGrammar definitions)
        (graphKnown definitions []) := by
  apply empty_wake_initialQueue coordinate (fun position => key (nameAt definitions position))
    (nameKey_injective definitions unique) _ origin input
    (fun item member => congrArg key (nameCoordinates item member)) _ _ covers
  intro item member
  rw [nullable_empty_ready definitions, expressionCoordinates item member]

/-- Actual admitted definitions discharge both source-name uniqueness and the
productive view's grammar/lexical namespace separation. -/
theorem admitted_productive_empty_wake (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (origin : Option Rank) (input : List Item)
    (nameCoordinates : ∀ item ∈ input,
      nameAt (definitionsFromDocument admitted.document) (coordinate (heapItem item)) = item.2.name)
    (expressionCoordinates : ∀ item ∈ input,
      expressionAt (definitionsFromDocument admitted.document) (coordinate (heapItem item)) = item.2.expression)
    (covers : ∀ position, ∃ item ∈ input, coordinate (heapItem item) = position) :
    pending coordinate (wake
      (PlainBnfProductiveSourceExecution.expressionMeaning [] admitted.authority.lexicalDeclarations)
      origin input (.nil, .nil, .empty)) =
      PlainBnfDependencyWorklist.initialQueue
        (productiveGrammar (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
        (graphKnown (definitionsFromDocument admitted.document) []) :=
  productive_empty_wake _ _ (admitted_definition_names_unique admitted) (admitted_names_disjoint admitted)
    coordinate origin input nameCoordinates expressionCoordinates covers

theorem admitted_nullable_empty_wake (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (origin : Option Rank) (input : List Item)
    (nameCoordinates : ∀ item ∈ input,
      nameAt (definitionsFromDocument admitted.document) (coordinate (heapItem item)) = item.2.name)
    (expressionCoordinates : ∀ item ∈ input,
      expressionAt (definitionsFromDocument admitted.document) (coordinate (heapItem item)) = item.2.expression)
    (covers : ∀ position, ∃ item ∈ input, coordinate (heapItem item) = position) :
    pending coordinate (wake (PlainBnfNullableSourceExecution.expressionMeaning [])
      origin input (.nil, .nil, .empty)) =
      PlainBnfDependencyWorklist.initialQueue (nullableGrammar (definitionsFromDocument admitted.document))
        (graphKnown (definitionsFromDocument admitted.document) []) :=
  nullable_empty_wake _ (admitted_definition_names_unique admitted)
    coordinate origin input nameCoordinates expressionCoordinates covers

/-- An actually ready source definition is observed in the initial graph queue. -/
theorem productive_ready_in_initialQueue (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (disjoint : NamesDisjoint definitions lexicals) (position : Fin definitions.length)
    (available : PlainBnfProductiveSourceExecution.expressionMeaning [] lexicals
      (expressionAt definitions position) = true) :
    position ∈ PlainBnfDependencyWorklist.initialQueue (productiveGrammar definitions lexicals)
      (graphKnown definitions []) := by
  simp [PlainBnfDependencyWorklist.initialQueue, productive_empty_ready definitions lexicals disjoint,
    available]

/-- Alignment alone is insufficient: omitting all candidates loses every
initially ready position. Full coverage is a real, separate obligation. -/
theorem missing_candidates_lose_ready_position (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (disjoint : NamesDisjoint definitions lexicals) (coordinate : HeapItem → Fin definitions.length)
    (origin : Option Rank) (position : Fin definitions.length)
    (available : PlainBnfProductiveSourceExecution.expressionMeaning [] lexicals
      (expressionAt definitions position) = true) :
    pending coordinate (wake (PlainBnfProductiveSourceExecution.expressionMeaning [] lexicals)
      origin [] (.nil, .nil, .empty)) ≠
      PlainBnfDependencyWorklist.initialQueue (productiveGrammar definitions lexicals)
        (graphKnown definitions []) := by
  intro same
  have present := productive_ready_in_initialQueue definitions lexicals disjoint position available
  rw [← same] at present
  simp [PlainBnfWakeSourceExecution.wake_nil, pending,
    PlainBnfTwoHeapWorklist.positions_nil] at present

#print axioms nameKey_injective
#print axioms productive_empty_wake
#print axioms nullable_empty_wake
#print axioms admitted_productive_empty_wake
#print axioms admitted_nullable_empty_wake
#print axioms missing_candidates_lose_ready_position

end Mettapedia.GSLT.Parsing.PlainBnfWakeGraphInitialization
