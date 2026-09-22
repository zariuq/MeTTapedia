import Mettapedia.GSLT.Parsing.PlainBnfRunSourceFamily
import Mettapedia.GSLT.Parsing.PlainBnfStructuredEnumeration
import Mettapedia.GSLT.Parsing.PlainBnfStructuredReverseDependencies
import Mettapedia.GSLT.Parsing.PlainBnfWakeOperationalFrontier

/-!
# Actual enumeration and reverse-index inputs to the controller

Successful source enumeration supplies candidate coverage and complete payload
alignment. Actual Wake execution in the controller family then initializes
the existing graph frontier. Reverse-index execution over that same candidate
list supplies the controller's exact ordered dependent bucket. Finite position
sets are only observations; the source list and queue packet stay unchanged.

These theorems do not assert whole-loop termination, publication order, or
generated/native correspondence. Live coordinate/rank agreement remains an
explicit observation boundary, not a default decoding of malformed ranks.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerInputExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfTrieSourceExecution (scalarRelations result trie)
open PlainBnfReverseIndexSourceExecution (Item key nodes)
open PlainBnfStructuredDiscoveryGraph
open PlainBnfStructuredEnumeration (wireDefinition candidates)
open PlainBnfSourceRank (Rank value)
open PlainBnfWakeSourceExecution (HeapItem heapItem Queues pending encodeQueues)
open PlainBnfWakeContextualExecution (NameIndex wakeCall)

theorem enumerated_productive_initialQueue
    (admitted : PlainBnfSemanticAdmission.AdmittedInput) (input : List Item)
    (enumerated : Step (engineBasePremises scalarRelations) PlainBnfEnumerationSourceExecution.language
      (PlainBnfEnumerationSourceExecution.enumerationCall
        ((definitionsFromDocument admitted.document).map wireDefinition) .zero) (result (nodes input)))
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (liveRanks : ∀ item ∈ input, (coordinate (heapItem item)).val = value item.1)
    (origin : Option Rank) (after : Queues)
    (executed : Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (wakeCall true input origin .empty [] admitted.authority.lexicalDeclarations (.nil, .nil, .empty))
      (result (encodeQueues after))) :
    pending coordinate after = PlainBnfDependencyWorklist.initialQueue
      (productiveGrammar (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
      (graphKnown (definitionsFromDocument admitted.document) []) := by
  have exactInput := (PlainBnfStructuredEnumeration.source_decoded_step_iff
    scalarRelations _ input).mp enumerated
  subst input
  apply PlainBnfWakeOperationalFrontier.execution_productive_initialQueue admitted coordinate origin
    (candidates _) after
    (PlainBnfStructuredEnumeration.coordinate_names _ coordinate liveRanks)
    (PlainBnfStructuredEnumeration.coordinate_expressions _ coordinate liveRanks)
    (PlainBnfStructuredEnumeration.coordinate_coverage _ coordinate liveRanks)
  exact (PlainBnfRunSourceFamily.wake_step_iff _ _ (by rfl)).mp executed

theorem enumerated_nullable_initialQueue
    (admitted : PlainBnfSemanticAdmission.AdmittedInput) (input : List Item)
    (enumerated : Step (engineBasePremises scalarRelations) PlainBnfEnumerationSourceExecution.language
      (PlainBnfEnumerationSourceExecution.enumerationCall
        ((definitionsFromDocument admitted.document).map wireDefinition) .zero) (result (nodes input)))
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (liveRanks : ∀ item ∈ input, (coordinate (heapItem item)).val = value item.1)
    (origin : Option Rank) (after : Queues)
    (executed : Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (wakeCall false input origin .empty [] admitted.authority.lexicalDeclarations (.nil, .nil, .empty))
      (result (encodeQueues after))) :
    pending coordinate after = PlainBnfDependencyWorklist.initialQueue
      (nullableGrammar (definitionsFromDocument admitted.document))
      (graphKnown (definitionsFromDocument admitted.document) []) := by
  have exactInput := (PlainBnfStructuredEnumeration.source_decoded_step_iff
    scalarRelations _ input).mp enumerated
  subst input
  apply PlainBnfWakeOperationalFrontier.execution_nullable_initialQueue admitted coordinate origin
    (candidates _) after
    (PlainBnfStructuredEnumeration.coordinate_names _ coordinate liveRanks)
    (PlainBnfStructuredEnumeration.coordinate_expressions _ coordinate liveRanks)
    (PlainBnfStructuredEnumeration.coordinate_coverage _ coordinate liveRanks)
  exact (PlainBnfRunSourceFamily.wake_step_iff _ _ (by rfl)).mp executed

/-- The common controller environment uses the bucket produced by the actual
scalar reverse-index execution. No answer-producing provider is installed. -/
theorem reverse_execution_dependents_iff (input : List Item) (query : String)
    (lexicals : List PlainBnfStructuredDenotation.LexicalDeclaration) (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall input lexicals .empty) (result (trie reverse)))
    (target : Pattern) :
    Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (PlainBnfReverseReferencesSourceExecution.dependentsCall
        (PlainBnfGraphNameTrie.lookup (key query) reverse)) target ↔
      target = result (nodes (PlainBnfStructuredReverseDependencies.bucket input query lexicals)) := by
  rw [PlainBnfRunSourceFamily.dependents_step_iff,
    PlainBnfStructuredReverseDependencies.execution_lookup_bucket input query lexicals reverse indexed]

/-- Enumeration discharges both full payload alignment and coverage for the
bucket's finite dependency observation; neither is guessed from rank syntax. -/
theorem enumerated_dependency_positions
    (admitted : PlainBnfSemanticAdmission.AdmittedInput) (input : List Item)
    (enumerated : Step (engineBasePremises scalarRelations) PlainBnfEnumerationSourceExecution.language
      (PlainBnfEnumerationSourceExecution.enumerationCall
        ((definitionsFromDocument admitted.document).map wireDefinition) .zero) (result (nodes input)))
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (liveRanks : ∀ item ∈ input, (coordinate (heapItem item)).val = value item.1)
    (position : Fin (definitionsFromDocument admitted.document).length) :
    PlainBnfWakeFrontierExactness.occurrencePositions coordinate
      (PlainBnfStructuredReverseDependencies.bucket input
        (nameAt (definitionsFromDocument admitted.document) position) admitted.authority.lexicalDeclarations) =
      PlainBnfDependencyWorklist.dependents
        (productiveGrammar (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
        position := by
  have exactInput := (PlainBnfStructuredEnumeration.source_decoded_step_iff
    scalarRelations _ input).mp enumerated
  subst input
  apply PlainBnfStructuredReverseDependencies.admitted_bucket_positions admitted (candidates _) coordinate
  · intro item member
    exact (PlainBnfStructuredEnumeration.coordinate_payload _ coordinate liveRanks item member).symm
  · exact PlainBnfStructuredEnumeration.coordinate_coverage _ coordinate liveRanks

/-- Exact source output precedes the lossy finite-position observation. -/
theorem enumerated_reverse_execution_positions
    (admitted : PlainBnfSemanticAdmission.AdmittedInput) (input output : List Item)
    (enumerated : Step (engineBasePremises scalarRelations) PlainBnfEnumerationSourceExecution.language
      (PlainBnfEnumerationSourceExecution.enumerationCall
        ((definitionsFromDocument admitted.document).map wireDefinition) .zero) (result (nodes input)))
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (liveRanks : ∀ item ∈ input, (coordinate (heapItem item)).val = value item.1)
    (position : Fin (definitionsFromDocument admitted.document).length) (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall input admitted.authority.lexicalDeclarations .empty)
      (result (trie reverse)))
    (executed : Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (PlainBnfReverseReferencesSourceExecution.dependentsCall
        (PlainBnfGraphNameTrie.lookup (key (nameAt (definitionsFromDocument admitted.document) position)) reverse))
      (result (nodes output))) :
    output = PlainBnfStructuredReverseDependencies.bucket input
        (nameAt (definitionsFromDocument admitted.document) position) admitted.authority.lexicalDeclarations ∧
      PlainBnfWakeFrontierExactness.occurrencePositions coordinate output =
        PlainBnfDependencyWorklist.dependents
          (productiveGrammar (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
          position := by
  have exactOutput := (reverse_execution_dependents_iff input _ _ reverse indexed _).mp executed
  have same := PlainBnfStructuredEnumeration.nodes_injective
    (PlainBnfTrieSourceExecution.result_injective exactOutput)
  subst output
  exact ⟨rfl, enumerated_dependency_positions admitted input enumerated coordinate liveRanks position⟩

#print axioms enumerated_productive_initialQueue
#print axioms enumerated_nullable_initialQueue
#print axioms reverse_execution_dependents_iff
#print axioms enumerated_reverse_execution_positions

end Mettapedia.GSLT.Parsing.PlainBnfControllerInputExecution
