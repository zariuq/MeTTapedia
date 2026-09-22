import Mettapedia.GSLT.Parsing.PlainBnfControllerInputExecution

/-!
# Actual controller Wake after publication

The two discovery modes select their existing graph observations. Actual
enumeration supplies full candidate alignment and coverage; actual reverse
indexing and the controller's dependent-list call supply the ordered bucket.
The returned packet of the controller's post-publication Wake then has exactly
the new graph frontier and preserves the scheduled-mark invariant.

Post-pop heap order, pending erasure, exact marks, live rank coordinates,
known-index validity, and scoped history remain explicit controller premises.
No whole-loop termination, native realization, or default rank decoding is
asserted. The finite-set conclusion does not replace the ordered bucket or
erase its complete source payload occurrences.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerPublicationFrontier

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open PlainBnfStructuredDenotation (LexicalDeclaration)
open PlainBnfReferenceCollectionSourceExecution (text)
open PlainBnfTrieSourceExecution (scalarRelations result trie)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfReverseIndexSourceExecution (Item key nodes)
open PlainBnfStructuredDiscoveryGraph
open PlainBnfStructuredEnumeration (wireDefinition candidates)
open PlainBnfSourceRank (Rank value)
open PlainBnfWakeSourceExecution (HeapItem heapItem Queues Ordered pending encodeQueues)
open PlainBnfWakeFrontierExactness (ExactMarks)
open PlainBnfWakeContextualExecution (NameIndex meaning wakeCall)

/-- A proof observation selecting the two already defined graphs, not a
new source or runtime grammar representation. -/
def graph (productive : Bool) (definitions : Definitions)
    (lexicals : List LexicalDeclaration) :
    PlainBnfOrderedGraphDiscovery.Grammar definitions.length :=
  if productive then productiveGrammar definitions lexicals else nullableGrammar definitions

theorem graph_dependents (productive : Bool) (definitions : Definitions)
    (lexicals : List LexicalDeclaration) (position : Fin definitions.length) :
    PlainBnfDependencyWorklist.dependents (graph productive definitions lexicals) position =
      PlainBnfDependencyWorklist.dependents (productiveGrammar definitions lexicals) position := by
  cases productive with
  | false => exact PlainBnfStructuredReverseDependencies.nullable_dependents_eq definitions lexicals position
  | true => rfl

/-- Known-name exclusion is separate from the expression decision in both
source modes. Publication does not make an already known rule ready again. -/
theorem graph_ready_exact (productive : Bool) (definitions : Definitions)
    (history : List SExpr) (lexicals : List LexicalDeclaration)
    (historyScoped : HistoryScoped definitions history)
    (disjoint : NamesDisjoint definitions lexicals) (position : Fin definitions.length) :
    PlainBnfOrderedGraphDiscovery.ready (graph productive definitions lexicals)
      (graphKnown definitions history) position =
      (!graphKnown definitions history position &&
        meaning productive history lexicals (expressionAt definitions position)) := by
  cases productive with
  | false => exact nullable_ready_exact definitions history historyScoped position
  | true => exact productive_ready_exact definitions history lexicals historyScoped disjoint position

/-- The readiness equation needed by refresh follows from publication of the
actual name in the existing history. No ready-answer provider is assumed. -/
theorem published_readiness_exact (productive : Bool) (definitions : Definitions)
    (lexicals : List LexicalDeclaration) (unique : (names definitions).Nodup)
    (disjoint : NamesDisjoint definitions lexicals) (history : List SExpr)
    (historyScoped : HistoryScoped definitions history) (position target : Fin definitions.length) :
    (!PlainBnfOrderedGraphDiscovery.publish (graphKnown definitions history) position target &&
      meaning productive (text (nameAt definitions position) :: history) lexicals
        (expressionAt definitions target)) =
      PlainBnfOrderedGraphDiscovery.ready (graph productive definitions lexicals)
        (PlainBnfOrderedGraphDiscovery.publish (graphKnown definitions history) position) target := by
  rw [← graphKnown_publish definitions unique history position]
  exact (graph_ready_exact productive definitions _ lexicals
    (history_publish_scoped definitions history historyScoped position) disjoint target).symm

/-- Both actual controller modes return the precise graph frontier after one
publication. The dependent bucket remains an exact ordered source result;
only its queue-position observation is a finite set. -/
theorem execution_publication_frontier
    (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (input dependentsInput : List Item)
    (enumerated : Step (engineBasePremises scalarRelations) PlainBnfEnumerationSourceExecution.language
      (PlainBnfEnumerationSourceExecution.enumerationCall
        ((definitionsFromDocument admitted.document).map wireDefinition) .zero) (result (nodes input)))
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (liveRanks : ∀ item ∈ input, (coordinate (heapItem item)).val = value item.1)
    (position : Fin (definitionsFromDocument admitted.document).length)
    (history : List SExpr)
    (historyScoped : HistoryScoped (definitionsFromDocument admitted.document) history)
    (index reverse : NameIndex)
    (valid : PlainBnfKnownNamesSourceExecution.Valid index
      (text (nameAt (definitionsFromDocument admitted.document) position) :: history))
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall input admitted.authority.lexicalDeclarations .empty)
      (result (trie reverse)))
    (dependentExecution : Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (PlainBnfReverseReferencesSourceExecution.dependentsCall
        (PlainBnfGraphNameTrie.lookup (key (nameAt (definitionsFromDocument admitted.document) position)) reverse))
      (result (nodes dependentsInput)))
    (origin : Option Rank) (before after : Queues) (ordered : Ordered before)
    (marks : ExactMarks coordinate (fun p => key (nameAt (definitionsFromDocument admitted.document) p))
      (Finset.univ.filter (fun p => graphKnown (definitionsFromDocument admitted.document)
        (text (nameAt (definitionsFromDocument admitted.document) position) :: history) p)) before)
    (oldPending : pending coordinate before =
      (PlainBnfDependencyWorklist.initialQueue
        (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
        (graphKnown (definitionsFromDocument admitted.document) history)).erase position)
    (executed : Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (wakeCall productive dependentsInput origin index
        (text (nameAt (definitionsFromDocument admitted.document) position) :: history)
        admitted.authority.lexicalDeclarations before) (result (encodeQueues after))) :
    dependentsInput = PlainBnfStructuredReverseDependencies.bucket input
      (nameAt (definitionsFromDocument admitted.document) position) admitted.authority.lexicalDeclarations ∧
    pending coordinate after =
      PlainBnfDependencyWorklist.initialQueue
        (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
        (graphKnown (definitionsFromDocument admitted.document)
          (text (nameAt (definitionsFromDocument admitted.document) position) :: history)) ∧
      ExactMarks coordinate (fun p => key (nameAt (definitionsFromDocument admitted.document) p))
        (Finset.univ.filter (fun p => graphKnown (definitionsFromDocument admitted.document)
          (text (nameAt (definitionsFromDocument admitted.document) position) :: history) p)) after := by
  have actualInput := (PlainBnfStructuredEnumeration.source_decoded_step_iff
    scalarRelations _ input).mp enumerated
  subst input
  have actualDependents := (PlainBnfControllerInputExecution.reverse_execution_dependents_iff
    (candidates _) _ _ reverse indexed _).mp dependentExecution
  have exactBucket := PlainBnfStructuredEnumeration.nodes_injective
    (PlainBnfTrieSourceExecution.result_injective actualDependents)
  subst dependentsInput
  have wakeExecuted := (PlainBnfRunSourceFamily.wake_step_iff _ _ (by rfl)).mp executed
  have actualQueues := (PlainBnfWakeContextualExecution.wake_queues_step_iff
    productive _ origin index _ admitted.authority.lexicalDeclarations before valid after).mp wakeExecuted
  have alignment := PlainBnfStructuredEnumeration.coordinate_payload
    (definitionsFromDocument admitted.document) coordinate liveRanks
  have coverage := PlainBnfStructuredEnumeration.coordinate_coverage
    (definitionsFromDocument admitted.document) coordinate liveRanks
  have publication := graphKnown_publish (definitionsFromDocument admitted.document)
    (admitted_definition_names_unique admitted) history position
  have namesInjective : Function.Injective
      (fun p => key (nameAt (definitionsFromDocument admitted.document) p)) :=
    PlainBnfReverseIndexSourceExecution.key_injective.comp
      (nameAt_injective _ (admitted_definition_names_unique admitted))
  have bucketNames : ∀ item ∈ PlainBnfStructuredReverseDependencies.bucket
      (candidates (definitionsFromDocument admitted.document))
      (nameAt (definitionsFromDocument admitted.document) position) admitted.authority.lexicalDeclarations,
      key (nameAt (definitionsFromDocument admitted.document) (coordinate (heapItem item))) = key item.2.name := by
    intro item inside
    exact congrArg key (PlainBnfStructuredEnumeration.coordinate_names _ coordinate liveRanks item
      ((PlainBnfStructuredReverseDependencies.mem_bucket _ _ _ item).mp inside).1)
  have retainedMarks := (PlainBnfWakeOperationalFrontier.execution_frontier productive _ origin
    index _ admitted.authority.lexicalDeclarations before after valid coordinate _ namesInjective _
    ordered marks bucketNames wakeExecuted).2
  refine ⟨rfl, ?_, retainedMarks⟩
  rw [actualQueues, publication]
  apply PlainBnfStructuredReverseDependencies.wake_refresh_frontier
    (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations
    (admitted_definition_names_unique admitted) (admitted_names_disjoint admitted)
    (admitted_references_resolved admitted) (candidates _) coordinate
    (fun item member => (alignment item member).symm) coverage position origin
    (graph productive _ _) (graph_dependents productive _ _ position)
    (graphKnown _ history)
    (Finset.univ.filter (fun p => graphKnown (definitionsFromDocument admitted.document)
      (text (nameAt (definitionsFromDocument admitted.document) position) :: history) p))
    (meaning productive _ admitted.authority.lexicalDeclarations) before ordered marks
  · intro p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, publication]
  · exact oldPending
  · intro item member
    rw [← PlainBnfStructuredEnumeration.coordinate_expressions _ coordinate liveRanks item member]
    exact published_readiness_exact productive _ admitted.authority.lexicalDeclarations
      (admitted_definition_names_unique admitted) (admitted_names_disjoint admitted)
      history historyScoped position (coordinate (heapItem item))

/-- The frontier proved above never requeues the just-published position,
even if its expression remains ready or contains a self-reference. -/
theorem published_position_not_in_frontier (productive : Bool) (definitions : Definitions)
    (lexicals : List LexicalDeclaration) (history : List SExpr)
    (position : Fin definitions.length) :
    position ∉ PlainBnfDependencyWorklist.initialQueue (graph productive definitions lexicals)
      (graphKnown definitions (text (nameAt definitions position) :: history)) := by
  simp [PlainBnfDependencyWorklist.initialQueue, PlainBnfOrderedGraphDiscovery.ready,
    graphKnown, PlainBnfProductiveSourceExecution.member]

/-- A stale scheduled mark cannot be justified by an otherwise empty
post-pop queue. It is excluded by the explicit exact-mark premise. -/
theorem stale_mark_refuses_empty_postpublication
    (definitions : Definitions) (unique : (names definitions).Nodup)
    (coordinate : HeapItem → Fin definitions.length) (history : List SExpr)
    (position target : Fin definitions.length) (different : target ≠ position)
    (unknown : graphKnown definitions history target = false)
    (scheduled : PlainBnfGraphNameTrie.Trie SExpr)
    (stale : PlainBnfGraphNameTrie.lookup (key (nameAt definitions target)) scheduled ≠ none) :
    ¬ ExactMarks coordinate (fun p => key (nameAt definitions p))
      (Finset.univ.filter (fun p => graphKnown definitions
        (text (nameAt definitions position) :: history) p)) (.nil, .nil, scheduled) := by
  intro exactMarks
  have marked : target ∈ PlainBnfWakeFrontierExactness.scheduledPositions
      (fun p => key (nameAt definitions p)) scheduled := by
    simpa only [PlainBnfWakeFrontierExactness.scheduledPositions,
      Finset.mem_filter, Finset.mem_univ, true_and] using stale
  rw [exactMarks] at marked
  have published := graphKnown_publish definitions unique history position
  simp [PlainBnfWakeSourceExecution.pending, PlainBnfTwoHeapWorklist.positions_nil,
    published, PlainBnfOrderedGraphDiscovery.publish, different, unknown] at marked

private def controlSpan : PlainBnfStructuredDenotation.SourceSpan := { start := 0, stop := 1 }

private def controlExpression (elements : List PlainBnfStructuredDenotation.Element) :
    PlainBnfStructuredDenotation.Expression :=
  { alternatives := [{ elements, span := controlSpan }], span := controlSpan }

private abbrev controlDefinitions : Definitions :=
  [⟨"seed", controlExpression [], controlSpan⟩,
   ⟨"dependent", controlExpression [.reference "seed" controlSpan, .reference "seed" controlSpan], controlSpan⟩,
   ⟨"literal", controlExpression [.literal "x" controlSpan], controlSpan⟩]

/-- Both modes wake the dependent after publication, including its repeated
reference occurrences. A nonempty literal distinguishes the two modes. -/
theorem both_modes_publication_control :
    PlainBnfDependencyWorklist.initialQueue (graph true controlDefinitions [])
      (graphKnown controlDefinitions []) = {0, 2} ∧
    PlainBnfDependencyWorklist.initialQueue (graph false controlDefinitions [])
      (graphKnown controlDefinitions []) = {0} ∧
    PlainBnfDependencyWorklist.initialQueue (graph true controlDefinitions [])
      (graphKnown controlDefinitions [text "seed"]) = {1, 2} ∧
    PlainBnfDependencyWorklist.initialQueue (graph false controlDefinitions [])
      (graphKnown controlDefinitions [text "seed"]) = {1} := by
  have emptyKnown : graphKnown controlDefinitions [] = fun _ => false := rfl
  have publishedKnown := graphKnown_publish controlDefinitions (by decide) [] 0
  change graphKnown controlDefinitions [text "seed"] =
    PlainBnfOrderedGraphDiscovery.publish (graphKnown controlDefinitions []) 0 at publishedKnown
  rw [publishedKnown, emptyKnown]
  decide

theorem replacing_nullable_by_productive_changes_frontier :
    PlainBnfDependencyWorklist.initialQueue (graph false controlDefinitions [])
      (graphKnown controlDefinitions [text "seed"]) ≠
    PlainBnfDependencyWorklist.initialQueue (graph true controlDefinitions [])
      (graphKnown controlDefinitions [text "seed"]) := by
  rw [both_modes_publication_control.2.2.1, both_modes_publication_control.2.2.2]
  decide

end Mettapedia.GSLT.Parsing.PlainBnfControllerPublicationFrontier
