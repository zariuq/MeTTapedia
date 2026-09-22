import Mettapedia.GSLT.Parsing.PlainBnfReverseIndexSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfStructuredDiscoveryGraph
import Mettapedia.GSLT.Parsing.PlainBnfWakeFrontierExactness

/-!
# Structured reverse-dependency buckets

The independent ordered bucket retains each complete ranked definition once
per matching reference occurrence. Reversal records the actual source's
prepend updates. The existing trie fold and its authored execution produce
exactly this structured list when started from the empty index.

Only the subsequent coordinate observation forgets reference multiplicity;
it targets the existing dependency worklist, not another lookup engine.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfStructuredReverseDependencies

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open PlainBnfStructuredDenotation (LexicalDeclaration Expression)
open PlainBnfReverseIndexSourceExecution (Item key node nodes reverseIndex occurrencesFor applyOccurrences)
open PlainBnfReferenceCollectionSourceExecution (grammarReferences)
open PlainBnfReverseReferencesSourceExecution (bucketCons emptyBucket dependents)
open PlainBnfGraphNameTrie (Trie lookup)
open PlainBnfTrieSourceExecution (scalarRelations result trie)
open PlainBnfStructuredDiscoveryGraph (Definitions names nameAt expressionAt NamesDisjoint Resolved)
open PlainBnfWakeSourceExecution (HeapItem heapItem Queues pending Ordered wake)
open PlainBnfWakeFrontierExactness (occurrencePositions readyCandidatePositions ExactMarks)

def bucket (input : List Item) (query : String) (lexicals : List LexicalDeclaration) : List Item :=
  (input.flatMap fun item =>
    List.replicate ((grammarReferences item.2.expression lexicals).count query) item).reverse

theorem bucket_node_occurrences (input : List Item) (query : String) (lexicals : List LexicalDeclaration) :
    (bucket input query lexicals).map node = (occurrencesFor input query lexicals).reverse := by
  simp [bucket, occurrencesFor, List.map_flatMap]

theorem nodes_fold (input : List Item) :
    nodes input = (input.map node).foldr bucketCons emptyBucket := by
  induction input with
  | nil => rfl
  | cons item rest ih => simp [nodes, ih]

theorem lookup_bucket (input : List Item) (query : String) (lexicals : List LexicalDeclaration) :
    dependents (lookup (key query) (reverseIndex input lexicals .empty)) =
      nodes (bucket input query lexicals) := by
  rw [PlainBnfReverseIndexSourceExecution.lookup_reverseIndex, PlainBnfGraphNameTrie.lookup_empty,
    nodes_fold, bucket_node_occurrences]
  cases occurrencesFor input query lexicals <;> simp [applyOccurrences, dependents]

theorem execution_lookup_bucket (input : List Item) (query : String) (lexicals : List LexicalDeclaration)
    (after : Trie SExpr)
    (executed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall input lexicals .empty) (result (trie after))) :
    dependents (lookup (key query) after) = nodes (bucket input query lexicals) := by
  rw [PlainBnfReverseIndexSourceExecution.execution_bucket_provenance input query lexicals .empty after executed,
    PlainBnfGraphNameTrie.lookup_empty, nodes_fold, bucket_node_occurrences]
  cases occurrencesFor input query lexicals <;> simp [applyOccurrences, dependents]

theorem execution_dependents_step_iff (input : List Item) (query : String)
    (lexicals : List LexicalDeclaration) (after : Trie SExpr)
    (executed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall input lexicals .empty) (result (trie after)))
    (target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Step (engineBasePremises scalarRelations) PlainBnfReverseReferencesSourceExecution.language
      (PlainBnfReverseReferencesSourceExecution.dependentsCall (lookup (key query) after)) target ↔
      target = result (nodes (bucket input query lexicals)) := by
  rw [PlainBnfReverseReferencesSourceExecution.dependents_step_iff,
    execution_lookup_bucket input query lexicals after executed]

theorem mem_bucket (input : List Item) (query : String) (lexicals : List LexicalDeclaration) (item : Item) :
    item ∈ bucket input query lexicals ↔
      item ∈ input ∧ query ∈ grammarReferences item.2.expression lexicals := by
  simp only [bucket, List.mem_reverse, List.mem_flatMap, List.mem_replicate]
  constructor
  · rintro ⟨other, present, positive, same⟩
    subst other
    exact ⟨present, List.count_pos_iff.mp (Nat.pos_of_ne_zero positive)⟩
  · rintro ⟨present, referenced⟩
    exact ⟨item, present, Nat.ne_of_gt (List.count_pos_iff.mpr referenced), rfl⟩

theorem bucket_length (input : List Item) (query : String) (lexicals : List LexicalDeclaration) :
    (bucket input query lexicals).length =
      (input.map fun item => (grammarReferences item.2.expression lexicals).count query).sum := by
  simp [bucket]

/-- Membership is obtained from the existing exact ordered incidence theorem,
not by assuming that name-based and position-based dependency tests coincide. -/
theorem reference_iff_dependent (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (unique : (names definitions).Nodup) (disjoint : NamesDisjoint definitions lexicals)
    (resolved : ∀ position, Resolved definitions lexicals (expressionAt definitions position).referenceNames)
    (source target : Fin definitions.length) :
    nameAt definitions source ∈ grammarReferences (expressionAt definitions target) lexicals ↔
      target ∈ PlainBnfDependencyWorklist.dependents
        (PlainBnfStructuredDiscoveryGraph.productiveGrammar definitions lexicals) source := by
  have namesInjective := PlainBnfStructuredDiscoveryGraph.nameAt_injective definitions unique
  have occurrenceLaw := PlainBnfStructuredDiscoveryGraph.incidence_occurrences_exact
    definitions lexicals disjoint resolved
  have left : (nameAt definitions source, nameAt definitions target) ∈
      (PlainBnfDependencyWorklist.referenceEdges
        (PlainBnfStructuredDiscoveryGraph.productiveGrammar definitions lexicals)).map
        (fun edge => (nameAt definitions edge.1, nameAt definitions edge.2)) ↔
      (source, target) ∈ PlainBnfDependencyWorklist.referenceEdges
        (PlainBnfStructuredDiscoveryGraph.productiveGrammar definitions lexicals) := by
    constructor
    · rintro member
      obtain ⟨⟨first, second⟩, present, same⟩ := List.mem_map.mp member
      have firstEq := namesInjective (Prod.mk.inj same).1
      have secondEq := namesInjective (Prod.mk.inj same).2
      change first = source at firstEq
      change second = target at secondEq
      subst first
      subst second
      exact present
    · intro member
      exact List.mem_map.mpr ⟨(source, target), member, rfl⟩
  rw [occurrenceLaw] at left
  have right : (nameAt definitions source, nameAt definitions target) ∈
      (List.finRange definitions.length).flatMap (fun position =>
        (grammarReferences (expressionAt definitions position) lexicals).map
          (fun query => (query, nameAt definitions position))) ↔
      nameAt definitions source ∈ grammarReferences (expressionAt definitions target) lexicals := by
    constructor
    · intro member
      obtain ⟨position, _, inside⟩ := List.mem_flatMap.mp member
      obtain ⟨query, referenced, same⟩ := List.mem_map.mp inside
      have positionEq := namesInjective (Prod.mk.inj same).2
      subst position
      rwa [(Prod.mk.inj same).1] at referenced
    · intro referenced
      exact List.mem_flatMap.mpr ⟨target, by simp, List.mem_map.mpr
        ⟨nameAt definitions source, referenced, rfl⟩⟩
  rw [← right, left, PlainBnfDependencyWorklist.mem_referenceEdges,
    PlainBnfDependencyWorklist.mem_dependents]

/-- Full payload alignment and coordinate coverage are supplied by admitted
source enumeration; rank-shaped data alone is not treated as that proof. -/
theorem bucket_positions (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (unique : (names definitions).Nodup) (disjoint : NamesDisjoint definitions lexicals)
    (resolved : ∀ position, Resolved definitions lexicals (expressionAt definitions position).referenceNames)
    (input : List Item) (coordinate : HeapItem → Fin definitions.length)
    (aligned : ∀ item ∈ input, item.2 = definitions.get (coordinate (heapItem item)))
    (covers : ∀ position, ∃ item ∈ input, coordinate (heapItem item) = position)
    (source : Fin definitions.length) :
    occurrencePositions coordinate (bucket input (nameAt definitions source) lexicals) =
      PlainBnfDependencyWorklist.dependents
        (PlainBnfStructuredDiscoveryGraph.productiveGrammar definitions lexicals) source := by
  ext target
  simp only [occurrencePositions, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨item, member, same⟩
    obtain ⟨present, referenced⟩ := (mem_bucket input _ lexicals item).mp member
    have payload := congrArg (fun definition : PlainBnfReverseIndexSourceExecution.Definition =>
      definition.expression) (aligned item present)
    change item.2.expression = expressionAt definitions (coordinate (heapItem item)) at payload
    rw [payload, same] at referenced
    exact (reference_iff_dependent definitions lexicals unique disjoint resolved source target).mp referenced
  · intro dependent
    have referenced := (reference_iff_dependent definitions lexicals unique disjoint resolved source target).mpr dependent
    obtain ⟨item, present, same⟩ := covers target
    refine ⟨item, (mem_bucket input _ lexicals item).mpr ⟨present, ?_⟩, same⟩
    have payload := congrArg (fun definition : PlainBnfReverseIndexSourceExecution.Definition =>
      definition.expression) (aligned item present)
    change item.2.expression = expressionAt definitions (coordinate (heapItem item)) at payload
    rwa [payload, same]

theorem admitted_bucket_positions (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (input : List Item)
    (coordinate : HeapItem → Fin (PlainBnfStructuredDiscoveryGraph.definitionsFromDocument admitted.document).length)
    (aligned : ∀ item ∈ input, item.2 =
      (PlainBnfStructuredDiscoveryGraph.definitionsFromDocument admitted.document).get (coordinate (heapItem item)))
    (covers : ∀ position, ∃ item ∈ input, coordinate (heapItem item) = position)
    (source : Fin (PlainBnfStructuredDiscoveryGraph.definitionsFromDocument admitted.document).length) :
    occurrencePositions coordinate (bucket input
      (nameAt (PlainBnfStructuredDiscoveryGraph.definitionsFromDocument admitted.document) source)
      admitted.authority.lexicalDeclarations) =
      PlainBnfDependencyWorklist.dependents
        (PlainBnfStructuredDiscoveryGraph.productiveGrammar
          (PlainBnfStructuredDiscoveryGraph.definitionsFromDocument admitted.document)
          admitted.authority.lexicalDeclarations) source :=
  bucket_positions _ _ (PlainBnfStructuredDiscoveryGraph.admitted_definition_names_unique admitted)
    (PlainBnfStructuredDiscoveryGraph.admitted_names_disjoint admitted)
    (PlainBnfStructuredDiscoveryGraph.admitted_references_resolved admitted)
    input coordinate aligned covers source

/-- Productivity and nullability use the same dependency incidence; their
leaf decisions differ, not their ordered reference occurrences. -/
theorem nullable_dependents_eq (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (source : Fin definitions.length) :
    PlainBnfDependencyWorklist.dependents (PlainBnfStructuredDiscoveryGraph.nullableGrammar definitions) source =
      PlainBnfDependencyWorklist.dependents
        (PlainBnfStructuredDiscoveryGraph.productiveGrammar definitions lexicals) source := by
  ext target
  rw [PlainBnfDependencyWorklist.mem_dependents, PlainBnfDependencyWorklist.mem_dependents]
  have references := PlainBnfStructuredDiscoveryGraph.productive_nullable_same_references
    definitions lexicals (expressionAt definitions target)
  have membership := congrArg (fun entries => source ∈ entries) references
  change ((PlainBnfStructuredDiscoveryGraph.nullableExpression definitions
    (expressionAt definitions target)).any (fun alternative => alternative.references.contains source) = true) ↔
      ((PlainBnfStructuredDiscoveryGraph.productiveExpression definitions lexicals
        (expressionAt definitions target)).any (fun alternative => alternative.references.contains source) = true)
  rw [List.any_eq_true, List.any_eq_true]
  simpa only [List.mem_flatMap, List.contains_iff_mem] using Iff.of_eq membership.symm

private theorem ready_positions_excluding_published {size : Nat}
    (coordinate : HeapItem → Fin size) (input : List Item) (ready : Expression → Bool)
    (known : PlainBnfOrderedGraphDiscovery.Known size) (published : Finset (Fin size))
    (publishedMeaning : ∀ position, position ∈ published ↔ known position = true)
    (positionReady : Fin size → Bool)
    (agreement : ∀ item ∈ input,
      (!known (coordinate (heapItem item)) && ready item.2.expression) = positionReady (coordinate (heapItem item))) :
    readyCandidatePositions coordinate ready input \ published =
      (occurrencePositions coordinate input).filter (fun position => positionReady position) := by
  ext position
  simp only [Finset.mem_sdiff, readyCandidatePositions, occurrencePositions, List.mem_toFinset,
    List.mem_map, List.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨⟨item, ⟨inside, enabled⟩, same⟩, unpublished⟩
    refine ⟨⟨item, inside, same⟩, ?_⟩
    have notKnown : known position = false := by
      cases value : known position with
      | false => rfl
      | true => exact False.elim (unpublished ((publishedMeaning position).mpr value))
    have exactReady := agreement item inside
    rw [same, notKnown, enabled] at exactReady
    exact exactReady.symm
  · rintro ⟨⟨item, inside, same⟩, enabled⟩
    have exactReady := agreement item inside
    rw [same, enabled] at exactReady
    have components : (!known position) = true ∧ ready item.2.expression = true := by
      simpa only [Bool.and_eq_true] using exactReady
    refine ⟨⟨item, ⟨inside, components.2⟩, same⟩, ?_⟩
    intro publishedPosition
    rw [(publishedMeaning position).mp publishedPosition] at components
    simp at components

/-- One publication's Wake has the existing worklist refresh frontier. The
caller supplies the actual post-pop pending erasure and the independently
proved expression/known-history readiness correspondence. -/
theorem wake_refresh_frontier (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (unique : (names definitions).Nodup) (disjoint : NamesDisjoint definitions lexicals)
    (resolved : ∀ position, Resolved definitions lexicals (expressionAt definitions position).referenceNames)
    (input : List Item) (coordinate : HeapItem → Fin definitions.length)
    (aligned : ∀ item ∈ input, item.2 = definitions.get (coordinate (heapItem item)))
    (covers : ∀ position, ∃ item ∈ input, coordinate (heapItem item) = position)
    (source : Fin definitions.length) (origin : Option PlainBnfSourceRank.Rank)
    (grammar : PlainBnfOrderedGraphDiscovery.Grammar definitions.length)
    (sameDependencies : PlainBnfDependencyWorklist.dependents grammar source =
      PlainBnfDependencyWorklist.dependents
        (PlainBnfStructuredDiscoveryGraph.productiveGrammar definitions lexicals) source)
    (known : PlainBnfOrderedGraphDiscovery.Known definitions.length)
    (published : Finset (Fin definitions.length)) (ready : Expression → Bool) (queues : Queues)
    (ordered : Ordered queues)
    (marks : ExactMarks coordinate (fun position => key (nameAt definitions position)) published queues)
    (publishedMeaning : ∀ position, position ∈ published ↔
      PlainBnfOrderedGraphDiscovery.publish known source position = true)
    (oldPending : pending coordinate queues =
      (PlainBnfDependencyWorklist.initialQueue grammar known).erase source)
    (readiness : ∀ item ∈ input,
      (!PlainBnfOrderedGraphDiscovery.publish known source (coordinate (heapItem item)) && ready item.2.expression) =
        PlainBnfOrderedGraphDiscovery.ready grammar
          (PlainBnfOrderedGraphDiscovery.publish known source) (coordinate (heapItem item))) :
    pending coordinate (wake ready origin (bucket input (nameAt definitions source) lexicals) queues) =
      PlainBnfDependencyWorklist.initialQueue grammar
        (PlainBnfOrderedGraphDiscovery.publish known source) := by
  have namesInjective : Function.Injective (fun position => key (nameAt definitions position)) :=
    PlainBnfReverseIndexSourceExecution.key_injective.comp
      (PlainBnfStructuredDiscoveryGraph.nameAt_injective definitions unique)
  have bucketAligned : ∀ item ∈ bucket input (nameAt definitions source) lexicals,
      key (nameAt definitions (coordinate (heapItem item))) = key item.2.name := by
    intro item inside
    have payload := aligned item ((mem_bucket input _ lexicals item).mp inside).1
    have nameEq := congrArg (fun definition : PlainBnfReverseIndexSourceExecution.Definition => definition.name) payload
    exact congrArg key nameEq.symm
  rw [PlainBnfWakeFrontierExactness.wake_pending_unpublished coordinate _ namesInjective
    ready origin _ queues published ordered marks bucketAligned]
  rw [ready_positions_excluding_published coordinate _ ready
    (PlainBnfOrderedGraphDiscovery.publish known source) published publishedMeaning _
    (fun item member => readiness item ((mem_bucket input _ lexicals item).mp member).1),
    bucket_positions definitions lexicals unique disjoint resolved input coordinate aligned covers source,
    ← sameDependencies, oldPending]
  have exactRefresh := PlainBnfDependencyWorklist.refresh_exact grammar known source
  simpa [PlainBnfDependencyWorklist.refresh, PlainBnfDependencyWorklist.dependents,
    PlainBnfDependencyWorklist.incidence] using exactRefresh

theorem bucket_two_source_order (first second : Item) (query : String)
    (lexicals : List LexicalDeclaration) :
    bucket [first, second] query lexicals =
      List.replicate ((grammarReferences second.2.expression lexicals).count query) second ++
      List.replicate ((grammarReferences first.2.expression lexicals).count query) first := by
  simp [bucket, List.reverse_append]

theorem duplicate_reference_retained (item : Item) (query : String)
    (lexicals : List LexicalDeclaration)
    (twice : (grammarReferences item.2.expression lexicals).count query = 2) :
    bucket [item] query lexicals = [item, item] := by
  simp [bucket, twice]

theorem reversing_bucket_is_not_authorized (first second : Item) (query : String)
    (lexicals : List LexicalDeclaration) (different : first ≠ second)
    (firstOnce : (grammarReferences first.2.expression lexicals).count query = 1)
    (secondOnce : (grammarReferences second.2.expression lexicals).count query = 1) :
    bucket [first, second] query lexicals ≠ [first, second] := by
  rw [bucket_two_source_order, firstOnce, secondOnce]
  simp [List.replicate_succ, Ne.symm different]

theorem lexical_query_has_empty_bucket (input : List Item) (query : String)
    (lexicals : List LexicalDeclaration)
    (lexical : lexicals.any (·.referenceName == query) = true) :
    bucket input query lexicals = [] := by
  have observed := bucket_node_occurrences input query lexicals
  rw [PlainBnfReverseIndexSourceExecution.lexical_name_has_no_bucket_occurrences
    input query lexicals lexical] at observed
  exact List.map_eq_nil_iff.mp observed

end Mettapedia.GSLT.Parsing.PlainBnfStructuredReverseDependencies
