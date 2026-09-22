import Mettapedia.GSLT.Parsing.PlainBnfEnumerationSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfWakeGraphInitialization

/-!
# Structured definitions through the authored source enumeration

The String/expression/span carrier is encoded using the existing source
codecs. Its indexed candidate list is a typed view of the existing proved
enumeration, not another executable enumerator. Coordinates are constrained
only on actual returned candidates; no default coordinate for malformed
ranked values is constructed. Source execution and graph initialization are
composed at their existing observations, without a native-runtime claim.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfStructuredEnumeration

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises rewriteAt)
open PlainBnfStructuredDenotation (SourceSpan Element Alternative Expression LexicalDeclaration)
open PlainBnfStructuredDiscoveryGraph
open PlainBnfSourceRank (Rank value successor)
open PlainBnfEnumerationSourceExecution (enumerate value_iterate enumerationCall enumerationHeight language)
open PlainBnfRankSourceExecution (result)
open PlainBnfReverseIndexSourceExecution (Item nodes)
open PlainBnfReferenceCollectionSourceExecution (text span element elements alternative alternatives expression)
open PlainBnfWakeSourceExecution (HeapItem heapItem wake pending)

theorem span_injective : Function.Injective span := by
  rintro ⟨ls, le⟩ ⟨rs, re⟩ same
  simp only [span, SExpr.list.injEq, List.cons.injEq, true_and, and_true, SExpr.atom.injEq] at same
  obtain ⟨sameStart, sameStop⟩ := same
  have start := Nat.repr_injective sameStart
  have stop := Nat.repr_injective sameStop
  subst rs
  subst re
  rfl

theorem element_injective : Function.Injective element := by
  intro left right same
  cases left <;> cases right <;>
    simp only [element, SExpr.list.injEq, List.cons.injEq, and_true, SExpr.atom.injEq] at same
  all_goals first
    | obtain ⟨_, names, locations⟩ := same
      cases PlainBnfReferenceCollectionSourceExecution.text_injective names
      cases span_injective locations
      rfl
    | simp at same

theorem elements_injective : Function.Injective elements := by
  intro left
  induction left with
  | nil => intro right same; cases right <;> simp_all [elements]
  | cons head tail ih =>
      intro right same
      cases right with
      | nil => simp [elements] at same
      | cons first rest =>
          simp only [elements, SExpr.list.injEq, List.cons.injEq, true_and, and_true] at same
          exact congrArg₂ List.cons (element_injective same.1) (ih same.2)

theorem alternative_injective : Function.Injective alternative := by
  rintro ⟨left, ls⟩ ⟨right, rs⟩ same
  simp only [alternative, SExpr.list.injEq, List.cons.injEq, true_and, and_true] at same
  cases elements_injective same.1
  cases span_injective same.2
  rfl

theorem alternatives_injective : Function.Injective alternatives := by
  intro left
  induction left with
  | nil => intro right same; cases right <;> simp_all [alternatives]
  | cons head tail ih =>
      intro right same
      cases right with
      | nil => simp [alternatives] at same
      | cons first rest =>
          simp only [alternatives, SExpr.list.injEq, List.cons.injEq, true_and, and_true] at same
          exact congrArg₂ List.cons (alternative_injective same.1) (ih same.2)

theorem expression_injective : Function.Injective expression := by
  rintro ⟨left, ls⟩ ⟨right, rs⟩ same
  simp only [expression, SExpr.list.injEq, List.cons.injEq, true_and, and_true] at same
  cases alternatives_injective same.1
  cases span_injective same.2
  rfl

def wireDefinition (definition : Definition) : PlainBnfEnumerationSourceExecution.Definition :=
  ⟨text definition.name, expression definition.expression, span definition.span⟩

theorem wireDefinition_injective : Function.Injective wireDefinition := by
  rintro ⟨ln, le, ls⟩ ⟨rn, re, rs⟩ same
  have names := PlainBnfReferenceCollectionSourceExecution.text_injective
    (congrArg PlainBnfDeclarationSemantics.Definition.name same)
  have expressions := expression_injective (congrArg PlainBnfDeclarationSemantics.Definition.expression same)
  have spans := span_injective (congrArg PlainBnfDeclarationSemantics.Definition.span same)
  cases names
  cases expressions
  cases spans
  rfl

def wireItem (item : Item) : Rank × PlainBnfEnumerationSourceExecution.Definition :=
  (item.1, wireDefinition item.2)

theorem wireItem_injective : Function.Injective wireItem := by
  rintro ⟨lr, ld⟩ ⟨rr, rd⟩ same
  have ranks := congrArg Prod.fst same
  have definitions := wireDefinition_injective (congrArg Prod.snd same)
  cases ranks
  cases definitions
  rfl

theorem heapItem_wireItem (item : Item) : heapItem item = wireItem item := rfl

theorem nodes_wire (input : List Item) :
    nodes input = PlainBnfEnumerationSourceExecution.rankedDefinitions (input.map wireItem) := by
  induction input with
  | nil => rfl
  | cons head tail ih =>
      simp only [nodes, List.map_cons, PlainBnfEnumerationSourceExecution.rankedDefinitions, ih]
      rfl

theorem nodes_injective : Function.Injective nodes := by
  intro left right same
  rw [nodes_wire, nodes_wire] at same
  exact (List.map_inj_right (fun _ _ h => wireItem_injective h)).mp
    (PlainBnfEnumerationSourceExecution.rankedDefinitions_injective same)

/-- Source-indexed typed view, with its exact encoded-enumeration equation below. -/
def candidates (definitions : Definitions) : List Item :=
  definitions.zipIdx.map fun (definition, index) => ((successor^[index]) Rank.zero, definition)

theorem candidates_wire (definitions : Definitions) :
    (candidates definitions).map wireItem = enumerate (definitions.map wireDefinition) .zero := by
  simp only [candidates, enumerate, List.zipIdx_map, List.map_map]
  rfl

theorem candidates_payloads (definitions : Definitions) :
    (candidates definitions).map Prod.snd = definitions := by
  simp only [candidates, List.map_map]
  exact List.zipIdx_map_fst 0 definitions

theorem candidates_coordinates (definitions : Definitions) :
    (candidates definitions).map (fun item => (value item.1, item.2)) =
      definitions.zipIdx.map (fun item => (item.2, item.1)) := by
  simp [candidates, List.map_map, value_iterate, value]

theorem source_answers (env : RelationEnv) (fuel : Nat) (definitions : Definitions) :
    rewriteAt (engineBasePremises env) language fuel
      (enumerationCall (definitions.map wireDefinition) .zero) =
      if enumerationHeight (definitions.map wireDefinition) .zero < fuel then
        [result (nodes (candidates definitions))] else [] := by
  rw [PlainBnfEnumerationSourceExecution.enumeration_answers, nodes_wire, candidates_wire]

theorem source_step_iff (env : RelationEnv) (definitions : Definitions) (target : Pattern) :
    Step (engineBasePremises env) language
      (enumerationCall (definitions.map wireDefinition) .zero) target ↔
      target = result (nodes (candidates definitions)) := by
  rw [PlainBnfEnumerationSourceExecution.enumeration_step_iff, nodes_wire, candidates_wire]

theorem source_decoded_step_iff (env : RelationEnv) (definitions : Definitions) (output : List Item) :
    Step (engineBasePremises env) language
      (enumerationCall (definitions.map wireDefinition) .zero) (result (nodes output)) ↔
      output = candidates definitions := by
  rw [source_step_iff, PlainBnfEnumerationSourceExecution.result_injective.eq_iff, nodes_injective.eq_iff]

/-- Every live candidate retains its complete original declaration at its rank. -/
theorem candidate_position (definitions : Definitions) (item : Item) (member : item ∈ candidates definitions) :
    ∃ position : Fin definitions.length, value item.1 = position.val ∧ item.2 = definitions.get position := by
  obtain ⟨⟨definition, index⟩, inside, same⟩ := List.mem_map.mp member
  obtain ⟨bound, selected⟩ := List.mem_zipIdx' inside
  subst item
  refine ⟨⟨index, bound⟩, ?_, selected⟩
  simp [value_iterate, value]

theorem candidate_coverage (definitions : Definitions) (position : Fin definitions.length) :
    ∃ item ∈ candidates definitions, value item.1 = position.val ∧ item.2 = definitions.get position := by
  refine ⟨((successor^[position.val]) .zero, definitions.get position), ?_, ?_, rfl⟩
  · apply List.mem_map.mpr
    refine ⟨(definitions.get position, position.val), ?_, rfl⟩
    exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simp)
  · simp [value_iterate, value]

theorem coordinate_payload (definitions : Definitions) (coordinate : HeapItem → Fin definitions.length)
    (liveRanks : ∀ item ∈ candidates definitions, (coordinate (heapItem item)).val = value item.1)
    (item : Item) (member : item ∈ candidates definitions) :
    definitions.get (coordinate (heapItem item)) = item.2 := by
  obtain ⟨position, rankPosition, payload⟩ := candidate_position definitions item member
  have same : coordinate (heapItem item) = position := Fin.ext ((liveRanks item member).trans rankPosition)
  rw [same, payload]

theorem coordinate_coverage (definitions : Definitions) (coordinate : HeapItem → Fin definitions.length)
    (liveRanks : ∀ item ∈ candidates definitions, (coordinate (heapItem item)).val = value item.1)
    (position : Fin definitions.length) :
    ∃ item ∈ candidates definitions, coordinate (heapItem item) = position := by
  obtain ⟨item, member, same, _⟩ := candidate_coverage definitions position
  exact ⟨item, member, Fin.ext ((liveRanks item member).trans same)⟩

theorem coordinate_names (definitions : Definitions) (coordinate : HeapItem → Fin definitions.length)
    (liveRanks : ∀ item ∈ candidates definitions, (coordinate (heapItem item)).val = value item.1)
    (item : Item) (member : item ∈ candidates definitions) :
    nameAt definitions (coordinate (heapItem item)) = item.2.name :=
  congrArg PlainBnfDeclarationSemantics.Definition.name (coordinate_payload definitions coordinate liveRanks item member)

theorem coordinate_expressions (definitions : Definitions) (coordinate : HeapItem → Fin definitions.length)
    (liveRanks : ∀ item ∈ candidates definitions, (coordinate (heapItem item)).val = value item.1)
    (item : Item) (member : item ∈ candidates definitions) :
    expressionAt definitions (coordinate (heapItem item)) = item.2.expression :=
  congrArg PlainBnfDeclarationSemantics.Definition.expression
    (coordinate_payload definitions coordinate liveRanks item member)

/-- Full payload equality also retains the declaration span, not just its name. -/
theorem coordinate_spans (definitions : Definitions) (coordinate : HeapItem → Fin definitions.length)
    (liveRanks : ∀ item ∈ candidates definitions, (coordinate (heapItem item)).val = value item.1)
    (item : Item) (member : item ∈ candidates definitions) :
    (definitions.get (coordinate (heapItem item))).span = item.2.span :=
  congrArg PlainBnfDeclarationSemantics.Definition.span (coordinate_payload definitions coordinate liveRanks item member)

theorem execution_preserves_payloads (env : RelationEnv) (definitions : Definitions) (output : List Item)
    (executed : Step (engineBasePremises env) language
      (enumerationCall (definitions.map wireDefinition) .zero) (result (nodes output))) :
    output.map Prod.snd = definitions := by
  rw [(source_decoded_step_iff env definitions output).mp executed, candidates_payloads]

theorem execution_productive_initialQueue (env : RelationEnv)
    (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (unique : (names definitions).Nodup) (disjoint : NamesDisjoint definitions lexicals)
    (output : List Item)
    (executed : Step (engineBasePremises env) language
      (enumerationCall (definitions.map wireDefinition) .zero) (result (nodes output)))
    (coordinate : HeapItem → Fin definitions.length)
    (liveRanks : ∀ item ∈ output, (coordinate (heapItem item)).val = value item.1)
    (origin : Option Rank) :
    pending coordinate (wake (PlainBnfProductiveSourceExecution.expressionMeaning [] lexicals)
      origin output (.nil, .nil, .empty)) =
      PlainBnfDependencyWorklist.initialQueue (productiveGrammar definitions lexicals)
        (graphKnown definitions []) := by
  have exactOutput := (source_decoded_step_iff env definitions output).mp executed
  subst output
  exact PlainBnfWakeGraphInitialization.productive_empty_wake definitions lexicals unique disjoint
    coordinate origin (candidates definitions) (coordinate_names definitions coordinate liveRanks)
    (coordinate_expressions definitions coordinate liveRanks) (coordinate_coverage definitions coordinate liveRanks)

theorem execution_nullable_initialQueue (env : RelationEnv) (definitions : Definitions)
    (unique : (names definitions).Nodup) (output : List Item)
    (executed : Step (engineBasePremises env) language
      (enumerationCall (definitions.map wireDefinition) .zero) (result (nodes output)))
    (coordinate : HeapItem → Fin definitions.length)
    (liveRanks : ∀ item ∈ output, (coordinate (heapItem item)).val = value item.1)
    (origin : Option Rank) :
    pending coordinate (wake (PlainBnfNullableSourceExecution.expressionMeaning [])
      origin output (.nil, .nil, .empty)) =
      PlainBnfDependencyWorklist.initialQueue (nullableGrammar definitions) (graphKnown definitions []) := by
  have exactOutput := (source_decoded_step_iff env definitions output).mp executed
  subst output
  exact PlainBnfWakeGraphInitialization.nullable_empty_wake definitions unique
    coordinate origin (candidates definitions) (coordinate_names definitions coordinate liveRanks)
    (coordinate_expressions definitions coordinate liveRanks) (coordinate_coverage definitions coordinate liveRanks)

theorem admitted_execution_initialQueues (env : RelationEnv)
    (admitted : PlainBnfSemanticAdmission.AdmittedInput) (output : List Item)
    (executed : Step (engineBasePremises env) language
      (enumerationCall ((definitionsFromDocument admitted.document).map wireDefinition) .zero)
      (result (nodes output)))
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (liveRanks : ∀ item ∈ output, (coordinate (heapItem item)).val = value item.1)
    (origin : Option Rank) :
    pending coordinate (wake
      (PlainBnfProductiveSourceExecution.expressionMeaning [] admitted.authority.lexicalDeclarations)
      origin output (.nil, .nil, .empty)) =
      PlainBnfDependencyWorklist.initialQueue
        (productiveGrammar (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
        (graphKnown (definitionsFromDocument admitted.document) []) ∧
    pending coordinate (wake (PlainBnfNullableSourceExecution.expressionMeaning [])
      origin output (.nil, .nil, .empty)) =
      PlainBnfDependencyWorklist.initialQueue (nullableGrammar (definitionsFromDocument admitted.document))
        (graphKnown (definitionsFromDocument admitted.document) []) :=
  ⟨execution_productive_initialQueue env _ _ (admitted_definition_names_unique admitted)
      (admitted_names_disjoint admitted) output executed coordinate liveRanks origin,
    execution_nullable_initialQueue env _ (admitted_definition_names_unique admitted)
      output executed coordinate liveRanks origin⟩

/-- Two equal definition payloads remain two source positions and two nodes. -/
theorem repeated_payloads_survive (env : RelationEnv) (definition : Definition) :
    Step (engineBasePremises env) language
      (enumerationCall ([definition, definition].map wireDefinition) .zero)
      (result (nodes [(.zero, definition), (successor .zero, definition)])) := by
  rw [source_decoded_step_iff]
  rfl

theorem missing_payload_is_not_enumeration (env : RelationEnv) (definition : Definition) :
    ¬ Step (engineBasePremises env) language
      (enumerationCall ([definition, definition].map wireDefinition) .zero)
      (result (nodes [(.zero, definition)])) := by
  rw [source_decoded_step_iff]
  intro same
  have lengths := congrArg List.length same
  simp [candidates] at lengths

theorem reordered_ranks_are_not_enumeration (env : RelationEnv) (left right : Definition) :
    ¬ Step (engineBasePremises env) language
      (enumerationCall ([left, right].map wireDefinition) .zero)
      (result (nodes [(successor .zero, right), (.zero, left)])) := by
  rw [source_decoded_step_iff]
  intro same
  have ranks := congrArg (fun input => input.map (fun item => value item.1)) same
  simp [candidates, List.zipIdx_cons, successor, value] at ranks

theorem changed_span_is_not_enumeration (env : RelationEnv) (name : String)
    (body : Expression) (original changed : SourceSpan) (different : original ≠ changed) :
    ¬ Step (engineBasePremises env) language
      (enumerationCall ([⟨name, body, original⟩].map wireDefinition) .zero)
      (result (nodes [(.zero, ⟨name, body, changed⟩)])) := by
  intro executed
  have payloads := execution_preserves_payloads env _ _ executed
  have spans := congrArg (fun input => input.map PlainBnfDeclarationSemantics.Definition.span) payloads
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at spans
  exact different spans.symm

#print axioms source_answers
#print axioms source_decoded_step_iff
#print axioms candidates_coordinates
#print axioms coordinate_payload
#print axioms admitted_execution_initialQueues
#print axioms changed_span_is_not_enumeration

end Mettapedia.GSLT.Parsing.PlainBnfStructuredEnumeration
