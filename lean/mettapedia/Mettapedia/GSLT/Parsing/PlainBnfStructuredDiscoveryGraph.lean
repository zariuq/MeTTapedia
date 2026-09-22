import Mettapedia.GSLT.Parsing.PlainBnfReadinessSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfDependencyWorklist

/-!
# Structured plain-BNF views for ordered discovery

Definition positions retain admitted source order. Grammar references retain
their occurrence list; literal and lexical leaves supply the selected finite
productivity/nullability classification. The target is the existing ordered
graph carrier, not another syntax or execution language. Unknown names and
grammar/lexical collisions have explicit boundaries below.
This reference fold does not replace the authored sparse-trie implementation.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfStructuredDiscoveryGraph

open Algorithms.MeTTa.Simple.Parser (SExpr)
open PlainBnfStructuredDenotation (SourceSpan Element Alternative Expression LexicalDeclaration GrammarAuthority)
open PlainBnfReferenceCollectionSourceExecution (text firstDeclaration grammarReferences)

abbrev Definition := PlainBnfDeclarationSemantics.Definition String Expression SourceSpan
abbrev Definitions := List Definition

def names (definitions : Definitions) : List String := definitions.map (·.name)
def nameAt (definitions : Definitions) (position : Fin definitions.length) : String :=
  (definitions.get position).name
def expressionAt (definitions : Definitions) (position : Fin definitions.length) : Expression :=
  (definitions.get position).expression

/-- First source position with this exact name. No default position exists for
unknown names, and duplicate declarations are not silently merged. -/
def position? : (definitions : Definitions) → String → Option (Fin definitions.length)
  | [], _ => none
  | head :: tail, key =>
      if head.name = key then some 0 else (position? tail key).map Fin.succ

theorem position_some_name (definitions : Definitions) (key : String)
    (position : Fin definitions.length) (found : position? definitions key = some position) :
    nameAt definitions position = key := by
  induction definitions with
  | nil => exact Fin.elim0 position
  | cons head tail ih =>
    by_cases same : head.name = key
    · have eq : position = 0 := by simpa [position?, same, eq_comm] using found
      subst position
      exact same
    · cases selected : position? tail key with
      | none => simp [position?, same, selected] at found
      | some previous =>
        have eq : position = previous.succ := by simpa [position?, same, selected, eq_comm] using found
        subst position
        exact ih previous selected

theorem position_none_iff (definitions : Definitions) (key : String) :
    position? definitions key = none ↔ key ∉ names definitions := by
  induction definitions with
  | nil => simp [position?, names]
  | cons head tail ih =>
    by_cases same : head.name = key
    · simp [position?, names, same]
    · simpa [position?, names, same, Ne.symm same] using ih

theorem position_nameAt (definitions : Definitions) (unique : (names definitions).Nodup)
    (position : Fin definitions.length) : position? definitions (nameAt definitions position) = some position := by
  induction definitions with
  | nil => exact Fin.elim0 position
  | cons head tail ih =>
    have distinct : head.name ∉ names tail := (List.nodup_cons.mp unique).1
    have tailUnique : (names tail).Nodup := (List.nodup_cons.mp unique).2
    refine Fin.cases ?_ (fun previous => ?_) position
    · simp [position?, nameAt]
    · have absent : head.name ≠ nameAt tail previous := by
        intro same
        apply distinct
        exact List.mem_map.mpr ⟨tail.get previous, List.get_mem _ _, same.symm⟩
      change (if head.name = nameAt tail previous then some 0
        else (position? tail (nameAt tail previous)).map Fin.succ) = some previous.succ
      rw [if_neg absent, ih tailUnique previous]
      rfl

theorem nameAt_injective (definitions : Definitions) (unique : (names definitions).Nodup) :
    Function.Injective (nameAt definitions) := by
  intro left right same
  have compared := congrArg (position? definitions) same
  simpa [position_nameAt definitions unique] using compared

def graphKnown (definitions : Definitions) (history : List SExpr) :
    PlainBnfOrderedGraphDiscovery.Known definitions.length :=
  fun position => PlainBnfProductiveSourceExecution.member history (nameAt definitions position)

/-- The known-history carrier may retain repeated occurrences, but no foreign
name may be treated as a discovered grammar definition. -/
def HistoryScoped (definitions : Definitions) (history : List SExpr) : Prop :=
  ∀ key, text key ∈ history → key ∈ names definitions

def NamesDisjoint (definitions : Definitions) (lexicals : List LexicalDeclaration) : Prop :=
  ∀ key ∈ names definitions, firstDeclaration key lexicals = none

def referencePosition? (definitions : Definitions) (element : Element) : Option (Fin definitions.length) :=
  element.referenceName?.bind (position? definitions)

def referencePositions (definitions : Definitions) (elements : List Element) : List (Fin definitions.length) :=
  elements.filterMap (referencePosition? definitions)

def productiveLeaf (definitions : Definitions) (lexicals : List LexicalDeclaration) : Element → Bool
  | .literal _ _ => true
  | .reference key _ => match position? definitions key with
      | some _ => true
      | none => PlainBnfProductiveSourceExecution.lexicalMeaning (firstDeclaration key lexicals)

def nullableLeaf (definitions : Definitions) : Element → Bool
  | .literal value _ => value == ""
  | .reference key _ => (position? definitions key).isSome

def alternativeView (definitions : Definitions) (leaf : Element → Bool)
    (value : Alternative) : PlainBnfOrderedGraphDiscovery.Alternative definitions.length :=
  { references := referencePositions definitions value.elements
    leavesAdmitted := value.elements.all leaf }

def productiveExpression (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (value : Expression) : List (PlainBnfOrderedGraphDiscovery.Alternative definitions.length) :=
  value.alternatives.map (alternativeView definitions (productiveLeaf definitions lexicals))

def nullableExpression (definitions : Definitions) (value : Expression) :
    List (PlainBnfOrderedGraphDiscovery.Alternative definitions.length) :=
  value.alternatives.map (alternativeView definitions (nullableLeaf definitions))

def productiveGrammar (definitions : Definitions) (lexicals : List LexicalDeclaration) :
    PlainBnfOrderedGraphDiscovery.Grammar definitions.length :=
  fun position => productiveExpression definitions lexicals (expressionAt definitions position)

def nullableGrammar (definitions : Definitions) : PlainBnfOrderedGraphDiscovery.Grammar definitions.length :=
  fun position => nullableExpression definitions (expressionAt definitions position)


theorem nameAt_mem (definitions : Definitions) (position : Fin definitions.length) :
    nameAt definitions position ∈ names definitions :=
  List.mem_map.mpr ⟨definitions.get position, List.get_mem _ _, rfl⟩

theorem known_at_position (definitions : Definitions) (history : List SExpr) (key : String)
    (position : Fin definitions.length) (found : position? definitions key = some position) :
    graphKnown definitions history position = PlainBnfProductiveSourceExecution.member history key := by
  unfold graphKnown
  rw [position_some_name definitions key position found]

theorem unknown_not_known (definitions : Definitions) (history : List SExpr)
    (historyScoped : HistoryScoped definitions history) (key : String) (missing : position? definitions key = none) :
    PlainBnfProductiveSourceExecution.member history key = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  exact (position_none_iff definitions key).mp missing
    (historyScoped key ((PlainBnfProductiveSourceExecution.member_iff history key).mp yes))

theorem nullable_known_agrees (history : List SExpr) (key : String) :
    PlainBnfNullableSourceExecution.isKnown history key =
      PlainBnfProductiveSourceExecution.member history key := rfl

/-- The existing all-fold distributes across the independent leaf/reference
classification. No search calculus is involved in this factorization. -/
theorem alternativeReady_fold (definitions : Definitions) (leaf : Element → Bool)
    (known : PlainBnfOrderedGraphDiscovery.Known definitions.length) (value : Alternative) :
    PlainBnfOrderedGraphDiscovery.alternativeReady known (alternativeView definitions leaf value) =
      value.elements.all (fun element =>
        leaf element && (referencePosition? definitions element).all known) := by
  rcases value with ⟨elements, location⟩
  simp only [PlainBnfOrderedGraphDiscovery.alternativeReady, alternativeView]
  induction elements with
  | nil => rfl
  | cons head tail ih =>
    cases selected : referencePosition? definitions head <;>
      simp [referencePositions, List.all_cons, selected, Bool.and_assoc,
        Bool.and_left_comm] at ih ⊢
    all_goals rw [ih]

theorem productive_element_exact (definitions : Definitions) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (historyScoped : HistoryScoped definitions history)
    (disjoint : NamesDisjoint definitions lexicals) (element : Element) :
    (productiveLeaf definitions lexicals element &&
        (referencePosition? definitions element).all (graphKnown definitions history)) =
      PlainBnfProductiveSourceExecution.elementMeaning history lexicals element := by
  cases element with
  | literal value location => rfl
  | reference key location =>
    cases found : position? definitions key with
    | none =>
      have absent := unknown_not_known definitions history historyScoped key found
      simp [productiveLeaf, referencePosition?, Element.referenceName?, found,
        PlainBnfProductiveSourceExecution.elementMeaning,
        PlainBnfProductiveSourceExecution.referenceMeaning, absent]
    | some position =>
      have value := known_at_position definitions history key position found
      have declared : key ∈ names definitions := by
        rw [← position_some_name definitions key position found]
        exact nameAt_mem definitions position
      have noLexical := disjoint key declared
      simp [productiveLeaf, referencePosition?, Element.referenceName?, found, value,
        PlainBnfProductiveSourceExecution.elementMeaning,
        PlainBnfProductiveSourceExecution.referenceMeaning,
        PlainBnfProductiveSourceExecution.lexicalMeaning, noLexical]

theorem nullable_element_exact (definitions : Definitions) (history : List SExpr)
    (historyScoped : HistoryScoped definitions history) (element : Element) :
    (nullableLeaf definitions element &&
        (referencePosition? definitions element).all (graphKnown definitions history)) =
      PlainBnfNullableSourceExecution.elementMeaning history element := by
  cases element with
  | literal value location => simp [nullableLeaf, referencePosition?, Element.referenceName?,
      PlainBnfNullableSourceExecution.elementMeaning]
  | reference key location =>
    cases found : position? definitions key with
    | none =>
      have absent := unknown_not_known definitions history historyScoped key found
      simp [nullableLeaf, referencePosition?, Element.referenceName?, found,
        PlainBnfNullableSourceExecution.elementMeaning, nullable_known_agrees, absent]
    | some position =>
      have value := known_at_position definitions history key position found
      simp [nullableLeaf, referencePosition?, Element.referenceName?, found, value,
        PlainBnfNullableSourceExecution.elementMeaning, nullable_known_agrees]

theorem productive_alternative_exact (definitions : Definitions) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (historyScoped : HistoryScoped definitions history)
    (disjoint : NamesDisjoint definitions lexicals) (value : Alternative) :
    PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown definitions history)
      (alternativeView definitions (productiveLeaf definitions lexicals) value) =
      PlainBnfProductiveSourceExecution.alternativeMeaning history lexicals value := by
  rw [alternativeReady_fold]
  simp_rw [productive_element_exact definitions history lexicals historyScoped disjoint]
  rfl

theorem nullable_alternative_exact (definitions : Definitions) (history : List SExpr)
    (historyScoped : HistoryScoped definitions history) (value : Alternative) :
    PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown definitions history)
      (alternativeView definitions (nullableLeaf definitions) value) =
      PlainBnfNullableSourceExecution.alternativeMeaning history value := by
  rw [alternativeReady_fold]
  simp_rw [nullable_element_exact definitions history historyScoped]
  rfl

theorem productive_expression_exact (definitions : Definitions) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (historyScoped : HistoryScoped definitions history)
    (disjoint : NamesDisjoint definitions lexicals) (value : Expression) :
    (productiveExpression definitions lexicals value).any
      (PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown definitions history)) =
      PlainBnfProductiveSourceExecution.expressionMeaning history lexicals value := by
  simp [productiveExpression, List.any_map,
    productive_alternative_exact definitions history lexicals historyScoped disjoint,
    PlainBnfProductiveSourceExecution.expressionMeaning, Function.comp_def]

theorem nullable_expression_exact (definitions : Definitions) (history : List SExpr)
    (historyScoped : HistoryScoped definitions history) (value : Expression) :
    (nullableExpression definitions value).any
      (PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown definitions history)) =
      PlainBnfNullableSourceExecution.expressionMeaning history value := by
  simp [nullableExpression, List.any_map, nullable_alternative_exact definitions history historyScoped,
    PlainBnfNullableSourceExecution.expressionMeaning, PlainBnfNullableSourceExecution.alternativesMeaning,
    Function.comp_def]

/-- Ordered discovery adds the separate already-known exclusion to readiness. -/
theorem productive_ready_exact (definitions : Definitions) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (historyScoped : HistoryScoped definitions history)
    (disjoint : NamesDisjoint definitions lexicals) (position : Fin definitions.length) :
    PlainBnfOrderedGraphDiscovery.ready (productiveGrammar definitions lexicals)
      (graphKnown definitions history) position =
      (!PlainBnfProductiveSourceExecution.member history (nameAt definitions position) &&
        PlainBnfProductiveSourceExecution.expressionMeaning history lexicals (expressionAt definitions position)) := by
  unfold PlainBnfOrderedGraphDiscovery.ready productiveGrammar
  rw [productive_expression_exact definitions history lexicals historyScoped disjoint]
  rfl

theorem nullable_ready_exact (definitions : Definitions) (history : List SExpr)
    (historyScoped : HistoryScoped definitions history) (position : Fin definitions.length) :
    PlainBnfOrderedGraphDiscovery.ready (nullableGrammar definitions)
      (graphKnown definitions history) position =
      (!PlainBnfProductiveSourceExecution.member history (nameAt definitions position) &&
        PlainBnfNullableSourceExecution.expressionMeaning history (expressionAt definitions position)) := by
  unfold PlainBnfOrderedGraphDiscovery.ready nullableGrammar
  rw [nullable_expression_exact definitions history historyScoped]
  rfl


def lexicalName (lexicals : List LexicalDeclaration) (key : String) : Bool :=
  lexicals.any (·.referenceName == key)

theorem lexicalName_false_iff (lexicals : List LexicalDeclaration) (key : String) :
    lexicalName lexicals key = false ↔ firstDeclaration key lexicals = none := by
  induction lexicals with
  | nil => simp [lexicalName, firstDeclaration]
  | cons head tail ih =>
    by_cases same : head.referenceName = key <;>
      simp [lexicalName, firstDeclaration, same] at ih ⊢

def Resolved (definitions : Definitions) (lexicals : List LexicalDeclaration) (keys : List String) : Prop :=
  ∀ key ∈ keys, key ∈ names definitions ∨ lexicalName lexicals key = true

theorem resolve_names_exact (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (disjoint : NamesDisjoint definitions lexicals) (keys : List String)
    (resolved : Resolved definitions lexicals keys) :
    (keys.filterMap (position? definitions)).map (nameAt definitions) =
      keys.filter (fun key => !lexicalName lexicals key) := by
  induction keys with
  | nil => rfl
  | cons head tail ih =>
    have rest : Resolved definitions lexicals tail := fun key present =>
      resolved key (List.mem_cons_of_mem _ present)
    cases found : position? definitions head with
    | none =>
      have lexical : lexicalName lexicals head = true := by
        rcases resolved head (by simp) with grammar | lexical
        · exact False.elim ((position_none_iff definitions head).mp found grammar)
        · exact lexical
      simp [found, lexical, ih rest]
    | some position =>
      have same := position_some_name definitions head position found
      have grammar : head ∈ names definitions := by
        rw [← same]
        exact nameAt_mem definitions position
      have notLexical := (lexicalName_false_iff lexicals head).mpr (disjoint head grammar)
      simp [found, same, notLexical, ih rest]

theorem referencePositions_filterMap (definitions : Definitions) (elements : List Element) :
    referencePositions definitions elements =
      (elements.filterMap Element.referenceName?).filterMap (position? definitions) := by
  simp only [referencePositions, List.filterMap_filterMap]
  rfl

theorem alternative_references_exact (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (disjoint : NamesDisjoint definitions lexicals) (value : Alternative)
    (resolved : Resolved definitions lexicals value.referenceNames) (leaf : Element → Bool) :
    ((alternativeView definitions leaf value).references).map (nameAt definitions) =
      value.referenceNames.filter (fun key => !lexicalName lexicals key) := by
  change (referencePositions definitions value.elements).map _ = _
  rw [referencePositions_filterMap]
  exact resolve_names_exact definitions lexicals disjoint value.referenceNames resolved

theorem expression_references_filterMap (definitions : Definitions) (leaf : Element → Bool)
    (value : Expression) :
    (value.alternatives.map (alternativeView definitions leaf)).flatMap (·.references) =
      value.referenceNames.filterMap (position? definitions) := by
  simp [List.flatMap_map, alternativeView, referencePositions_filterMap,
    Expression.referenceNames, Alternative.referenceNames, List.filterMap_flatMap]

/-- Exact name-list correspondence, not merely equality of reachability sets. -/
theorem expression_references_exact (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (disjoint : NamesDisjoint definitions lexicals) (value : Expression)
    (resolved : Resolved definitions lexicals value.referenceNames) (leaf : Element → Bool) :
    ((value.alternatives.map (alternativeView definitions leaf)).flatMap (·.references)).map
        (nameAt definitions) = grammarReferences value lexicals := by
  rw [expression_references_filterMap]
  exact resolve_names_exact definitions lexicals disjoint value.referenceNames resolved

theorem productive_references_exact (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (disjoint : NamesDisjoint definitions lexicals) (value : Expression)
    (resolved : Resolved definitions lexicals value.referenceNames) :
    ((productiveExpression definitions lexicals value).flatMap (·.references)).map
        (nameAt definitions) = grammarReferences value lexicals :=
  expression_references_exact definitions lexicals disjoint value resolved _

theorem nullable_references_exact (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (disjoint : NamesDisjoint definitions lexicals) (value : Expression)
    (resolved : Resolved definitions lexicals value.referenceNames) :
    ((nullableExpression definitions value).flatMap (·.references)).map
        (nameAt definitions) = grammarReferences value lexicals :=
  expression_references_exact definitions lexicals disjoint value resolved _

/-- The two analyses share precisely the same reference occurrences. -/
theorem productive_nullable_same_references (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (value : Expression) :
    (productiveExpression definitions lexicals value).flatMap (·.references) =
      (nullableExpression definitions value).flatMap (·.references) := by
  rw [productiveExpression, nullableExpression, expression_references_filterMap,
    expression_references_filterMap]

/-- The existing reverse-incidence edge list remains ordered by definition,
alternative, and element occurrence before any set-valued observer is used. -/
theorem incidence_occurrences_exact (definitions : Definitions) (lexicals : List LexicalDeclaration)
    (disjoint : NamesDisjoint definitions lexicals)
    (resolved : ∀ position, Resolved definitions lexicals (expressionAt definitions position).referenceNames) :
    (PlainBnfDependencyWorklist.referenceEdges (productiveGrammar definitions lexicals)).map
        (fun edge => (nameAt definitions edge.1, nameAt definitions edge.2)) =
      (List.finRange definitions.length).flatMap (fun position =>
        (grammarReferences (expressionAt definitions position) lexicals).map
          (fun key => (key, nameAt definitions position))) := by
  unfold PlainBnfDependencyWorklist.referenceEdges
  simp only [List.map_flatMap]
  apply List.flatMap_congr
  intro position _
  have exactReferences := productive_references_exact definitions lexicals disjoint
    (expressionAt definitions position) (resolved position)
  rw [← exactReferences]
  simp [productiveGrammar, List.map_map, List.map_flatMap, Function.comp_def]

theorem productive_source_step_iff (definitions : Definitions) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (historyScoped : HistoryScoped definitions history)
    (disjoint : NamesDisjoint definitions lexicals) (value : Expression)
    (index : PlainBnfProductiveSourceExecution.NameIndex)
    (valid : PlainBnfKnownNamesSourceExecution.Valid index history)
    (target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises PlainBnfLexicalMatcherSourceExecution.relations)
      PlainBnfProductiveSourceExecution.language
      (PlainBnfProductiveSourceExecution.expressionCall value index history lexicals) target ↔
      target = PlainBnfTrieSourceExecution.result (PlainBnfLexicalMatcherSourceExecution.answer
        ((productiveExpression definitions lexicals value).any
          (PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown definitions history)))) := by
  rw [productive_expression_exact definitions history lexicals historyScoped disjoint]
  exact PlainBnfProductiveSourceExecution.expression_step_iff value index history lexicals valid target

theorem nullable_source_step_iff (definitions : Definitions) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (historyScoped : HistoryScoped definitions history)
    (value : Expression) (index : PlainBnfProductiveSourceExecution.NameIndex)
    (valid : PlainBnfKnownNamesSourceExecution.Valid index history)
    (target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
      PlainBnfNullableSourceExecution.language
      (PlainBnfNullableSourceExecution.expressionCall value index history lexicals) target ↔
      target = PlainBnfTrieSourceExecution.result (PlainBnfLexicalMatcherSourceExecution.answer
        ((nullableExpression definitions value).any
          (PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown definitions history)))) := by
  rw [nullable_expression_exact definitions history historyScoped]
  exact PlainBnfNullableSourceExecution.expression_step_iff value index history lexicals valid target

theorem productive_graph_semantics (definitions : Definitions) (history : List SExpr)
    (authority : GrammarAuthority) (historyScoped : HistoryScoped definitions history)
    (disjoint : NamesDisjoint definitions authority.lexicalDeclarations)
    (unique : (authority.lexicalDeclarations.map (·.referenceName)).Nodup)
    (valid : ∀ declaration ∈ authority.lexicalDeclarations,
      PlainBnfSemanticAdmission.MatcherWellFormed declaration.matcher) (value : Expression) :
    (productiveExpression definitions authority.lexicalDeclarations value).any
        (PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown definitions history)) = true ↔
      PlainBnfGraphSemantics.ExpressionProductive {key | text key ∈ history} authority value := by
  rw [productive_expression_exact definitions history authority.lexicalDeclarations historyScoped disjoint]
  exact PlainBnfProductiveSourceExecution.expressionMeaning_iff history authority unique valid value


theorem nullable_graph_semantics (definitions : Definitions) (history : List SExpr)
    (historyScoped : HistoryScoped definitions history) (value : Expression) :
    (nullableExpression definitions value).any
        (PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown definitions history)) = true ↔
      PlainBnfGraphSemantics.ExpressionNullable {key | text key ∈ history} value := by
  rw [nullable_expression_exact definitions history historyScoped]
  exact PlainBnfNullableSourceExecution.expression_meaning_iff history value

theorem empty_history_scoped (definitions : Definitions) : HistoryScoped definitions [] := by
  intro key impossible
  cases impossible

theorem history_publish_scoped (definitions : Definitions) (history : List SExpr)
    (historyScoped : HistoryScoped definitions history) (position : Fin definitions.length) :
    HistoryScoped definitions (text (nameAt definitions position) :: history) := by
  intro key present
  rcases List.mem_cons.mp present with same | old
  · have keyEq := PlainBnfReferenceCollectionSourceExecution.text_injective same
    rw [keyEq]
    exact nameAt_mem definitions position
  · exact historyScoped key old

theorem graphKnown_publish (definitions : Definitions) (unique : (names definitions).Nodup)
    (history : List SExpr) (position : Fin definitions.length) :
    graphKnown definitions (text (nameAt definitions position) :: history) =
      PlainBnfOrderedGraphDiscovery.publish (graphKnown definitions history) position := by
  funext other
  by_cases same : other = position
  · subst other
    simp [graphKnown, PlainBnfProductiveSourceExecution.member, PlainBnfOrderedGraphDiscovery.publish]
  · have distinctNames : nameAt definitions other ≠ nameAt definitions position :=
      fun equal => same (nameAt_injective definitions unique equal)
    have distinctText : text (nameAt definitions other) ≠ text (nameAt definitions position) :=
      fun equal => distinctNames (PlainBnfReferenceCollectionSourceExecution.text_injective equal)
    simp [graphKnown, PlainBnfProductiveSourceExecution.member,
      PlainBnfOrderedGraphDiscovery.publish, same, distinctText]

/-- Only rule entries produce discovery positions; their original name, body,
and span remain in the existing definition carrier in source order. -/
def definitionsFromDocument (document : PlainBnfStructuredDenotation.Document) : Definitions :=
  (PlainBnfSemanticAdmission.ruleOccurrences document).map
    (fun occurrence => ⟨occurrence.name, occurrence.expression, occurrence.span⟩)

theorem definitionsFromDocument_names (document : PlainBnfStructuredDenotation.Document) :
    names (definitionsFromDocument document) =
      (PlainBnfSemanticAdmission.ruleOccurrences document).map (·.name) := by
  simp [names, definitionsFromDocument, List.map_map]

private theorem ruleOccurrence_references (entries : List PlainBnfStructuredDenotation.Entry) (index : Nat) :
    (PlainBnfSemanticAdmission.ruleOccurrencesFrom entries index).flatMap
        (fun occurrence => occurrence.expression.referenceNames) =
      PlainBnfStructuredDenotation.entryReferenceNames entries := by
  induction entries generalizing index with
  | nil => rfl
  | cons entry tail ih =>
    cases entry <;>
      simp [PlainBnfSemanticAdmission.ruleOccurrencesFrom,
        PlainBnfStructuredDenotation.entryReferenceNames,
        PlainBnfStructuredDenotation.Entry.referenceNames, ih]

theorem definitionsFromDocument_references (document : PlainBnfStructuredDenotation.Document) :
    (definitionsFromDocument document).flatMap (fun definition => definition.expression.referenceNames) =
      PlainBnfStructuredDenotation.entryReferenceNames document.entries := by
  simp [definitionsFromDocument, List.flatMap_map, PlainBnfSemanticAdmission.ruleOccurrences,
    ruleOccurrence_references]

theorem admitted_definition_names_unique (input : PlainBnfSemanticAdmission.AdmittedInput) :
    (names (definitionsFromDocument input.document)).Nodup := by
  rw [definitionsFromDocument_names]
  exact input.wellFormed.2.1

theorem admitted_names_disjoint (input : PlainBnfSemanticAdmission.AdmittedInput) :
    NamesDisjoint (definitionsFromDocument input.document) input.authority.lexicalDeclarations := by
  intro key grammar
  rw [definitionsFromDocument_names] at grammar
  rcases input.wellFormed with ⟨_, _, _, _, _, disjoint, _⟩
  have absent := List.forall_iff_forall_mem.mp disjoint key grammar
  change key ∉ (PlainBnfSemanticAdmission.lexicalOccurrencesFrom input.authority.lexicalDeclarations 0).map
    (·.declaration.referenceName) at absent
  rw [PlainBnfSemanticAdmission.lexicalOccurrence_referenceNames] at absent
  apply (lexicalName_false_iff input.authority.lexicalDeclarations key).mp
  apply Bool.eq_false_iff.mpr
  intro yes
  obtain ⟨declaration, present, equal⟩ := List.any_eq_true.mp yes
  exact absent (List.mem_map.mpr ⟨declaration, present, by simpa using equal⟩)

theorem admitted_lexical_names_unique (input : PlainBnfSemanticAdmission.AdmittedInput) :
    (input.authority.lexicalDeclarations.map (·.referenceName)).Nodup := by
  have unique := input.wellFormed.2.2.1
  change ((PlainBnfSemanticAdmission.lexicalOccurrencesFrom input.authority.lexicalDeclarations 0).map
    (·.declaration.referenceName)).Nodup at unique
  simpa [PlainBnfSemanticAdmission.lexicalOccurrence_referenceNames] using unique

theorem admitted_lexical_matchers_valid (input : PlainBnfSemanticAdmission.AdmittedInput) :
    ∀ declaration ∈ input.authority.lexicalDeclarations,
      PlainBnfSemanticAdmission.MatcherWellFormed declaration.matcher := by
  rcases input.wellFormed with ⟨_, _, _, _, _, _, valid, _⟩
  intro declaration present
  exact (List.forall_iff_forall_mem.mp valid declaration present).2.2.2

theorem admitted_references_resolved (input : PlainBnfSemanticAdmission.AdmittedInput)
    (position : Fin (definitionsFromDocument input.document).length) :
    Resolved (definitionsFromDocument input.document) input.authority.lexicalDeclarations
      (expressionAt (definitionsFromDocument input.document) position).referenceNames := by
  intro key present
  have sourceMember : key ∈ (definitionsFromDocument input.document).flatMap
      (fun definition => definition.expression.referenceNames) :=
    List.mem_flatMap.mpr ⟨(definitionsFromDocument input.document).get position, List.get_mem _ _, present⟩
  rw [definitionsFromDocument_references,
    ← PlainBnfSemanticAdmission.referenceOccurrencesFrom_names input.document.entries 0] at sourceMember
  obtain ⟨occurrence, occurrenceMember, keyEq⟩ := List.mem_map.mp sourceMember
  rcases input.wellFormed with ⟨_, _, _, _, _, _, _, _, resolves⟩
  have unique := List.forall_iff_forall_mem.mp resolves occurrence occurrenceMember
  rw [keyEq] at unique
  have declared := PlainBnfSemanticAdmission.name_mem_denoted_type_names_of_unique_resolution
    input.document input.authority key unique
  change key ∈ (PlainBnfStructuredDenotation.denote input.document input.authority).language.types.map
    Mettapedia.OSLF.MeTTaIL.Syntax.TypeDecl.name at declared
  rw [PlainBnfStructuredDenotation.denote_type_names] at declared
  rcases List.mem_append.mp declared with grammar | lexical
  · left
    rw [definitionsFromDocument_names]
    simpa [PlainBnfSemanticAdmission.ruleOccurrences,
      PlainBnfSemanticAdmission.ruleOccurrence_names] using grammar
  · right
    obtain ⟨declaration, member, equal⟩ := List.mem_map.mp lexical
    exact List.any_eq_true.mpr ⟨declaration, member, by simpa using equal⟩


theorem admitted_incidence_occurrences (input : PlainBnfSemanticAdmission.AdmittedInput) :
    (PlainBnfDependencyWorklist.referenceEdges
        (productiveGrammar (definitionsFromDocument input.document) input.authority.lexicalDeclarations)).map
      (fun edge => (nameAt (definitionsFromDocument input.document) edge.1,
        nameAt (definitionsFromDocument input.document) edge.2)) =
    (List.finRange (definitionsFromDocument input.document).length).flatMap (fun position =>
      (grammarReferences (expressionAt (definitionsFromDocument input.document) position)
        input.authority.lexicalDeclarations).map
          (fun key => (key, nameAt (definitionsFromDocument input.document) position))) :=
  incidence_occurrences_exact _ _ (admitted_names_disjoint input) (admitted_references_resolved input)

private def controlSpan : SourceSpan := { start := 0, stop := 1 }
private def emptyExpression : Expression :=
  { alternatives := [{ elements := [], span := controlSpan }], span := controlSpan }
private def referencesExpression (keys : List String) : Expression :=
  { alternatives := [{ elements := keys.map (fun key => .reference key controlSpan), span := controlSpan }],
    span := controlSpan }
private abbrev controlDefinitions : Definitions :=
  [⟨"a", emptyExpression, controlSpan⟩,
   ⟨"b", referencesExpression ["a", "a"], controlSpan⟩]
private def controlLexical (key : String) : LexicalDeclaration :=
  { referenceName := key, className := "class", matcher := .except [], ruleLabel := "lex",
    origin := { authority := "control", occurrence := 0 } }

theorem repeated_edges_are_not_deduplicated :
    (productiveGrammar controlDefinitions [] 1).flatMap (·.references) = [0, 0] ∧
    (nullableGrammar controlDefinitions 1).flatMap (·.references) = [0, 0] ∧
    (PlainBnfDependencyWorklist.referenceEdges (productiveGrammar controlDefinitions [])).map
      (fun edge => (nameAt controlDefinitions edge.1, nameAt controlDefinitions edge.2)) =
        [("a", "b"), ("a", "b")] := by decide

theorem source_order_controls_position :
    position? controlDefinitions "a" = some 0 ∧
    position? controlDefinitions "b" = some 1 ∧
    position? controlDefinitions "missing" = none := by decide

theorem unknown_reference_does_not_satisfy_resolution :
    ¬ Resolved controlDefinitions [] ["missing"] ∧
    ((productiveExpression controlDefinitions [] (referencesExpression ["missing"])).any
      (PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown controlDefinitions []))) = false ∧
    grammarReferences (referencesExpression ["missing"]) [] = ["missing"] ∧
    (productiveExpression controlDefinitions [] (referencesExpression ["missing"])).flatMap
      (·.references) = [] := by
  constructor
  · intro resolves
    have declared := resolves "missing" (by simp)
    simp [names, controlDefinitions, lexicalName] at declared
  · decide

theorem lexical_leaf_differs_between_analyses :
    ((productiveExpression controlDefinitions [controlLexical "x"] (referencesExpression ["x"])).any
      (PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown controlDefinitions []))) = true ∧
    ((nullableExpression controlDefinitions (referencesExpression ["x"])).any
      (PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown controlDefinitions []))) = false := by decide

theorem namespace_collision_changes_productivity :
    ¬ NamesDisjoint controlDefinitions [controlLexical "a"] ∧
    ((productiveExpression controlDefinitions [controlLexical "a"] (referencesExpression ["a"])).any
      (PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown controlDefinitions []))) = false ∧
    PlainBnfProductiveSourceExecution.expressionMeaning [] [controlLexical "a"]
      (referencesExpression ["a"]) = true := by
  constructor
  · intro disjoint
    have absent := disjoint "a" (by simp [names, controlDefinitions])
    simp [firstDeclaration, controlLexical] at absent
  · decide

theorem foreign_history_changes_the_observation :
    ¬ HistoryScoped controlDefinitions [text "missing"] ∧
    ((nullableExpression controlDefinitions (referencesExpression ["missing"])).any
      (PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown controlDefinitions [text "missing"]))) = false ∧
    PlainBnfNullableSourceExecution.expressionMeaning [text "missing"]
      (referencesExpression ["missing"]) = true := by
  constructor
  · intro scopedHistory
    have declared := scopedHistory "missing" (by simp)
    simp [names, controlDefinitions] at declared
  · constructor
    · decide
    · simp [PlainBnfNullableSourceExecution.expressionMeaning,
        PlainBnfNullableSourceExecution.alternativesMeaning,
        PlainBnfNullableSourceExecution.alternativeMeaning,
        PlainBnfNullableSourceExecution.elementsMeaning,
        PlainBnfNullableSourceExecution.elementMeaning,
        PlainBnfNullableSourceExecution.isKnown, referencesExpression]

private abbrev duplicateDefinitions : Definitions :=
  [⟨"a", emptyExpression, controlSpan⟩, ⟨"a", referencesExpression ["a"], controlSpan⟩]

theorem duplicate_definitions_break_position_roundtrip :
    ¬ (names duplicateDefinitions).Nodup ∧
    position? duplicateDefinitions (nameAt duplicateDefinitions 1) = some 0 ∧
    position? duplicateDefinitions (nameAt duplicateDefinitions 1) ≠ some 1 := by decide

theorem already_known_expression_is_not_a_new_discovery :
    (productiveExpression controlDefinitions [] emptyExpression).any
      (PlainBnfOrderedGraphDiscovery.alternativeReady (graphKnown controlDefinitions [text "a"])) = true ∧
    PlainBnfOrderedGraphDiscovery.ready (productiveGrammar controlDefinitions [])
      (graphKnown controlDefinitions [text "a"]) 0 = false := by
  constructor
  · rfl
  · simp [PlainBnfOrderedGraphDiscovery.ready, graphKnown, nameAt, controlDefinitions,
      PlainBnfProductiveSourceExecution.member]

#print axioms position_nameAt
#print axioms productive_expression_exact
#print axioms nullable_expression_exact
#print axioms productive_source_step_iff
#print axioms nullable_source_step_iff
#print axioms incidence_occurrences_exact
#print axioms admitted_references_resolved
#print axioms admitted_incidence_occurrences
#print axioms graphKnown_publish

end Mettapedia.GSLT.Parsing.PlainBnfStructuredDiscoveryGraph
