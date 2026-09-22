import Mettapedia.GSLT.Parsing.PlainBnfControllerCompletedAnswers

/-!
# Discovery answers and the independent grammar fixed points

The existing ordered event reference is sound by publication and complete by
saturation. Its name observation therefore equals the independent productive
or nullable least fixed point. This set-valued observation does not replace
the exact ordered packet or its answer-occurrence theorem.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerLeastFixedPoint

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open PlainBnfStructuredDenotation (Document GrammarAuthority Expression)
open PlainBnfSemanticAdmission (AdmittedInput RuleOccurrence ruleOccurrences)
open PlainBnfStructuredDiscoveryGraph
open PlainBnfControllerPublicationFrontier (graph)
open PlainBnfControllerReferenceHistory
open PlainBnfOrderedGraphDiscovery (runEvents nextEvent ready alternativeReady)
open PlainBnfReferenceCollectionSourceExecution (text)
open PlainBnfGraphSemantics

/-- Select the two already defined independent meanings. -/
def semanticNames (productive : Bool) (document : Document) (authority : GrammarAuthority) : Set String :=
  if productive then Productive document authority else Nullable document

def expressionHolds (productive : Bool) (authority : GrammarAuthority)
    (current : Set String) (expression : Expression) : Prop :=
  if productive then ExpressionProductive current authority expression else ExpressionNullable current expression

theorem expressionHolds_mono (productive : Bool) (authority : GrammarAuthority)
    {left right : Set String} (included : left ⊆ right) (expression : Expression) :
    expressionHolds productive authority left expression →
      expressionHolds productive authority right expression := by
  cases productive with
  | false => exact expressionNullable_mono included
  | true => exact expressionProductive_mono included authority

theorem position_occurrence (document : Document)
    (position : Fin (definitionsFromDocument document).length) :
    ∃ occurrence ∈ ruleOccurrences document,
      nameAt (definitionsFromDocument document) position = occurrence.name ∧
      expressionAt (definitionsFromDocument document) position = occurrence.expression := by
  have member := List.get_mem (definitionsFromDocument document) position
  obtain ⟨occurrence, inside, same⟩ := List.mem_map.mp member
  exact ⟨occurrence, inside, (congrArg (·.name) same).symm,
    (congrArg (·.expression) same).symm⟩

theorem occurrence_position (document : Document) (occurrence : RuleOccurrence)
    (inside : occurrence ∈ ruleOccurrences document) :
    ∃ position : Fin (definitionsFromDocument document).length,
      nameAt (definitionsFromDocument document) position = occurrence.name ∧
      expressionAt (definitionsFromDocument document) position = occurrence.expression := by
  have member : (⟨occurrence.name, occurrence.expression, occurrence.span⟩ : Definition) ∈
      definitionsFromDocument document := List.mem_map.mpr ⟨occurrence, inside, rfl⟩
  obtain ⟨position, same⟩ := List.mem_iff_get.mp member
  exact ⟨position, congrArg (·.name) same, congrArg (·.expression) same⟩

theorem expression_graph_iff (productive : Bool) (admitted : AdmittedInput)
    (history : List SExpr) (historyScoped : HistoryScoped (definitionsFromDocument admitted.document) history)
    (position : Fin (definitionsFromDocument admitted.document).length) :
    ((graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
      position).any (alternativeReady (graphKnown (definitionsFromDocument admitted.document) history)) = true ↔
      expressionHolds productive admitted.authority {name | text name ∈ history}
        (expressionAt (definitionsFromDocument admitted.document) position) := by
  cases productive with
  | false => exact nullable_graph_semantics _ history historyScoped _
  | true =>
      exact productive_graph_semantics _ history admitted.authority historyScoped
        (admitted_names_disjoint admitted) (admitted_lexical_names_unique admitted)
        (admitted_lexical_matchers_valid admitted) _

theorem expression_justifies_name (productive : Bool) (admitted : AdmittedInput)
    (position : Fin (definitionsFromDocument admitted.document).length)
    (holds : expressionHolds productive admitted.authority
      (semanticNames productive admitted.document admitted.authority)
      (expressionAt (definitionsFromDocument admitted.document) position)) :
    nameAt (definitionsFromDocument admitted.document) position ∈
      semanticNames productive admitted.document admitted.authority := by
  obtain ⟨occurrence, inside, named, body⟩ := position_occurrence admitted.document position
  rw [named]
  rw [body] at holds
  cases productive with
  | false => exact nullable_of_expression admitted.document occurrence inside holds
  | true => exact productive_of_expression admitted.document admitted.authority occurrence inside holds

/-- Every reference publication is justified by the independent meaning. -/
theorem reference_history_sound (productive : Bool) (admitted : AdmittedInput)
    (fuel : Nat) (history : List SExpr) (round cursor : Nat)
    (historyScoped : HistoryScoped (definitionsFromDocument admitted.document) history)
    (sound : {name | text name ∈ history} ⊆ semanticNames productive admitted.document admitted.authority) :
    {name | text name ∈
      (runEvents (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
        fuel (graphKnown (definitionsFromDocument admitted.document) history) round cursor).foldl
          (fun current event => text (nameAt (definitionsFromDocument admitted.document) event.position) :: current)
          history} ⊆ semanticNames productive admitted.document admitted.authority := by
  induction fuel generalizing history round cursor with
  | zero => exact sound
  | succ fuel ih =>
      cases selected : nextEvent
          (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
          (graphKnown (definitionsFromDocument admitted.document) history) round cursor with
      | none => simpa [runEvents, selected] using sound
      | some event =>
          have enabled := nextEvent_ready _ _ _ _ event selected
          simp only [ready, Bool.and_eq_true] at enabled
          have bodyReady := enabled.2
          have holds := (expression_graph_iff productive admitted history historyScoped event.position).mp bodyReady
          have justified := expression_justifies_name productive admitted event.position
            (expressionHolds_mono productive admitted.authority sound _ holds)
          have nextSound : {name | text name ∈
              text (nameAt (definitionsFromDocument admitted.document) event.position) :: history} ⊆
              semanticNames productive admitted.document admitted.authority := by
            intro name member
            rcases List.mem_cons.mp member with same | old
            · exact (PlainBnfReferenceCollectionSourceExecution.text_injective same) ▸ justified
            · exact sound old
          rw [runEvents_succ _ fuel _ round cursor event selected, List.foldl_cons,
            ← graphKnown_publish _ (admitted_definition_names_unique admitted) history event.position]
          exact ih _ _ _ (history_publish_scoped _ history historyScoped event.position) nextSound

/-- A saturated history is closed under every authored definition's meaning.
It need not contain all declared names: an unseeded cycle adds none. -/
theorem saturated_history_closed (productive : Bool) (admitted : AdmittedInput)
    (history : List SExpr) (historyScoped : HistoryScoped (definitionsFromDocument admitted.document) history)
    (saturated : ∀ position, ready
      (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
      (graphKnown (definitionsFromDocument admitted.document) history) position = false) :
    ∀ occurrence ∈ ruleOccurrences admitted.document,
      expressionHolds productive admitted.authority {name | text name ∈ history} occurrence.expression →
        text occurrence.name ∈ history := by
  intro occurrence inside holds
  obtain ⟨position, named, body⟩ := occurrence_position admitted.document occurrence inside
  by_contra missing
  have unknown : graphKnown (definitionsFromDocument admitted.document) history position = false := by
    simpa [graphKnown, PlainBnfProductiveSourceExecution.member, named] using missing
  have bodyReady := (expression_graph_iff productive admitted history historyScoped position).mpr (body ▸ holds)
  have impossible := saturated position
  simp only [ready, unknown, Bool.not_false, Bool.true_and, bodyReady] at impossible
  contradiction

/-- The actual ordered reference contains exactly the least productive or
nullable name set, while its list order remains available separately. -/
theorem reference_history_exact (productive : Bool) (admitted : AdmittedInput) :
    let definitions := definitionsFromDocument admitted.document
    let events := runEvents (graph productive definitions admitted.authority.lexicalDeclarations)
      definitions.length (graphKnown definitions []) 0 0
    let history := events.foldl (fun current event => text (nameAt definitions event.position) :: current) []
    {name | text name ∈ history} = semanticNames productive admitted.document admitted.authority := by
  dsimp only
  apply Set.Subset.antisymm
  · exact reference_history_sound productive admitted _ [] 0 0 (empty_history_scoped _)
      (by intro name impossible; cases impossible)
  · have enough : (PlainBnfDependencyWorklist.unpublished
        (graphKnown (definitionsFromDocument admitted.document) [])).card ≤
        (definitionsFromDocument admitted.document).length :=
      (Finset.card_filter_le _ _).trans_eq (by simp)
    have saturated := reference_history_saturated _ (admitted_definition_names_unique admitted)
      (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
      _ [] 0 0 enough
    have closed := saturated_history_closed productive admitted _
      (history_fold_scoped _ _ [] (empty_history_scoped _)) saturated
    cases productive with
    | false => exact nullable_le_of_closed admitted.document _ closed
    | true => exact productive_le_of_closed admitted.document admitted.authority _ closed

theorem closure_answer_membership (productive : Bool) (admitted : AdmittedInput)
    (reverse : PlainBnfWakeContextualExecution.NameIndex)
    (indexed : Step (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
      PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall
        (PlainBnfStructuredEnumeration.candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty)
      (PlainBnfTrieSourceExecution.result (PlainBnfTrieSourceExecution.trie reverse)))
    (finalIndex : PlainBnfWakeContextualExecution.NameIndex) (finalHistory : List SExpr)
    (completed : Step (engineBasePremises PlainBnfLexicalMatcherSourceExecution.relations)
      PlainBnfRunSourceFamily.language
      (PlainBnfRunSourceExecution.closureCall productive
        (PlainBnfStructuredEnumeration.candidates (definitionsFromDocument admitted.document))
        reverse admitted.authority.lexicalDeclarations)
      (PlainBnfTrieSourceExecution.result (PlainBnfKnownNamesSourceExecution.known finalIndex finalHistory))) :
    ∀ name, text name ∈ finalHistory ↔
      name ∈ semanticNames productive admitted.document admitted.authority := by
  have packet := (PlainBnfControllerCompletedAnswers.admitted_closure_reference_answers
    productive admitted reverse indexed).1 _ |>.mp completed
  have histories := (PlainBnfKnownNamesSourceExecution.known_eq_iff _ _ _ _).mp
    (PlainBnfTrieSourceExecution.result_injective packet)
  rw [histories.2]
  exact fun name => Set.ext_iff.mp (reference_history_exact productive admitted) name

/-- Neither a fabricated name nor a missing justified name can be hidden by
the saturated-queue predicate: exact source execution rules both out. -/
theorem incorrect_membership_refused (productive : Bool) (admitted : AdmittedInput)
    (reverse : PlainBnfWakeContextualExecution.NameIndex)
    (indexed : Step (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
      PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall
        (PlainBnfStructuredEnumeration.candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty)
      (PlainBnfTrieSourceExecution.result (PlainBnfTrieSourceExecution.trie reverse)))
    (finalIndex : PlainBnfWakeContextualExecution.NameIndex) (finalHistory : List SExpr)
    (name : String)
    (wrong : ¬ (text name ∈ finalHistory ↔
      name ∈ semanticNames productive admitted.document admitted.authority)) :
    ¬ Step (engineBasePremises PlainBnfLexicalMatcherSourceExecution.relations)
      PlainBnfRunSourceFamily.language
      (PlainBnfRunSourceExecution.closureCall productive
        (PlainBnfStructuredEnumeration.candidates (definitionsFromDocument admitted.document))
        reverse admitted.authority.lexicalDeclarations)
      (PlainBnfTrieSourceExecution.result (PlainBnfKnownNamesSourceExecution.known finalIndex finalHistory)) := by
  intro completed
  exact wrong (closure_answer_membership productive admitted reverse indexed finalIndex finalHistory completed name)

private def controlSpan : PlainBnfStructuredDenotation.SourceSpan := { start := 0, stop := 1 }
private def literalExpression : Expression :=
  { alternatives := [{ elements := [.literal "x" controlSpan], span := controlSpan }], span := controlSpan }
private def literalInput : AdmittedInput :=
  { document := { entries := [.rule "s" literalExpression controlSpan], span := controlSpan }
    authority := { startName := "s", lexicalDeclarations := [] }
    wellFormed := by decide }

/-- The same admitted literal rule seeds productivity, but not nullability. -/
theorem literal_mode_discriminator :
    "s" ∈ semanticNames true literalInput.document literalInput.authority ∧
    "s" ∉ semanticNames false literalInput.document literalInput.authority := by
  constructor
  · apply expression_justifies_name true literalInput ⟨0, by decide⟩
    simp [expressionHolds, ExpressionProductive, AlternativeProductive, ElementProductive,
      expressionAt, definitionsFromDocument, literalInput, literalExpression,
      ruleOccurrences, PlainBnfSemanticAdmission.ruleOccurrencesFrom]
  · rw [← reference_history_exact false literalInput]
    decide

private def cycleExpression : Expression :=
  { alternatives := [{ elements := [.reference "s" controlSpan], span := controlSpan }], span := controlSpan }
private def cycleInput : AdmittedInput :=
  { document := { entries := [.rule "s" cycleExpression controlSpan], span := controlSpan }
    authority := { startName := "s", lexicalDeclarations := [] }
    wellFormed := by decide }

/-- A well-formed recursive grammar need not have any productive or nullable rule. -/
theorem unseeded_cycle_discriminator :
    "s" ∉ semanticNames true cycleInput.document cycleInput.authority ∧
    "s" ∉ semanticNames false cycleInput.document cycleInput.authority := by
  constructor
  · rw [← reference_history_exact true cycleInput]
    decide
  · rw [← reference_history_exact false cycleInput]
    decide

#print axioms reference_history_sound
#print axioms saturated_history_closed
#print axioms reference_history_exact
#print axioms closure_answer_membership
#print axioms incorrect_membership_refused
#print axioms literal_mode_discriminator
#print axioms unseeded_cycle_discriminator

end Mettapedia.GSLT.Parsing.PlainBnfControllerLeastFixedPoint
