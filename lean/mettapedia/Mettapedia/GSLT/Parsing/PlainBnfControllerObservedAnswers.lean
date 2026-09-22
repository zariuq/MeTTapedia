import Mettapedia.GSLT.Parsing.PlainBnfControllerLeastFixedPoint
import Mettapedia.GSLT.Parsing.PlainBnfNamesObservationSourceExecution

/-!
# Exact source Closure followed by names observation

These are the two existing calls used by the enclosing analysis. Their
relational composition returns exactly the forward reference names; each
individual call eventually returns one answer occurrence. No new interpreter
or combined runtime entry is defined. Reachability, validation diagnostics,
and generated/native caller preservation are separate obligations.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerObservedAnswers

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises rewriteAt)
open PlainBnfSemanticAdmission (AdmittedInput)
open PlainBnfStructuredDiscoveryGraph (definitionsFromDocument nameAt graphKnown)
open PlainBnfStructuredEnumeration (candidates)
open PlainBnfControllerPublicationFrontier (graph)
open PlainBnfOrderedGraphDiscovery (runEvents)
open PlainBnfWakeContextualExecution (NameIndex)
open PlainBnfReferenceCollectionSourceExecution (text)
open PlainBnfTrieSourceExecution (result result_injective trie scalarRelations)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfKnownNamesSourceExecution (known names observeCall known_eq_iff)
open PlainBnfRunSourceFamily (language)
open PlainBnfRunSourceExecution (closureCall)
open PlainBnfControllerCompletedAnswers (admitted_closure_reference_answers)
open PlainBnfNamesObservationSourceExecution (observe_event_history_step_iff observe_event_history_answers)

/-- Existentially linking the real output and next input preserves the exact
ordered names, not only an extensional set. -/
theorem closure_observation_iff (productive : Bool) (admitted : AdmittedInput)
    (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse)))
    (target : Pattern) :
    let definitions := definitionsFromDocument admitted.document
    let lexicals := admitted.authority.lexicalDeclarations
    let events := runEvents (graph productive definitions lexicals) definitions.length (graphKnown definitions []) 0 0
    (∃ (index : NameIndex) (history : List SExpr),
      Step (engineBasePremises relations) language (closureCall productive (candidates definitions) reverse lexicals)
        (result (known index history)) ∧
      Step (engineBasePremises relations) language (observeCall index history) target) ↔
      target = result (names (events.map (fun event => text (nameAt definitions event.position)))) := by
  dsimp only
  have completed := (admitted_closure_reference_answers productive admitted reverse indexed).1
  constructor
  · rintro ⟨index, history, closure, observed⟩
    have packet := (completed _).mp closure
    obtain ⟨rfl, rfl⟩ := (known_eq_iff _ _ _ _).mp (result_injective packet)
    simpa using (observe_event_history_step_iff _ _ _ [] target).mp observed
  · intro exactTarget
    refine ⟨_, _, (completed _).mpr rfl, ?_⟩
    apply (observe_event_history_step_iff _ _ _ [] target).mpr
    simpa using exactTarget

/-- Both source calls return single occurrences at a common sufficient
contextual depth. This is not a claim about native time or stack usage. -/
theorem closure_observation_eventual_singletons (productive : Bool) (admitted : AdmittedInput)
    (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse))) :
    let definitions := definitionsFromDocument admitted.document
    let lexicals := admitted.authority.lexicalDeclarations
    let events := runEvents (graph productive definitions lexicals) definitions.length (graphKnown definitions []) 0 0
    ∃ (index : NameIndex) (history : List SExpr) (threshold : Nat),
      ∀ fuel, threshold ≤ fuel →
        rewriteAt (engineBasePremises relations) language fuel
          (closureCall productive (candidates definitions) reverse lexicals) = [result (known index history)] ∧
        rewriteAt (engineBasePremises relations) language fuel (observeCall index history) =
          [result (names (events.map (fun event => text (nameAt definitions event.position))))] := by
  dsimp only
  obtain ⟨threshold, completed⟩ := (admitted_closure_reference_answers productive admitted reverse indexed).2.2
  let events := runEvents
    (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
    (definitionsFromDocument admitted.document).length
    (graphKnown (definitionsFromDocument admitted.document) []) 0 0
  let index : NameIndex := events.foldl (fun current event => PlainBnfGraphNameTrie.insertFirst
    (PlainBnfReverseIndexSourceExecution.key (nameAt (definitionsFromDocument admitted.document) event.position))
    (text (nameAt (definitionsFromDocument admitted.document) event.position)) current) .empty
  let history := events.foldl
    (fun current event => text (nameAt (definitionsFromDocument admitted.document) event.position) :: current) []
  refine ⟨index, history, threshold + events.length + 2, ?_⟩
  intro fuel enough
  refine ⟨completed fuel (by omega), ?_⟩
  dsimp only [history]
  rw [observe_event_history_answers]
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append]
  rw [if_pos (by omega)]

/-- The ordered answer also has precisely the independently defined grammar
meaning. The set projection here neither selects nor removes occurrences. -/
theorem observed_names_membership (productive : Bool) (admitted : AdmittedInput) :
    let definitions := definitionsFromDocument admitted.document
    let events := runEvents (graph productive definitions admitted.authority.lexicalDeclarations)
      definitions.length (graphKnown definitions []) 0 0
    ∀ name, text name ∈ events.map (fun event => text (nameAt definitions event.position)) ↔
      name ∈ PlainBnfControllerLeastFixedPoint.semanticNames productive admitted.document admitted.authority := by
  dsimp only
  intro name
  have exactMeaning := Set.ext_iff.mp
    (PlainBnfControllerLeastFixedPoint.reference_history_exact productive admitted) name
  simpa only [PlainBnfControllerReferenceHistory.history_fold_exact,
    List.append_nil, List.mem_reverse, Set.mem_ofPred_eq] using exactMeaning

/-- Reverse indexing is executed as well: no reverse-index answer premise is
required at this selected three-call boundary. The outer analysis has other
calls, whose composition is not asserted here. -/
theorem admitted_source_observation_iff (productive : Bool) (admitted : AdmittedInput)
    (target : Pattern) :
    let definitions := definitionsFromDocument admitted.document
    let lexicals := admitted.authority.lexicalDeclarations
    let events := runEvents (graph productive definitions lexicals) definitions.length (graphKnown definitions []) 0 0
    (∃ (reverse index : NameIndex) (history : List SExpr),
      Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
        (PlainBnfReverseIndexSourceExecution.reverseCall (candidates definitions) lexicals .empty)
        (result (trie reverse)) ∧
      Step (engineBasePremises relations) language (closureCall productive (candidates definitions) reverse lexicals)
        (result (known index history)) ∧
      Step (engineBasePremises relations) language (observeCall index history) target) ↔
      target = result (names (events.map (fun event => text (nameAt definitions event.position)))) := by
  dsimp only
  constructor
  · rintro ⟨reverse, index, history, indexed, closed, observed⟩
    exact (closure_observation_iff productive admitted reverse indexed target).mp ⟨index, history, closed, observed⟩
  · intro equal
    let reverse := PlainBnfReverseIndexSourceExecution.reverseIndex
      (candidates (definitionsFromDocument admitted.document)) admitted.authority.lexicalDeclarations .empty
    have indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
        (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
          admitted.authority.lexicalDeclarations .empty) (result (trie reverse)) :=
      (PlainBnfReverseIndexSourceExecution.reverse_step_iff _ _ _ _).mpr rfl
    obtain ⟨index, history, closed, observed⟩ :=
      (closure_observation_iff productive admitted reverse indexed target).mpr equal
    exact ⟨reverse, index, history, indexed, closed, observed⟩

#print axioms closure_observation_iff
#print axioms closure_observation_eventual_singletons
#print axioms observed_names_membership
#print axioms admitted_source_observation_iff

end Mettapedia.GSLT.Parsing.PlainBnfControllerObservedAnswers
