import Mettapedia.GSLT.Parsing.PlainBnfControllerRunCompletion
import Mettapedia.GSLT.Parsing.PlainBnfControllerAnswerOccurrences
import Mettapedia.GSLT.Parsing.PlainBnfControllerReferenceIndex
import Mettapedia.GSLT.Parsing.PlainBnfControllerReferenceExecution
import Mettapedia.GSLT.Parsing.PlainBnfControllerCoordinateExistence

/-!
# Complete occurrence-valued answers of the authored discovery controller

Termination supplies an actual finite derivation. The independent finite-depth
occurrence bound prevents duplicate equal answers, and depth monotonicity
preserves the answer at larger bounds. Thus sufficiently deep evaluation
returns exactly one complete known packet. This concerns source contextual
execution, not generated PeTTa, native runtime time limits, or a C theorem.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerCompletedAnswers

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern LanguageDef)
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open PlainBnfStructuredDiscoveryGraph (definitionsFromDocument HistoryScoped graphKnown)
open PlainBnfStructuredEnumeration (candidates)
open PlainBnfSourceRank (Rank value)
open PlainBnfWakeSourceExecution (HeapItem heapItem Queues)
open PlainBnfWakeContextualExecution (NameIndex)
open PlainBnfKnownNamesSourceExecution (Valid known)
open PlainBnfRunSourceExecution (runCall closureCall)
open PlainBnfRunSourceFamily (language)
open PlainBnfControllerInvariant (Invariant)
open PlainBnfControllerPublicationFrontier (graph)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfTrieSourceExecution (scalarRelations result trie)

private theorem singleton_of_mem_length {α : Type} (items : List α) (answer : α)
    (member : answer ∈ items) (bound : items.length ≤ 1) : items = [answer] := by
  cases items with
  | nil => cases member
  | cons first rest =>
    cases rest with
    | nil =>
      have same : answer = first := by simpa using member
      subst first
      rfl
    | cons second tail => simp at bound

/-- A theorem about the established contextual answer lists, not another
evaluator. The occurrence bound and total exact relation are separate inputs. -/
private theorem eventual_singleton (base : BasePremiseEvaluator) (lang : LanguageDef)
    (source answer : Pattern)
    (exactAnswer : ∀ target, Step base lang source target ↔ target = answer)
    (bound : ∀ fuel, (rewriteAt base lang fuel source).length ≤ 1) :
    (∀ fuel, rewriteAt base lang fuel source = [] ∨ rewriteAt base lang fuel source = [answer]) ∧
    ∃ threshold, ∀ fuel, threshold ≤ fuel → rewriteAt base lang fuel source = [answer] := by
  have present : ∃ fuel, answer ∈ rewriteAt base lang fuel source :=
    (exists_mem_rewriteAt_iff_step).mpr ((exactAnswer answer).mpr rfl)
  constructor
  · intro fuel
    cases answers : rewriteAt base lang fuel source with
    | nil => exact Or.inl rfl
    | cons first rest =>
      have inside : first ∈ rewriteAt base lang fuel source := by simp [answers]
      have same := (exactAnswer first).mp (exists_mem_rewriteAt_iff_step.mp ⟨fuel, inside⟩)
      have singleton := singleton_of_mem_length _ first inside (bound fuel)
      exact Or.inr (by simpa only [answers, same] using singleton)
  · obtain ⟨threshold, member⟩ := present
    refine ⟨threshold, fun fuel enough => singleton_of_mem_length _ answer ?_ (bound fuel)⟩
    exact PlainBnfRunSourceExecution.depth_mono base lang enough source member

theorem run_completed_answers (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput)
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
      (∀ target, Step (engineBasePremises relations) language
        (runCall productive reverse admitted.authority.lexicalDeclarations index history queues) target ↔
          target = result (known finalIndex finalHistory)) ∧
      (∀ fuel, rewriteAt (engineBasePremises relations) language fuel
          (runCall productive reverse admitted.authority.lexicalDeclarations index history queues) = [] ∨
        rewriteAt (engineBasePremises relations) language fuel
          (runCall productive reverse admitted.authority.lexicalDeclarations index history queues) =
            [result (known finalIndex finalHistory)]) ∧
      ∃ threshold, ∀ fuel, threshold ≤ fuel →
        rewriteAt (engineBasePremises relations) language fuel
          (runCall productive reverse admitted.authority.lexicalDeclarations index history queues) =
            [result (known finalIndex finalHistory)] := by
  obtain ⟨finalIndex, finalHistory, valid, historyScoped, nodup, suffix, saturated, exactAnswer⟩ :=
    PlainBnfControllerRunCompletion.run_complete productive admitted coordinate candidateRanks reverse indexed
      index history origin queues invariant
  exact ⟨finalIndex, finalHistory, valid, historyScoped, nodup, suffix, saturated, exactAnswer,
    eventual_singleton _ _ _ _ exactAnswer
      (fun fuel => PlainBnfControllerAnswerOccurrences.run_answers_length_le_one productive admitted
        coordinate candidateRanks reverse indexed fuel index history origin queues invariant)⟩

theorem closure_completed_answers (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (candidateRanks : ∀ item ∈ candidates (definitionsFromDocument admitted.document),
      (coordinate (heapItem item)).val = value item.1)
    (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse))) :
    ∃ (finalIndex : NameIndex) (finalHistory : List SExpr),
      Valid finalIndex finalHistory ∧ HistoryScoped (definitionsFromDocument admitted.document) finalHistory ∧
      finalHistory.Nodup ∧
      (∀ position, PlainBnfOrderedGraphDiscovery.ready
        (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
        (graphKnown (definitionsFromDocument admitted.document) finalHistory) position = false) ∧
      (∀ target, Step (engineBasePremises relations) language
        (closureCall productive (candidates (definitionsFromDocument admitted.document)) reverse
          admitted.authority.lexicalDeclarations) target ↔ target = result (known finalIndex finalHistory)) ∧
      (∀ fuel, rewriteAt (engineBasePremises relations) language fuel
          (closureCall productive (candidates (definitionsFromDocument admitted.document)) reverse
            admitted.authority.lexicalDeclarations) = [] ∨
        rewriteAt (engineBasePremises relations) language fuel
          (closureCall productive (candidates (definitionsFromDocument admitted.document)) reverse
            admitted.authority.lexicalDeclarations) = [result (known finalIndex finalHistory)]) ∧
      ∃ threshold, ∀ fuel, threshold ≤ fuel →
        rewriteAt (engineBasePremises relations) language fuel
          (closureCall productive (candidates (definitionsFromDocument admitted.document)) reverse
            admitted.authority.lexicalDeclarations) = [result (known finalIndex finalHistory)] := by
  obtain ⟨finalIndex, finalHistory, valid, historyScoped, nodup, _, saturated, exactRun⟩ :=
    PlainBnfControllerRunCompletion.run_complete productive admitted coordinate candidateRanks reverse indexed
      .empty [] none _ (PlainBnfControllerInvariant.initial_invariant productive admitted coordinate candidateRanks)
  have exactClosure : ∀ target, Step (engineBasePremises relations) language
      (closureCall productive (candidates (definitionsFromDocument admitted.document)) reverse
        admitted.authority.lexicalDeclarations) target ↔ target = result (known finalIndex finalHistory) := by
    intro target
    rw [PlainBnfRunSourceExecution.closure_iff]
    exact exactRun target
  exact ⟨finalIndex, finalHistory, valid, historyScoped, nodup, saturated, exactClosure,
    eventual_singleton _ _ _ _ exactClosure
      (PlainBnfControllerAnswerOccurrences.closure_answers_length_le_one productive admitted
        coordinate candidateRanks reverse indexed)⟩

/-- Every admitted grammar has the required source-coordinate observation;
the caller does not supply it. The answer is the independently ordered
reference trace replayed into the genuinely empty initial source packet. -/
theorem admitted_closure_reference_answers (productive : Bool)
    (admitted : PlainBnfSemanticAdmission.AdmittedInput) (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse))) :
    let definitions := definitionsFromDocument admitted.document
    let lexicals := admitted.authority.lexicalDeclarations
    let events := PlainBnfOrderedGraphDiscovery.runEvents (graph productive definitions lexicals)
      definitions.length (graphKnown definitions []) 0 0
    let answer := result (known
      (events.foldl (fun current event => PlainBnfGraphNameTrie.insertFirst
        (PlainBnfReverseIndexSourceExecution.key (PlainBnfStructuredDiscoveryGraph.nameAt definitions event.position))
        (PlainBnfReferenceCollectionSourceExecution.text
          (PlainBnfStructuredDiscoveryGraph.nameAt definitions event.position)) current) (.empty : NameIndex))
      (events.foldl (fun current event => PlainBnfReferenceCollectionSourceExecution.text
        (PlainBnfStructuredDiscoveryGraph.nameAt definitions event.position) :: current) []))
    (∀ target, Step (engineBasePremises relations) language
      (closureCall productive (candidates definitions) reverse lexicals) target ↔ target = answer) ∧
    (∀ fuel, rewriteAt (engineBasePremises relations) language fuel
        (closureCall productive (candidates definitions) reverse lexicals) = [] ∨
      rewriteAt (engineBasePremises relations) language fuel
        (closureCall productive (candidates definitions) reverse lexicals) = [answer]) ∧
    ∃ threshold, ∀ fuel, threshold ≤ fuel → rewriteAt (engineBasePremises relations) language fuel
      (closureCall productive (candidates definitions) reverse lexicals) = [answer] := by
  dsimp only
  obtain ⟨coordinate, candidateRanks⟩ :=
    PlainBnfControllerCoordinateExistence.admitted_coordinate_exists admitted
  have enough : (PlainBnfDependencyWorklist.unpublished
      (graphKnown (definitionsFromDocument admitted.document) [])).card ≤
      (definitionsFromDocument admitted.document).length := by
    exact (Finset.card_filter_le _ _).trans_eq (by simp)
  have exactAnswer := fun target => (PlainBnfRunSourceExecution.closure_iff productive
      (candidates (definitionsFromDocument admitted.document)) reverse admitted.authority.lexicalDeclarations target).trans
    (PlainBnfControllerReferenceExecution.run_reference_packet_iff productive admitted coordinate candidateRanks
      reverse indexed (definitionsFromDocument admitted.document).length .empty [] none _ 0
      (PlainBnfControllerInvariant.initial_invariant productive admitted coordinate candidateRanks) enough target)
  exact ⟨exactAnswer, eventual_singleton _ _ _ _ exactAnswer
    (PlainBnfControllerAnswerOccurrences.closure_answers_length_le_one productive admitted
      coordinate candidateRanks reverse indexed)⟩

#print axioms run_completed_answers
#print axioms closure_completed_answers
#print axioms admitted_closure_reference_answers

end Mettapedia.GSLT.Parsing.PlainBnfControllerCompletedAnswers
