import Mettapedia.GSLT.Parsing.PlainBnfControllerInvariant

/-!
# Finite-depth answer occurrences of the actual discovery controller

The existing contextual evaluator executes the original Run clauses. Every
invariant state returns at most one answer occurrence at any finite depth.
The proof follows the exact done, rollover, and publication answer lists;
it neither deduplicates equal values nor assumes termination or a final answer.
The reverse index is tied to its actual source execution on the same admitted
candidate and lexical inventory throughout the argument.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerAnswerOccurrences

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises rewriteAt)
open PlainBnfStructuredDiscoveryGraph (definitionsFromDocument)
open PlainBnfStructuredEnumeration (candidates)
open PlainBnfSourceRank (Rank value)
open PlainBnfWakeSourceExecution (HeapItem heapItem Queues)
open PlainBnfWakeContextualExecution (NameIndex)
open PlainBnfRunSourceExecution
  (runCall closureCall run_done_answers run_rollover_answers run_publish_answers closure_answers)
open PlainBnfRunSourceFamily (language)
open PlainBnfControllerInvariant (Invariant)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfTrieSourceExecution (scalarRelations result trie)

theorem run_answers_length_le_one (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (candidateRanks : ∀ item ∈ candidates (definitionsFromDocument admitted.document),
      (coordinate (heapItem item)).val = value item.1)
    (reverse : NameIndex)
    (reverseExecuted : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse)))
    (fuel : Nat) (index : NameIndex) (history : List SExpr) (origin : Option Rank) (queues : Queues)
    (invariant : Invariant productive (definitionsFromDocument admitted.document)
      admitted.authority.lexicalDeclarations coordinate index history origin queues) :
    (rewriteAt (engineBasePremises relations) language fuel
      (runCall productive reverse admitted.authority.lexicalDeclarations index history queues)).length ≤ 1 := by
  induction fuel generalizing index history origin queues with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
      rcases queues with ⟨current, following, scheduled⟩
      cases current with
      | nil =>
          cases following with
          | nil => simp [run_done_answers]
          | node payload children siblings =>
              rw [run_rollover_answers]
              exact ih index history none _
                (PlainBnfControllerInvariant.rollover productive _ _ coordinate index history origin
                  (.node payload children siblings) scheduled invariant)
      | node payload children siblings =>
          have noSiblings : siblings = .nil := by cases invariant.ordered.1; rfl
          subst siblings
          obtain ⟨item, _, same⟩ := invariant.payloads payload
            (by simp [PlainBnfWakeSourceExecution.contents, PlainBnfPairingHeapObservation.contents])
          subst payload
          have bucket := PlainBnfStructuredReverseDependencies.execution_lookup_bucket
            (candidates (definitionsFromDocument admitted.document)) item.2.name
            admitted.authority.lexicalDeclarations reverse reverseExecuted
          rw [run_publish_answers productive fuel item _ reverse index history
            admitted.authority.lexicalDeclarations children following scheduled invariant.valid bucket]
          split
          · exact ih _ _ (some item.1) _
              (PlainBnfControllerInvariant.publication productive admitted coordinate candidateRanks
                index history origin item children following scheduled invariant)
          · simp

theorem closure_answers_length_le_one (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (candidateRanks : ∀ item ∈ candidates (definitionsFromDocument admitted.document),
      (coordinate (heapItem item)).val = value item.1)
    (reverse : NameIndex)
    (reverseExecuted : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse)))
    (fuel : Nat) :
    (rewriteAt (engineBasePremises relations) language fuel
      (closureCall productive (candidates (definitionsFromDocument admitted.document)) reverse
        admitted.authority.lexicalDeclarations)).length ≤ 1 := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
      rw [closure_answers]
      split
      · exact run_answers_length_le_one productive admitted coordinate candidateRanks reverse reverseExecuted
          fuel .empty [] none _ (PlainBnfControllerInvariant.initial_invariant productive admitted coordinate candidateRanks)
      · simp

/-- Two equal answer values are still two occurrences and are excluded. -/
theorem run_cannot_repeat_answer (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (candidateRanks : ∀ item ∈ candidates (definitionsFromDocument admitted.document),
      (coordinate (heapItem item)).val = value item.1)
    (reverse : NameIndex)
    (reverseExecuted : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse)))
    (fuel : Nat) (index : NameIndex) (history : List SExpr) (origin : Option Rank) (queues : Queues)
    (invariant : Invariant productive (definitionsFromDocument admitted.document)
      admitted.authority.lexicalDeclarations coordinate index history origin queues) (answer : Pattern) :
    rewriteAt (engineBasePremises relations) language fuel
      (runCall productive reverse admitted.authority.lexicalDeclarations index history queues) ≠ [answer, answer] := by
  intro duplicated
  have bounded := run_answers_length_le_one productive admitted coordinate candidateRanks reverse reverseExecuted
    fuel index history origin queues invariant
  rw [duplicated] at bounded
  simp at bounded

/-- The real done clause supplies a positive singleton, not merely an upper bound. -/
theorem done_one_occurrence (productive : Bool) (fuel : Nat) (reverse : NameIndex)
    (lexicals : List PlainBnfStructuredDenotation.LexicalDeclaration)
    (index : NameIndex) (history : List SExpr) (scheduled : NameIndex) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (runCall productive reverse lexicals index history (.nil, .nil, scheduled)) =
      [result (PlainBnfKnownNamesSourceExecution.known index history)] := by
  simp [run_done_answers]

/-- A set-level uniqueness claim would not supply the occurrence theorem. -/
theorem equal_values_still_two_occurrences (answer : Pattern) :
    (∀ value ∈ [answer, answer], value = answer) ∧ ¬ ([answer, answer].length ≤ 1) := by simp

#print axioms run_answers_length_le_one
#print axioms closure_answers_length_le_one
#print axioms run_cannot_repeat_answer
#print axioms done_one_occurrence

end Mettapedia.GSLT.Parsing.PlainBnfControllerAnswerOccurrences
