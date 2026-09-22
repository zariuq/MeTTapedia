import Mettapedia.GSLT.Parsing.PlainBnfControllerPayloadProvenance
import Mettapedia.GSLT.Parsing.PlainBnfControllerQueuePreservation

/-!
# Structural source occurrence bounds for discovery Closure

The actual source controller returns at most one answer occurrence at every
finite contextual depth on arbitrary structured ranked definitions. The
proof retains only valid known-name packets, ordered heaps, and complete
candidate-payload provenance. It does not require unique names or positions,
resolved references, semantic grammar admission, or a termination premise.

These predicates observe the existing source state; there is no second
controller or expected-answer provider. The reverse index is connected to
its actual source execution. The domain is the existing String/Nat-spanned
structured carrier, not arbitrary edited Integer wire data. Finite source
absence is not a generated-runtime completion or exhaustion classification.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerStructuralOccurrences

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Batteries.PairingHeapImp (Heap)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises rewriteAt)
open PlainBnfSourceRank (Rank)
open PlainBnfStructuredDenotation (Expression LexicalDeclaration)
open PlainBnfReverseIndexSourceExecution (Item)
open PlainBnfWakeSourceExecution (HeapItem Queues Ordered heapItem contents wake)
open PlainBnfWakeContextualExecution (NameIndex meaning)
open PlainBnfKnownNamesSourceExecution (Valid known)
open PlainBnfControllerPayloadProvenance (FromCandidates)
open PlainBnfRunSourceExecution
  (runCall closureCall initialQueues publishedQueues publishedIndex publishedHistory
    run_done_answers run_rollover_answers run_publish_answers closure_answers)
open PlainBnfRunSourceFamily (language)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfTrieSourceExecution (scalarRelations result trie)

/-- A proof-only invariant of the original packet and heaps. It retains
complete encoded payloads; it neither deduplicates them nor demands distinct
rank or name fields. -/
structure Invariant (ranked : List Item) (index : NameIndex) (history : List SExpr)
    (queues : Queues) : Prop where
  valid : Valid index history
  ordered : Ordered queues
  payloads : FromCandidates ranked queues

theorem wake_ordered (ready : Expression → Bool) (origin : Option Rank)
    (input : List Item) (queues : Queues) (ordered : Ordered queues) :
    Ordered (wake ready origin input queues) := by
  induction input generalizing queues with
  | nil => exact ordered
  | cons item rest ih =>
      rw [PlainBnfWakeSourceExecution.wake_cons]
      apply ih
      unfold PlainBnfWakeSourceExecution.wakeStep
      split
      · split
        · exact PlainBnfWakeSourceExecution.enqueue_ordered origin item queues ordered
        · exact ordered
      · exact ordered

theorem initial_invariant (productive : Bool) (ranked : List Item)
    (lexicals : List LexicalDeclaration) :
    Invariant ranked .empty [] (initialQueues productive ranked lexicals) :=
  ⟨PlainBnfKnownNamesSourceExecution.valid_empty,
    wake_ordered _ none ranked (.nil, .nil, .empty) ⟨.nil, .nil⟩,
    PlainBnfControllerPayloadProvenance.initialQueues productive ranked lexicals⟩

theorem rollover (ranked : List Item) (index : NameIndex) (history : List SExpr)
    (following : Heap HeapItem) (scheduled : NameIndex)
    (before : Invariant ranked index history (.nil, following, scheduled)) :
    Invariant ranked index history (following, .nil, scheduled) :=
  ⟨before.valid, ⟨before.ordered.2, .nil⟩,
    PlainBnfControllerPayloadProvenance.rollover_preserves ranked following scheduled before.payloads⟩

theorem publication (productive : Bool) (ranked : List Item)
    (lexicals : List LexicalDeclaration) (index : NameIndex) (history : List SExpr)
    (item : Item) (children following : Heap HeapItem) (scheduled : NameIndex)
    (before : Invariant ranked index history
      (.node (heapItem item) children .nil, following, scheduled)) :
    Invariant ranked (publishedIndex item index) (publishedHistory item history)
      (publishedQueues productive item
        (PlainBnfStructuredReverseDependencies.bucket ranked item.2.name lexicals)
        history lexicals children following scheduled) :=
  ⟨PlainBnfRunSourceExecution.published_valid item index history before.valid,
    wake_ordered _ (some item.1) _ _
      (PlainBnfControllerQueuePreservation.pop_ordered (heapItem item) children following scheduled before.ordered),
    PlainBnfControllerPayloadProvenance.publishedQueues productive ranked item history lexicals
      children following scheduled before.ordered before.payloads⟩

/-- Source semideterminism uses finite fuel induction, not a proof that Run
terminates. The actual reverse-index execution supplies every recursive bucket. -/
theorem run_answers_length_le_one (productive : Bool) (ranked : List Item)
    (lexicals : List LexicalDeclaration) (reverse : NameIndex)
    (reverseExecuted : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall ranked lexicals .empty) (result (trie reverse)))
    (fuel : Nat) (index : NameIndex) (history : List SExpr) (queues : Queues)
    (invariant : Invariant ranked index history queues) :
    (rewriteAt (engineBasePremises relations) language fuel
      (runCall productive reverse lexicals index history queues)).length ≤ 1 := by
  induction fuel generalizing index history queues with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
      rcases queues with ⟨current, following, scheduled⟩
      cases current with
      | nil =>
          cases following with
          | nil => simp [run_done_answers]
          | node payload children siblings =>
              rw [run_rollover_answers]
              exact ih index history _
                (rollover ranked index history (.node payload children siblings) scheduled invariant)
      | node payload children siblings =>
          have noSiblings : siblings = .nil := by cases invariant.ordered.1; rfl
          subst siblings
          obtain ⟨item, _, same⟩ := invariant.payloads payload
            (by simp [contents, PlainBnfPairingHeapObservation.contents])
          subst payload
          have bucket := PlainBnfStructuredReverseDependencies.execution_lookup_bucket
            ranked item.2.name lexicals reverse reverseExecuted
          rw [run_publish_answers productive fuel item _ reverse index history lexicals
            children following scheduled invariant.valid bucket]
          split
          · exact ih _ _ _ (publication productive ranked lexicals index history item
              children following scheduled invariant)
          · simp

theorem closure_answers_length_le_one (productive : Bool) (ranked : List Item)
    (lexicals : List LexicalDeclaration) (reverse : NameIndex)
    (reverseExecuted : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall ranked lexicals .empty) (result (trie reverse)))
    (fuel : Nat) :
    (rewriteAt (engineBasePremises relations) language fuel
      (closureCall productive ranked reverse lexicals)).length ≤ 1 := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
      rw [closure_answers]
      split
      · exact run_answers_length_le_one productive ranked lexicals reverse reverseExecuted
          fuel .empty [] _ (initial_invariant productive ranked lexicals)
      · simp

/-- The actual source reverse fold always supplies the premise above. This
corollary does not posit an oracle that returns the completed reverse index. -/
theorem source_reverse_closure_answers_length_le_one (productive : Bool) (ranked : List Item)
    (lexicals : List LexicalDeclaration) (fuel : Nat) :
    (rewriteAt (engineBasePremises relations) language fuel
      (closureCall productive ranked
        (PlainBnfReverseIndexSourceExecution.reverseIndex ranked lexicals .empty) lexicals)).length ≤ 1 :=
  closure_answers_length_le_one productive ranked lexicals _
    ((PlainBnfReverseIndexSourceExecution.reverse_step_iff ranked lexicals .empty _).mpr rfl) fuel

/-- Equal answers remain separate occurrences. This excludes repetition;
it is stronger than uniqueness after observing a set of answer values. -/
theorem closure_cannot_repeat_answer (productive : Bool) (ranked : List Item)
    (lexicals : List LexicalDeclaration) (reverse : NameIndex)
    (reverseExecuted : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall ranked lexicals .empty) (result (trie reverse)))
    (fuel : Nat) (answer : Pattern) :
    rewriteAt (engineBasePremises relations) language fuel
      (closureCall productive ranked reverse lexicals) ≠ [answer, answer] := by
  intro duplicate
  have bounded := closure_answers_length_le_one productive ranked lexicals reverse reverseExecuted fuel
  rw [duplicate] at bounded
  simp at bounded

/-- Empty ranked input is covered and really returns one empty packet after
the two source calls. The reverse trie is not consulted on this input. -/
theorem empty_closure_answers (productive : Bool) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) (fuel : Nat) :
    rewriteAt (engineBasePremises relations) language fuel
      (closureCall productive [] reverse lexicals) =
      if 1 < fuel then [result (known (.empty : NameIndex) [])] else [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [closure_answers]
      simp [PlainBnfRunSourceExecution.closureHeight,
        PlainBnfWakeContextualExecution.wakeHeight, initialQueues,
        PlainBnfWakeSourceExecution.wake_nil, run_done_answers]

theorem empty_closure_step_iff (productive : Bool) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) (output : Pattern) :
    Step (engineBasePremises relations) language
      (closureCall productive [] reverse lexicals) output ↔
      output = result (known (.empty : NameIndex) []) := by
  rw [PlainBnfRunSourceExecution.closure_iff]
  simpa [initialQueues, PlainBnfWakeSourceExecution.wake_nil] using
    PlainBnfRunSourceExecution.run_done productive reverse lexicals .empty [] .empty output

/-- Equal names and equal ranks are not excluded by the cardinality theorem.
Both complete input occurrences remain in the actual source input list. -/
theorem duplicate_names_and_ranks_are_covered (productive : Bool) (item : Item)
    (lexicals : List LexicalDeclaration) (fuel : Nat) :
    ¬ (([item, item] : List Item).map (fun entry => entry.2.name)).Nodup ∧
    ¬ (([item, item] : List Item).map Prod.fst).Nodup ∧
    (rewriteAt (engineBasePremises relations) language fuel
      (closureCall productive [item, item]
        (PlainBnfReverseIndexSourceExecution.reverseIndex [item, item] lexicals .empty)
        lexicals)).length ≤ 1 :=
  ⟨by simp, by simp,
    source_reverse_closure_answers_length_le_one productive [item, item] lexicals fuel⟩

private def unresolvedItem : Item :=
  (.zero, ⟨"defined", ⟨[⟨[.reference "missing" ⟨0, 1⟩], ⟨0, 1⟩⟩], ⟨0, 1⟩⟩, ⟨0, 1⟩⟩)

/-- The referenced name is absent from both the definition and lexical
inventory. The occurrence bound is not a proof of successful validation. -/
theorem unresolved_reference_is_covered (productive : Bool) (fuel : Nat) :
    unresolvedItem.2.expression.referenceNames = ["missing"] ∧
    "missing" ∉ ([unresolvedItem].map (fun entry => entry.2.name)) ∧
    (rewriteAt (engineBasePremises relations) language fuel
      (closureCall productive [unresolvedItem]
        (PlainBnfReverseIndexSourceExecution.reverseIndex [unresolvedItem] [] .empty) [])).length ≤ 1 :=
  ⟨rfl, by decide,
    source_reverse_closure_answers_length_le_one productive [unresolvedItem] [] fuel⟩

#print axioms initial_invariant
#print axioms publication
#print axioms run_answers_length_le_one
#print axioms closure_answers_length_le_one
#print axioms source_reverse_closure_answers_length_le_one
#print axioms closure_cannot_repeat_answer
#print axioms empty_closure_answers
#print axioms empty_closure_step_iff
#print axioms duplicate_names_and_ranks_are_covered
#print axioms unresolved_reference_is_covered

end Mettapedia.GSLT.Parsing.PlainBnfControllerStructuralOccurrences
