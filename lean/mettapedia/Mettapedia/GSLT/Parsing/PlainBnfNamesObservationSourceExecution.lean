import Mettapedia.GSLT.Parsing.PlainBnfRunSourceFamily
import Mettapedia.GSLT.Parsing.PlainBnfControllerReferenceHistory

/-!
# Ordered names observation in the actual controller source family

The three discovery rules at source positions 2–4 already have exact
execution proofs in KnownNamesSourceExecution. This module reuses those
proofs and the existing conservative extension into the controller family.
It connects the stored reversed history to the forward reference-event names,
retaining occurrence order, duplicate payloads, and exact finite-depth answers.
No source program, decoder, evaluator, or runtime data carrier is added.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfNamesObservationSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises rewriteAt exists_mem_rewriteAt_iff_step)
open SourceSExprPatternCodec (encode encodeList)
open PlainBnfCollectorSourceExecution (NameScalarCodec)
open PlainBnfGraphNameTrie (Trie)
open PlainBnfKnownNamesSourceExecution (names namesNil reverseOnto reverseCall observeCall)
open PlainBnfTrieSourceExecution (call result result_injective)
open PlainBnfIndexedCollectorSourceExecution (headedBy)
open PlainBnfReadinessEnvironment (knownHeads)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfRunSourceFamily (language)
open PlainBnfStructuredDiscoveryGraph (Definitions nameAt)
open PlainBnfOrderedGraphDiscovery (Event)
open PlainBnfReferenceCollectionSourceExecution (text)

/-- Actual source occurrences and their existing executed mode translation,
not a second hand-written observation family. -/
theorem selected_translation_exact :
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 2).take 3).mapM
      PlainBnfKnownNamesSourceExecution.lowerRule? =
      some ((PlainBnfKnownNamesSourceExecution.knownRules.drop 2).take 3) := rfl

theorem selected_occurrences_exact :
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 2).take 3 =
      ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 2).take 3).zipIdx 2 := rfl

theorem selected_source_exhaustive :
    PlainBnfCollectorSourceAdmission.discoverySource.rewrites.filter (fun row => match row.head with
      | .list (.atom head :: _) => head == "BNFIndexedNamesObserveV1" || head == "BNFDiscoveryReverseNamesV1"
      | _ => false) = (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 2).take 3 := rfl

private theorem reverse_head (history : List SExpr) (before : SExpr) :
    headedBy knownHeads (reverseCall history before) = true := by
  simp [headedBy, reverseCall, call, encode, encodeList, knownHeads,
    PlainBnfKnownNamesSourceExecution.knownNames]

theorem reverse_answers (fuel : Nat) (history : List SExpr) (before : SExpr) :
    rewriteAt (engineBasePremises relations) language fuel (reverseCall history before) =
      if history.length < fuel then [result (reverseOnto history before)] else [] := by
  rw [PlainBnfRunSourceFamily.known_extension fuel _ (reverse_head history before)]
  exact PlainBnfKnownNamesSourceExecution.reverse_answers fuel history before

theorem reverse_step_iff (history : List SExpr) (before : SExpr) (target : Pattern) :
    Step (engineBasePremises relations) language (reverseCall history before) target ↔
      target = result (reverseOnto history before) := by
  rw [← PlainBnfKnownNamesSourceExecution.reverse_step_iff history before target,
    ← exists_mem_rewriteAt_iff_step, ← exists_mem_rewriteAt_iff_step]
  apply exists_congr
  intro fuel
  rw [PlainBnfRunSourceFamily.known_extension fuel _ (reverse_head history before)]

variable {Scalar : Type} [NameScalarCodec Scalar]

private theorem observe_head (index : Trie SExpr Scalar) (history : List SExpr) :
    headedBy knownHeads (observeCall index history) = true := by
  simp [headedBy, observeCall, call, encode, encodeList, knownHeads,
    PlainBnfKnownNamesSourceExecution.knownNames]

theorem observe_answers (fuel : Nat) (index : Trie SExpr Scalar) (history : List SExpr) :
    rewriteAt (engineBasePremises relations) language fuel (observeCall index history) =
      if history.length + 1 < fuel then [result (names history.reverse)] else [] := by
  rw [PlainBnfRunSourceFamily.known_extension fuel _ (observe_head index history),
    PlainBnfKnownNamesSourceExecution.observe_answers, PlainBnfKnownNamesSourceExecution.reverse_nil_observation]

theorem observe_step_iff (index : Trie SExpr Scalar) (history : List SExpr) (target : Pattern) :
    Step (engineBasePremises relations) language (observeCall index history) target ↔
      target = result (names history.reverse) := by
  rw [← PlainBnfKnownNamesSourceExecution.reverse_nil_observation,
    ← PlainBnfKnownNamesSourceExecution.observe_step_iff index history target,
    ← exists_mem_rewriteAt_iff_step, ← exists_mem_rewriteAt_iff_step]
  apply exists_congr
  intro fuel
  rw [PlainBnfRunSourceFamily.known_extension fuel _ (observe_head index history)]

theorem observe_decoded_step_iff (index : Trie SExpr Scalar) (history output : List SExpr) :
    Step (engineBasePremises relations) language (observeCall index history) (result (names output)) ↔
      output = history.reverse := by
  rw [observe_step_iff, result_injective.eq_iff, PlainBnfKnownNamesSourceExecution.names_injective.eq_iff]

/-- The depth counts actual contextual rule nesting, not elapsed time. -/
theorem observe_depth_boundary (index : Trie SExpr Scalar) (history : List SExpr) :
    rewriteAt (engineBasePremises relations) language (history.length + 1) (observeCall index history) = [] ∧
    ∀ fuel, history.length + 2 ≤ fuel →
      rewriteAt (engineBasePremises relations) language fuel (observeCall index history) =
        [result (names history.reverse)] := by
  constructor
  · simp [observe_answers]
  · intro fuel enough
    rw [observe_answers, if_pos (by omega)]

/-- Observing the terminal replay reverses the stored history once: the old
public prefix is followed by the reference event names in their original order. -/
theorem observe_event_history_answers (fuel : Nat) (definitions : Definitions)
    (events : List (Event definitions.length)) (index : Trie SExpr Scalar) (history : List SExpr) :
    rewriteAt (engineBasePremises relations) language fuel
      (observeCall index (events.foldl (fun current event => text (nameAt definitions event.position) :: current) history)) =
      if events.length + history.length + 1 < fuel then
        [result (names (history.reverse ++ events.map (fun event => text (nameAt definitions event.position))))] else [] := by
  rw [observe_answers, PlainBnfControllerReferenceHistory.history_fold_exact]
  simp

theorem observe_event_history_step_iff (definitions : Definitions) (events : List (Event definitions.length))
    (index : Trie SExpr Scalar) (history : List SExpr) (target : Pattern) :
    Step (engineBasePremises relations) language
      (observeCall index (events.foldl (fun current event => text (nameAt definitions event.position) :: current) history)) target ↔
      target = result (names (history.reverse ++ events.map (fun event => text (nameAt definitions event.position)))) := by
  rw [observe_step_iff, PlainBnfControllerReferenceHistory.history_fold_exact]
  simp

theorem reversed_public_order (index : Trie SExpr Scalar) (first second : SExpr)
    (different : first ≠ second) :
    Step (engineBasePremises relations) language (observeCall index [second, first])
      (result (names [first, second])) ∧
    ¬ Step (engineBasePremises relations) language (observeCall index [second, first])
      (result (names [second, first])) := by
  simp [observe_decoded_step_iff, different, Ne.symm different]

theorem duplicate_occurrences_survive (index : Trie SExpr Scalar) (entry : SExpr) :
    Step (engineBasePremises relations) language (observeCall index [entry, entry])
      (result (names [entry, entry])) ∧
    ¬ Step (engineBasePremises relations) language (observeCall index [entry, entry])
      (result (names [entry])) := by
  simp [observe_decoded_step_iff]

end Mettapedia.GSLT.Parsing.PlainBnfNamesObservationSourceExecution
