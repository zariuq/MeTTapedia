import Mettapedia.GSLT.Parsing.PlainBnfControllerReferenceHistory
import Mettapedia.GSLT.Parsing.PlainBnfRunSourceExecution

/-!
# Structural known-index replay of the existing reference events

Standard list folds apply the source's existing first-binding insertion to
the original trie and prepend names to its original reversed history. The
history law is shared with the reference-history proof. No independent event
interpreter, runtime state, canonical rebuilding, or new lookup operation is
introduced.

Lookup consistency does not determine trie structure: an empty node and the
empty constructor have identical lookups but different encoded packets. Even
zero-event terminal Run execution retains this distinction. The results below
do not identify the reference event trace with an entire source Run execution.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerReferenceIndex

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open PlainBnfOrderedGraphDiscovery (Event)
open PlainBnfStructuredDiscoveryGraph (Definitions nameAt)
open PlainBnfReferenceCollectionSourceExecution (text)
open PlainBnfReverseIndexSourceExecution (Item key)
open PlainBnfGraphNameTrie (Trie lookup insertFirst)
open PlainBnfCollectorSourceExecution (name)
open PlainBnfKnownNamesSourceExecution (Valid known appendCall)
open PlainBnfTrieSourceExecution (scalarRelations result)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfWakeContextualExecution (NameIndex)

/-- Each replay insertion is precisely the existing authored append step,
with its full known-name packet reflected for arbitrary targets. -/
theorem event_append_step_iff (definitions : Definitions) (event : Event definitions.length)
    (index : NameIndex) (history : List SExpr) (target : Pattern) :
    Step (engineBasePremises scalarRelations) PlainBnfKnownNamesSourceExecution.language
      (appendCall (key (nameAt definitions event.position)) index history) target ↔
    target = result (known
      (insertFirst (key (nameAt definitions event.position))
        (text (nameAt definitions event.position)) index)
      (text (nameAt definitions event.position) :: history)) :=
  PlainBnfKnownNamesSourceExecution.append_step_iff _ _ _ _

/-- Source publication and event replay use the same update when the full
published declaration has its established source-position alignment. -/
theorem publication_event_update (definitions : Definitions) (event : Event definitions.length)
    (item : Item) (aligned : item.2 = definitions.get event.position)
    (index : NameIndex) (history : List SExpr) :
    PlainBnfRunSourceExecution.publishedIndex item index =
      insertFirst (key (nameAt definitions event.position))
        (text (nameAt definitions event.position)) index ∧
    PlainBnfRunSourceExecution.publishedHistory item history =
      text (nameAt definitions event.position) :: history := by
  have sameName := congrArg PlainBnfDeclarationSemantics.Definition.name aligned
  change item.2.name = nameAt definitions event.position at sameName
  simp only [PlainBnfRunSourceExecution.publishedIndex,
    PlainBnfRunSourceExecution.publishedHistory, sameName]
  exact ⟨rfl, rfl⟩

/-- Membership-and-payload validity is preserved from the original index;
the history fold retains every event occurrence, even repeated positions. -/
theorem index_history_fold_valid (definitions : Definitions)
    (events : List (Event definitions.length)) (index : NameIndex) (history : List SExpr)
    (valid : Valid index history) :
    Valid
      (events.foldl (fun current event =>
        insertFirst (key (nameAt definitions event.position))
          (text (nameAt definitions event.position)) current) index)
      (events.foldl (fun current event => text (nameAt definitions event.position) :: current) history) := by
  induction events generalizing index history with
  | nil => exact valid
  | cons event rest ih =>
      exact ih _ _ (PlainBnfKnownNamesSourceExecution.valid_append
        (key (nameAt definitions event.position)) index history valid)

theorem index_reverse_history_valid (definitions : Definitions)
    (events : List (Event definitions.length)) (index : NameIndex) (history : List SExpr)
    (valid : Valid index history) :
    Valid
      (events.foldl (fun current event =>
        insertFirst (key (nameAt definitions event.position))
          (text (nameAt definitions event.position)) current) index)
      ((events.map (fun event => text (nameAt definitions event.position))).reverse ++ history) := by
  rw [← PlainBnfControllerReferenceHistory.history_fold_exact]
  exact index_history_fold_valid definitions events index history valid

/-- The reference trie keeps all pre-existing payloads, including when the
caller has not established membership validity. New bindings use the exact
source name; no normalization or last-writer replacement is performed. -/
theorem index_fold_lookup (definitions : Definitions) (events : List (Event definitions.length))
    (index : NameIndex) (query : List Nat) :
    lookup query (events.foldl (fun current event =>
      insertFirst (key (nameAt definitions event.position))
        (text (nameAt definitions event.position)) current) index) =
      (lookup query index).or
        (if query ∈ events.map (fun event => key (nameAt definitions event.position))
          then some (name query) else none) := by
  induction events generalizing index with
  | nil => simp
  | cons event rest ih =>
      rw [List.foldl_cons, ih, PlainBnfGraphNameTrie.lookup_insertFirst]
      by_cases same : query = key (nameAt definitions event.position)
      · subst query
        cases lookup (key (nameAt definitions event.position)) index <;>
          simp [PlainBnfReverseIndexSourceExecution.text_wire]
      · simp only [List.map_cons, List.mem_cons, same, false_or, ↓reduceIte]

theorem existing_payload_survives (definitions : Definitions)
    (events : List (Event definitions.length)) (index : NameIndex)
    (query : List Nat) (payload : SExpr) (found : lookup query index = some payload) :
    lookup query (events.foldl (fun current event =>
      insertFirst (key (nameAt definitions event.position))
        (text (nameAt definitions event.position)) current) index) = some payload := by
  rw [index_fold_lookup, found]
  rfl

/-- Terminal source execution returns both folds verbatim. This only states
the terminal clause, not that an arbitrary event list is a valid source run. -/
theorem terminal_replay_packet_iff (productive : Bool) (definitions : Definitions)
    (events : List (Event definitions.length)) (index : NameIndex) (history : List SExpr)
    (reverse : NameIndex) (lexicals : List PlainBnfStructuredDenotation.LexicalDeclaration)
    (scheduled : NameIndex) (target : Pattern) :
    Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (PlainBnfRunSourceExecution.runCall productive reverse lexicals
        (events.foldl (fun current event =>
          insertFirst (key (nameAt definitions event.position))
            (text (nameAt definitions event.position)) current) index)
        (events.foldl (fun current event => text (nameAt definitions event.position) :: current) history)
        (.nil, .nil, scheduled)) target ↔
      target = result (known
        (events.foldl (fun current event =>
          insertFirst (key (nameAt definitions event.position))
            (text (nameAt definitions event.position)) current) index)
        ((events.map (fun event => text (nameAt definitions event.position))).reverse ++ history)) := by
  rw [PlainBnfRunSourceExecution.run_done,
    PlainBnfControllerReferenceHistory.history_fold_exact]

theorem zero_events_preserve_index (definitions : Definitions) (index : NameIndex) :
    ([] : List (Event definitions.length)).foldl (fun current event =>
      insertFirst (key (nameAt definitions event.position))
        (text (nameAt definitions event.position)) current) index = index := rfl

theorem two_events_keep_exact_index_and_history (definitions : Definitions)
    (first second : Event definitions.length) (index : NameIndex) (history : List SExpr) :
    [first, second].foldl (fun current event =>
      insertFirst (key (nameAt definitions event.position))
        (text (nameAt definitions event.position)) current) index =
      insertFirst (key (nameAt definitions second.position)) (text (nameAt definitions second.position))
        (insertFirst (key (nameAt definitions first.position)) (text (nameAt definitions first.position)) index) ∧
    [first, second].foldl (fun current event => text (nameAt definitions event.position) :: current) history =
      text (nameAt definitions second.position) :: text (nameAt definitions first.position) :: history :=
  ⟨rfl, PlainBnfControllerReferenceHistory.two_events_reverse_exactly definitions first second history⟩

private theorem empty_node_lookup (query : List Nat) :
    lookup query (.node none [] : NameIndex) = none := by
  cases query <;> simp [lookup, PlainBnfGraphNameTrie.valueAt,
    PlainBnfGraphNameTrie.edgesOf, PlainBnfGraphNameTrie.childFor]

theorem lookup_validity_does_not_determine_structure :
    (∀ query : List Nat, lookup query (.node none [] : NameIndex) = lookup query (.empty : NameIndex)) ∧
    Valid (.node none [] : NameIndex) [] ∧ Valid (.empty : NameIndex) [] ∧
    known (.node none [] : NameIndex) [] ≠ known (.empty : NameIndex) [] := by
  refine ⟨?_, ?_, PlainBnfKnownNamesSourceExecution.valid_empty, ?_⟩
  · intro query
    rw [empty_node_lookup, PlainBnfGraphNameTrie.lookup_empty]
  · intro query
    simp [empty_node_lookup]
  · intro same
    have structures := (PlainBnfKnownNamesSourceExecution.known_eq_iff _ _ _ _).mp same
    cases structures.1

/-- Rebuilding the empty history from the empty constructor changes the
actual zero-event terminal packet, despite preserving every lookup and the
full membership-validity invariant. -/
theorem zero_event_terminal_refuses_rebuilt_index (productive : Bool) :
    Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (PlainBnfRunSourceExecution.runCall productive .empty [] (.node none []) [] (.nil, .nil, .empty))
      (result (known (.node none [] : NameIndex) [])) ∧
    ¬ Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (PlainBnfRunSourceExecution.runCall productive .empty [] (.node none []) [] (.nil, .nil, .empty))
      (result (known (PlainBnfKnownNamesSourceExecution.historyIndex ([] : List (List Nat))) [])) := by
  constructor
  · exact (PlainBnfRunSourceExecution.run_done productive .empty [] (.node none []) [] .empty _).mpr rfl
  · rw [PlainBnfRunSourceExecution.run_done]
    intro same
    exact lookup_validity_does_not_determine_structure.2.2.2
      (PlainBnfTrieSourceExecution.result_injective same).symm

end Mettapedia.GSLT.Parsing.PlainBnfControllerReferenceIndex
