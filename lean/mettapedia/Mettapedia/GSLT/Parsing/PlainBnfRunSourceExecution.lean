import Mettapedia.GSLT.Parsing.PlainBnfWakeContextualExecution
import Mettapedia.GSLT.Parsing.PlainBnfHeapCombineSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfReverseReferencesSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfRunSourceFamily

/-!
# Authored discovery Run and Closure clause execution

The observations here unfold the existing controller calls. They do not
introduce a second Run evaluator or assert whole-loop termination. Publishing
retains the complete known-name packet, including its reversed history, and
uses actual heap, append, lookup, dependent-bucket, and Wake source calls.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfRunSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList)
open PlainBnfGraphNameTrie (Trie lookup insertFirst)
open PlainBnfCollectorSourceExecution (name)
open PlainBnfSourceRank (Rank)
open PlainBnfReverseIndexSourceExecution (Item key node nodes)
open PlainBnfWakeSourceExecution (Queues heapItem wake encodeQueues)
open PlainBnfWakeContextualExecution (NameIndex modeTag meaning wakeCall)
open PlainBnfStructuredDenotation (LexicalDeclaration)
open PlainBnfReferenceCollectionSourceExecution (declarations)
open PlainBnfKnownNamesSourceExecution (known Valid)
open PlainBnfTrieSourceExecution (call result trie)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfHeapSourceExecution (itemLE)
open Batteries.PairingHeapImp (Heap)
open PlainBnfRunSourceFamily (language rules observedRules rules_exact)
open PlainBnfIndexedCollectorSourceExecution (headedBy)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def runCall (productive : Bool) (reverse : NameIndex) (lexicals : List LexicalDeclaration)
    (index : NameIndex) (history : List SExpr) (queues : Queues) : Pattern :=
  call "BNFDiscoveryRunV1" [modeTag productive, trie reverse, declarations lexicals,
    known index history, encodeQueues queues]

def closureCall (productive : Bool) (ranked : List Item) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFDiscoveryClosureV1" [modeTag productive, nodes ranked, trie reverse, declarations lexicals]

/-- The source's append changes the original trie and prepends to its
reversed history. It does not replace that packet by a membership set. -/
def publishedIndex (item : Item) (index : NameIndex) : NameIndex :=
  insertFirst (key item.2.name) (name (key item.2.name)) index

def publishedHistory (item : Item) (history : List SExpr) : List SExpr :=
  name (key item.2.name) :: history

theorem published_valid (item : Item) (index : NameIndex) (history : List SExpr)
    (valid : Valid index history) : Valid (publishedIndex item index) (publishedHistory item history) :=
  PlainBnfKnownNamesSourceExecution.valid_append (key item.2.name) index history valid

/-- Mathematical observation of the actual combine-then-Wake source calls.
The reverse-reference bucket is supplied as an explicit decoded input;
its agreement with the reverse trie remains a theorem premise. -/
def publishedQueues (productive : Bool) (item : Item) (dependents : List Item)
    (history : List SExpr) (lexicals : List LexicalDeclaration)
    (children following : Heap PlainBnfHeapSourceExecution.Item) (scheduled : NameIndex) : Queues :=
  wake (meaning productive (publishedHistory item history) lexicals) (some item.1) dependents
    (children.combine itemLE, following, scheduled)

def initialQueues (productive : Bool) (ranked : List Item)
    (lexicals : List LexicalDeclaration) : Queues :=
  wake (meaning productive [] lexicals) none ranked (.nil, .nil, .empty)

/-- Depth of the five finite prerequisite calls before Run recurs. This
does not assign a termination bound or a final answer to Run itself. -/
def publishHeight (productive : Bool) (item : Item) (dependents : List Item)
    (reverse index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (children following : Heap PlainBnfHeapSourceExecution.Item) (scheduled : NameIndex) : Nat :=
  max (PlainBnfHeapCombineSourceExecution.combineHeight children)
    (max (PlainBnfTrieSourceExecution.insertHeight (key item.2.name) index + 1)
      (max (PlainBnfTrieSourceExecution.lookupHeight (key item.2.name) reverse)
        (max 0 (PlainBnfWakeContextualExecution.wakeHeight productive (some item.1)
          (publishedIndex item index) (publishedHistory item history) lexicals dependents
          (children.combine itemLE, following, scheduled)))))

def closureHeight (productive : Bool) (ranked : List Item)
    (lexicals : List LexicalDeclaration) : Nat :=
  PlainBnfWakeContextualExecution.wakeHeight productive none .empty [] lexicals ranked (.nil, .nil, .empty)

/-- The final source result binder passes complete unary tuples without
dropping or reordering occurrences. Its payload need not be decoded data. -/
private theorem final_result_binding (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursive : Pattern → List Pattern) (input : Pattern) (bindings : Bindings)
    (fresh : bindings.find? (fun entry => entry.1 == "?result") = none)
    (shapes : ∀ output ∈ recursive (applyBindings bindings input),
      ∃ payload, output = Pattern.apply "source-sexpr-list-v1" [payload]) :
    (premisesUsing base language recursive
      [.congruence input (.apply "source-sexpr-list-v1" [.fvar "?result"])] bindings).map
        (fun final => applyBindings final (.apply "source-sexpr-list-v1" [.fvar "?result"])) =
      recursive (applyBindings bindings input) := by
  simp only [premisesUsing, premiseStepUsing, List.map_flatMap]
  calc
    _ = (recursive (applyBindings bindings input)).flatMap (fun output => [output]) := by
      rw [List.flatMap_assoc]
      apply List.flatMap_congr
      intro output member
      obtain ⟨payload, rfl⟩ := shapes output member
      simp [matchPattern, matchArgs, mergeBindings, List.foldlM, fresh, applyBindings]
    _ = _ := by simp

/-- Enlarging only the recursive call answers preserves an existing premise
derivation. This is a local proof about the established contextual engine. -/
private theorem premises_mono (base : BasePremiseEvaluator) (language : LanguageDef)
    (first second : Pattern → List Pattern) (more : ∀ input, first input ⊆ second input)
    (premises : List Premise) (bindings : Bindings) :
    premisesUsing base language first premises bindings ⊆
      premisesUsing base language second premises bindings := by
  induction premises generalizing bindings with
  | nil => exact List.Subset.refl _
  | cons premise rest ih =>
      intro final member
      obtain ⟨middle, headMember, tailMember⟩ := List.mem_flatMap.mp member
      apply List.mem_flatMap.mpr
      refine ⟨middle, ?_, ih middle tailMember⟩
      cases premise with
      | congruence source target =>
          obtain ⟨candidate, produced, matched, bound, merged⟩ :=
            (by simpa only [premiseStepUsing, List.mem_flatMap, List.mem_filterMap] using headMember)
          simp only [premiseStepUsing, List.mem_flatMap, List.mem_filterMap]
          exact ⟨candidate, more _ produced, matched, bound, merged⟩
      | _ => exact headMember

private theorem rule_mono (base : BasePremiseEvaluator) (language : LanguageDef)
    (first second : Pattern → List Pattern) (more : ∀ input, first input ⊆ second input)
    (rule : RewriteRule) (source : Pattern) :
    applyRuleUsing base language first rule source ⊆
      applyRuleUsing base language second rule source := by
  intro output member
  obtain ⟨initial, matched, final, premises, rfl⟩ :=
    (by simpa only [applyRuleUsing, List.mem_flatMap, List.mem_map] using member)
  simp only [applyRuleUsing, List.mem_flatMap, List.mem_map]
  exact ⟨initial, matched, final, premises_mono base language first second more _ _ premises, rfl⟩

private theorem depth_succ (base : BasePremiseEvaluator) (language : LanguageDef)
    (fuel : Nat) (source : Pattern) :
    rewriteAt base language fuel source ⊆ rewriteAt base language (fuel + 1) source := by
  induction fuel generalizing source with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
      intro output member
      obtain ⟨rule, present, returned⟩ := List.mem_flatMap.mp member
      apply List.mem_flatMap.mpr
      exact ⟨rule, present, rule_mono base language _ _ ih rule source returned⟩

theorem depth_mono (base : BasePremiseEvaluator) (language : LanguageDef)
    {fuel later : Nat} (more : fuel ≤ later) (source : Pattern) :
    rewriteAt base language fuel source ⊆ rewriteAt base language later source := by
  induction more with
  | refl => exact List.Subset.refl _
  | @step later _ ih => exact List.Subset.trans ih (depth_succ base language later source)

private theorem run_head (productive : Bool) (reverse : NameIndex) (lexicals : List LexicalDeclaration)
    (index : NameIndex) (history : List SExpr) (queues : Queues) :
    headedBy PlainBnfRunSourceFamily.runHeads (runCall productive reverse lexicals index history queues) = true := by
  simp [headedBy, PlainBnfRunSourceFamily.runHeads, runCall, call, encode, encodeList]

private theorem closure_head (productive : Bool) (ranked : List Item) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) :
    headedBy PlainBnfRunSourceFamily.runHeads (closureCall productive ranked reverse lexicals) = true := by
  simp [headedBy, PlainBnfRunSourceFamily.runHeads, closureCall, call, encode, encodeList]

private theorem rhs_shape (rule : RewriteRule) (member : rule ∈ rules) :
    ∃ body, rule.right = Pattern.apply "source-sexpr-list-v1" [body] := by
  rw [rules_exact] at member
  simp only [observedRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- This shape follows from the four actual rule RHSs, not from assumed
correctness of any recursive Run answer or a source-data decoder. -/
theorem answers_are_result_tuples (fuel : Nat) (source : Pattern)
    (headed : headedBy PlainBnfRunSourceFamily.runHeads source = true) :
    ∀ output ∈ rewriteAt (engineBasePremises relations) language fuel source,
      ∃ payload, output = Pattern.apply "source-sexpr-list-v1" [payload] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
      intro output member
      rw [PlainBnfRunSourceFamily.run_rewriteAt fuel source headed] at member
      obtain ⟨rule, present, returned⟩ := List.mem_flatMap.mp member
      simp only [applyRuleUsing, List.mem_flatMap, List.mem_map] at returned
      obtain ⟨initial, _, final, _, rfl⟩ := returned
      obtain ⟨body, shape⟩ := rhs_shape rule present
      rw [applyBindingsForRule_eq_syntactic, shape, applyBindings]
      exact ⟨_, rfl⟩

theorem run_done_answers (productive : Bool) (fuel : Nat) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) (index : NameIndex) (history : List SExpr)
    (scheduled : NameIndex) :
    rewriteAt (engineBasePremises relations) language fuel
      (runCall productive reverse lexicals index history (.nil, .nil, scheduled)) =
      if 0 < fuel then [result (known index history)] else [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [PlainBnfRunSourceFamily.run_rewriteAt fuel _ (run_head _ _ _ _ _ _)]
      simp [rules_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
        applyRuleUsing, runCall, encodeQueues, PlainBnfScheduleSourceExecution.queues,
        PlainBnfHeapSourceExecution.heap, call, result, pattern, patternList,
        SourceIntegerProvider.sourceVariableToken, encode, encodeList,
        matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

theorem run_done (productive : Bool) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) (index : NameIndex) (history : List SExpr)
    (scheduled : NameIndex) (output : Pattern) :
    Step (engineBasePremises relations) language
      (runCall productive reverse lexicals index history (.nil, .nil, scheduled)) output ↔
      output = result (known index history) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [run_done_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨1, by simp [run_done_answers]⟩

theorem run_rollover_answers (productive : Bool) (fuel : Nat) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) (index : NameIndex) (history : List SExpr)
    (item : PlainBnfHeapSourceExecution.Item) (children siblings : Heap PlainBnfHeapSourceExecution.Item)
    (scheduled : NameIndex) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (runCall productive reverse lexicals index history (.nil, .node item children siblings, scheduled)) =
    rewriteAt (engineBasePremises relations) language fuel
      (runCall productive reverse lexicals index history (.node item children siblings, .nil, scheduled)) := by
  rw [PlainBnfRunSourceFamily.run_rewriteAt fuel _ (run_head _ _ _ _ _ _)]
  simp [rules_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, runCall, encodeQueues, PlainBnfScheduleSourceExecution.queues,
    PlainBnfHeapSourceExecution.heap, call, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]
  rw [final_result_binding]
  · simp [applyBindings]
  · simp
  · intro output member
    apply answers_are_result_tuples fuel
      (runCall productive reverse lexicals index history (.node item children siblings, .nil, scheduled))
      (run_head _ _ _ _ _ _) output
    simpa [applyBindings, runCall, encodeQueues, PlainBnfScheduleSourceExecution.queues,
      PlainBnfHeapSourceExecution.heap, call, encode, encodeList] using member

theorem run_rollover_iff (productive : Bool) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) (index : NameIndex) (history : List SExpr)
    (item : PlainBnfHeapSourceExecution.Item) (children siblings : Heap PlainBnfHeapSourceExecution.Item)
    (scheduled : NameIndex) (output : Pattern) :
    Step (engineBasePremises relations) language
      (runCall productive reverse lexicals index history (.nil, .node item children siblings, scheduled)) output ↔
    Step (engineBasePremises relations) language
      (runCall productive reverse lexicals index history (.node item children siblings, .nil, scheduled)) output := by
  rw [← exists_mem_rewriteAt_iff_step, ← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    cases fuel with
    | zero => cases member
    | succ fuel => exact ⟨fuel, by simpa only [run_rollover_answers] using member⟩
  · rintro ⟨fuel, member⟩
    exact ⟨fuel + 1, by simpa only [run_rollover_answers] using member⟩

private theorem wake_answers (productive : Bool) (fuel : Nat) (input : List Item)
    (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language fuel
      (wakeCall productive input origin index history lexicals queues) =
      if PlainBnfWakeContextualExecution.wakeHeight productive origin index history lexicals input queues < fuel then
        [result (encodeQueues (wake (meaning productive history lexicals) origin input queues))] else [] := by
  rw [PlainBnfRunSourceFamily.wake_extension fuel _ (by
    simp [headedBy, wakeCall, call, encode, encodeList,
      PlainBnfWakeSourceFamily.relationHeads, PlainBnfWakeSourceFamily.wakeHeads])]
  exact PlainBnfWakeContextualExecution.wake_answers productive fuel input origin index history lexicals queues valid

theorem closure_answers (productive : Bool) (fuel : Nat) (ranked : List Item) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (closureCall productive ranked reverse lexicals) =
      if closureHeight productive ranked lexicals < fuel then
        rewriteAt (engineBasePremises relations) language fuel
          (runCall productive reverse lexicals .empty [] (initialQueues productive ranked lexicals)) else [] := by
  rw [PlainBnfRunSourceFamily.run_rewriteAt fuel _ (closure_head _ _ _ _)]
  simp [rules_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, closureCall, call, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]
  rw [premisesUsing]
  conv_lhs => arg 2; simp [premiseStepUsing, applyBindings]
  have first := wake_answers productive fuel ranked none .empty [] lexicals (.nil, .nil, .empty)
    PlainBnfKnownNamesSourceExecution.valid_empty
  simp only [wakeCall, PlainBnfScheduleSourceExecution.position, known,
    PlainBnfKnownNamesSourceExecution.names, PlainBnfKnownNamesSourceExecution.namesNil, List.foldr_nil,
    encodeQueues, PlainBnfScheduleSourceExecution.queues,
    PlainBnfHeapSourceExecution.heap, trie, call, result, encode, encodeList] at first
  rw [first]
  split
  · rename_i enough
    simp [closureHeight, enough, matchPattern, matchArgs, mergeBindings, List.foldlM]
    rw [final_result_binding]
    · simp [applyBindings, runCall, known, PlainBnfKnownNamesSourceExecution.names,
        PlainBnfKnownNamesSourceExecution.namesNil, encodeQueues, PlainBnfScheduleSourceExecution.queues,
        initialQueues, call, encode, encodeList, trie]
    · simp
    · intro output member
      apply answers_are_result_tuples fuel
        (runCall productive reverse lexicals .empty [] (initialQueues productive ranked lexicals))
        (run_head _ _ _ _ _ _) output
      simpa [applyBindings, runCall, known, PlainBnfKnownNamesSourceExecution.names,
        PlainBnfKnownNamesSourceExecution.namesNil, encodeQueues, PlainBnfScheduleSourceExecution.queues,
        initialQueues, call, encode, encodeList, trie] using member
  · rename_i insufficient
    simp [closureHeight, insufficient]

theorem closure_iff (productive : Bool) (ranked : List Item) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) (output : Pattern) :
    Step (engineBasePremises relations) language (closureCall productive ranked reverse lexicals) output ↔
    Step (engineBasePremises relations) language
      (runCall productive reverse lexicals .empty [] (initialQueues productive ranked lexicals)) output := by
  rw [← exists_mem_rewriteAt_iff_step, ← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    cases fuel with
    | zero => cases member
    | succ fuel =>
        rw [closure_answers] at member
        split at member
        · exact ⟨fuel, member⟩
        · cases member
  · rintro ⟨fuel, member⟩
    let later := max fuel (closureHeight productive ranked lexicals + 1)
    refine ⟨later + 1, ?_⟩
    rw [closure_answers, if_pos (by dsimp [later]; omega)]
    exact depth_mono _ _ (Nat.le_max_left _ _) _ member

private def publishRule : RewriteRule := rules[2]'(by rw [rules_exact]; decide)
private theorem publishRule_exact : publishRule = observedRules[2]'(by decide) := rfl

private def publishBindings (productive : Bool) (item : Item) (reverse index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration)
    (children following : Heap PlainBnfHeapSourceExecution.Item) (scheduled : NameIndex) : Bindings :=
  [("?mode", encode (modeTag productive)), ("?lexicals", encode (declarations lexicals)),
   ("?following", encode (PlainBnfHeapSourceExecution.heap following)), ("?scheduled", encode (trie scheduled)),
   ("?name", encode (PlainBnfReferenceCollectionSourceExecution.text item.2.name)),
   ("?span", encode (PlainBnfReferenceCollectionSourceExecution.span item.2.span)),
   ("?expression", encode (PlainBnfReferenceCollectionSourceExecution.expression item.2.expression)),
   ("?rank", encode (PlainBnfRankSourceExecution.rank item.1)),
   ("?children", encode (PlainBnfHeapSourceExecution.heap children)),
   ("?known", encode (known index history)), ("?reverse", encode (trie reverse))]

private theorem publish_match (productive : Bool) (item : Item) (reverse index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration)
    (children following : Heap PlainBnfHeapSourceExecution.Item) (scheduled : NameIndex) :
    matchPattern publishRule.left
      (runCall productive reverse lexicals index history (.node (heapItem item) children .nil, following, scheduled)) =
      [publishBindings productive item reverse index history lexicals children following scheduled] := by
  simp [publishRule_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    publishBindings, runCall, encodeQueues, PlainBnfScheduleSourceExecution.queues,
    PlainBnfHeapSourceExecution.heap, PlainBnfWakeSourceExecution.node_wire,
    call, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]
  have matched := PlainBnfWakeContextualExecution.node_match item
  simp [pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode] at matched
  rw [matched]
  simp [List.foldlM]

private theorem publish_only (productive : Bool) (fuel : Nat) (item : Item) (reverse index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration)
    (children following : Heap PlainBnfHeapSourceExecution.Item) (scheduled : NameIndex) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (runCall productive reverse lexicals index history (.node (heapItem item) children .nil, following, scheduled)) =
    applyRuleUsing (engineBasePremises relations) language (rewriteAt (engineBasePremises relations) language fuel)
      publishRule (runCall productive reverse lexicals index history
        (.node (heapItem item) children .nil, following, scheduled)) := by
  rw [PlainBnfRunSourceFamily.run_rewriteAt fuel _ (run_head _ _ _ _ _ _), rules_exact, publishRule_exact]
  simp only [observedRules, List.flatMap_cons, List.flatMap_nil]
  simp [PlainBnfTrieSourceExecution.observedRule, applyRuleUsing,
    runCall, encodeQueues, PlainBnfScheduleSourceExecution.queues, PlainBnfHeapSourceExecution.heap,
    call, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem combine_answers (fuel : Nat) (children : Heap PlainBnfHeapSourceExecution.Item) :
    rewriteAt (engineBasePremises relations) language fuel (PlainBnfHeapCombineSourceExecution.combineCall children) =
      if PlainBnfHeapCombineSourceExecution.combineHeight children < fuel then
        [result (PlainBnfHeapSourceExecution.heap (children.combine itemLE))] else [] := by
  rw [PlainBnfRunSourceFamily.combine_extension fuel _ (by
    simp [headedBy, PlainBnfRunSourceFamily.combineHeads, PlainBnfHeapCombineSourceExecution.combineNames,
      PlainBnfHeapCombineSourceExecution.combineCall, PlainBnfRankSourceExecution.call, encode, encodeList])]
  exact PlainBnfHeapCombineSourceExecution.combine_answers relations fuel children

private theorem append_answers (fuel : Nat) (item : Item) (index : NameIndex) (history : List SExpr) :
    rewriteAt (engineBasePremises relations) language fuel
      (PlainBnfKnownNamesSourceExecution.appendCall (key item.2.name) index history) =
      if PlainBnfTrieSourceExecution.insertHeight (key item.2.name) index + 1 < fuel then
        [result (known (publishedIndex item index) (publishedHistory item history))] else [] := by
  rw [PlainBnfRunSourceFamily.known_extension fuel _ (by
    simp [headedBy, PlainBnfReadinessEnvironment.knownHeads, PlainBnfKnownNamesSourceExecution.knownNames,
      PlainBnfKnownNamesSourceExecution.appendCall, call, encode, encodeList])]
  exact PlainBnfKnownNamesSourceExecution.append_answers fuel (key item.2.name) index history

private theorem lookup_answers (fuel : Nat) (key : List Nat) (index : NameIndex) :
    rewriteAt (engineBasePremises relations) language fuel (PlainBnfTrieSourceExecution.lookupCall key index) =
      if PlainBnfTrieSourceExecution.lookupHeight key index < fuel then
        [result (PlainBnfTrieSourceExecution.value (lookup key index))] else [] := by
  rw [PlainBnfRunSourceFamily.trie_extension fuel _ (by
    simp [headedBy, PlainBnfIndexedCollectorSourceExecution.trieNames,
      PlainBnfTrieSourceExecution.lookupCall, call, encode, encodeList])]
  exact (PlainBnfTrieSourceExecution.lookup_answers fuel).1 key index

/-- Existing premise fields, selected for proof factoring only. -/
private def publishPremise (i : Fin 6) : Premise :=
  publishRule.premises[i.val]'(by have count : publishRule.premises.length = 6 := rfl; omega)

private theorem publish_premises_exact : publishRule.premises =
    [publishPremise 0, publishPremise 1, publishPremise 2, publishPremise 3, publishPremise 4, publishPremise 5] := rfl

section PublicationBindings
variable (productive : Bool) (item : Item) (reverse index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration)
    (children following : Heap PlainBnfHeapSourceExecution.Item) (scheduled : NameIndex)

/-- Proof observations of the actual successive binding lists. -/
private def afterCombineBindings : Bindings :=
  ("?remaining", encode (PlainBnfHeapSourceExecution.heap (children.combine itemLE))) ::
    publishBindings productive item reverse index history lexicals children following scheduled

private def afterAppendBindings : Bindings :=
  ("?nextKnown", encode (known (publishedIndex item index) (publishedHistory item history))) ::
    afterCombineBindings productive item reverse index history lexicals children following scheduled

private def afterLookupBindings : Bindings :=
  ("?lookup", encode (PlainBnfTrieSourceExecution.value (lookup (key item.2.name) reverse))) ::
    afterAppendBindings productive item reverse index history lexicals children following scheduled

private def afterDependentsBindings (dependents : List Item) : Bindings :=
  ("?dependents", encode (nodes dependents)) ::
    afterLookupBindings productive item reverse index history lexicals children following scheduled

private def afterWakeBindings (dependents : List Item) : Bindings :=
  ("?nextQueues", encode (encodeQueues
    (publishedQueues productive item dependents history lexicals children following scheduled))) ::
    afterDependentsBindings productive item reverse index history lexicals children following scheduled dependents

private theorem combine_premise (fuel : Nat) :
    premiseStepUsing (engineBasePremises relations) language (rewriteAt (engineBasePremises relations) language fuel)
      (publishBindings productive item reverse index history lexicals children following scheduled) (publishPremise 0) =
      if PlainBnfHeapCombineSourceExecution.combineHeight children < fuel then
        [afterCombineBindings productive item reverse index history lexicals children following scheduled] else [] := by
  simp [publishPremise, publishRule_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    publishBindings, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode,
    premiseStepUsing, applyBindings]
  have first := combine_answers fuel children
  simp only [PlainBnfHeapCombineSourceExecution.combineCall, PlainBnfRankSourceExecution.call,
    result, encode, encodeList] at first
  rw [first]
  split <;> simp [afterCombineBindings, publishBindings,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem append_premise (fuel : Nat) :
    premiseStepUsing (engineBasePremises relations) language (rewriteAt (engineBasePremises relations) language fuel)
      (afterCombineBindings productive item reverse index history lexicals children following scheduled) (publishPremise 1) =
      if PlainBnfTrieSourceExecution.insertHeight (key item.2.name) index + 1 < fuel then
        [afterAppendBindings productive item reverse index history lexicals children following scheduled] else [] := by
  simp [publishPremise, publishRule_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    afterCombineBindings, publishBindings, PlainBnfReverseIndexSourceExecution.text_wire,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, premiseStepUsing, applyBindings]
  have first := append_answers fuel item index history
  simp only [PlainBnfKnownNamesSourceExecution.appendCall, call, result, encode, encodeList] at first
  rw [first]
  split <;> simp [afterAppendBindings, afterCombineBindings, publishBindings,
    PlainBnfReverseIndexSourceExecution.text_wire, matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem lookup_premise (fuel : Nat) :
    premiseStepUsing (engineBasePremises relations) language (rewriteAt (engineBasePremises relations) language fuel)
      (afterAppendBindings productive item reverse index history lexicals children following scheduled) (publishPremise 2) =
      if PlainBnfTrieSourceExecution.lookupHeight (key item.2.name) reverse < fuel then
        [afterLookupBindings productive item reverse index history lexicals children following scheduled] else [] := by
  simp [publishPremise, publishRule_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    afterAppendBindings, afterCombineBindings, publishBindings, PlainBnfReverseIndexSourceExecution.text_wire,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, premiseStepUsing, applyBindings]
  have first := lookup_answers fuel (key item.2.name) reverse
  simp only [PlainBnfTrieSourceExecution.lookupCall, call, result, encode, encodeList] at first
  rw [first]
  split <;> simp [afterLookupBindings, afterAppendBindings, afterCombineBindings, publishBindings,
    PlainBnfReverseIndexSourceExecution.text_wire, matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem dependents_premise (fuel : Nat) (dependents : List Item)
    (bucket : PlainBnfReverseReferencesSourceExecution.dependents (lookup (key item.2.name) reverse) = nodes dependents) :
    premiseStepUsing (engineBasePremises relations) language (rewriteAt (engineBasePremises relations) language fuel)
      (afterLookupBindings productive item reverse index history lexicals children following scheduled) (publishPremise 3) =
      if 0 < fuel then
        [afterDependentsBindings productive item reverse index history lexicals children following scheduled dependents] else [] := by
  simp [publishPremise, publishRule_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    afterLookupBindings, afterAppendBindings, afterCombineBindings, publishBindings,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, premiseStepUsing, applyBindings]
  have first := PlainBnfRunSourceFamily.dependents_answers fuel (lookup (key item.2.name) reverse)
  rw [bucket] at first
  simp only [PlainBnfReverseReferencesSourceExecution.dependentsCall, call, result, encode, encodeList] at first
  rw [first]
  split <;> simp [afterDependentsBindings, afterLookupBindings, afterAppendBindings, afterCombineBindings, publishBindings,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem wake_premise (fuel : Nat) (dependents : List Item) (valid : Valid index history) :
    premiseStepUsing (engineBasePremises relations) language (rewriteAt (engineBasePremises relations) language fuel)
      (afterDependentsBindings productive item reverse index history lexicals children following scheduled dependents)
      (publishPremise 4) =
      if PlainBnfWakeContextualExecution.wakeHeight productive (some item.1)
          (publishedIndex item index) (publishedHistory item history) lexicals dependents
          (children.combine itemLE, following, scheduled) < fuel then
        [afterWakeBindings productive item reverse index history lexicals children following scheduled dependents] else [] := by
  simp [publishPremise, publishRule_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    afterDependentsBindings, afterLookupBindings, afterAppendBindings, afterCombineBindings, publishBindings,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, premiseStepUsing, applyBindings]
  have first := wake_answers productive fuel dependents (some item.1)
    (publishedIndex item index) (publishedHistory item history) lexicals
    (children.combine itemLE, following, scheduled) (published_valid item index history valid)
  simp only [wakeCall, PlainBnfScheduleSourceExecution.position, encodeQueues, PlainBnfScheduleSourceExecution.queues,
    call, result, encode, encodeList] at first
  rw [first]
  split <;> simp [afterWakeBindings, afterDependentsBindings, afterLookupBindings, afterAppendBindings,
    afterCombineBindings, publishBindings, publishedQueues, encodeQueues, PlainBnfScheduleSourceExecution.queues,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem publish_tail_result (fuel : Nat) (dependents : List Item) :
    (premisesUsing (engineBasePremises relations) language
      (rewriteAt (engineBasePremises relations) language fuel) [publishPremise 5]
      (afterWakeBindings productive item reverse index history lexicals children following scheduled dependents)).map
      (fun final => applyBindingsForRule language publishRule final) =
    rewriteAt (engineBasePremises relations) language fuel
      (runCall productive reverse lexicals (publishedIndex item index) (publishedHistory item history)
        (publishedQueues productive item dependents history lexicals children following scheduled)) := by
  simp only [applyBindingsForRule_eq_syntactic]
  simp only [publishPremise, publishRule_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    List.getElem_cons_succ, List.getElem_cons_zero]
  simp [pattern, patternList, SourceIntegerProvider.sourceVariableToken]
  rw [final_result_binding]
  · simp [afterWakeBindings, afterDependentsBindings, afterLookupBindings, afterAppendBindings,
      afterCombineBindings, publishBindings, applyBindings, runCall, call, encode, encodeList]
  · simp [afterWakeBindings, afterDependentsBindings, afterLookupBindings, afterAppendBindings,
      afterCombineBindings, publishBindings]
  · intro output member
    apply answers_are_result_tuples fuel
      (runCall productive reverse lexicals (publishedIndex item index) (publishedHistory item history)
        (publishedQueues productive item dependents history lexicals children following scheduled))
      (run_head _ _ _ _ _ _) output
    simpa [afterWakeBindings, afterDependentsBindings, afterLookupBindings, afterAppendBindings,
      afterCombineBindings, publishBindings, applyBindings, runCall, call, encode, encodeList] using member

end PublicationBindings

/-- Exact finite unfolding of the authored publication clause. The five
prerequisites really execute before the unchanged recursive Run call. -/
theorem run_publish_answers (productive : Bool) (fuel : Nat) (item : Item) (dependents : List Item)
    (reverse index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (children following : Heap PlainBnfHeapSourceExecution.Item) (scheduled : NameIndex)
    (valid : Valid index history)
    (bucket : PlainBnfReverseReferencesSourceExecution.dependents (lookup (key item.2.name) reverse) = nodes dependents) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (runCall productive reverse lexicals index history
        (.node (heapItem item) children .nil, following, scheduled)) =
      if publishHeight productive item dependents reverse index history lexicals children following scheduled < fuel then
        rewriteAt (engineBasePremises relations) language fuel
          (runCall productive reverse lexicals (publishedIndex item index) (publishedHistory item history)
            (publishedQueues productive item dependents history lexicals children following scheduled)) else [] := by
  rw [publish_only, applyRuleUsing, matchPatternForRule_eq_syntactic, publish_match]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [publish_premises_exact, premisesUsing, combine_premise]
  split
  · rename_i combined
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [premisesUsing, append_premise]
    split
    · rename_i appended
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [premisesUsing, lookup_premise]
      split
      · rename_i lookedUp
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [premisesUsing, dependents_premise _ _ _ _ _ _ _ _ _ _ dependents bucket]
        split
        · rename_i obtained
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rw [premisesUsing, wake_premise _ _ _ _ _ _ _ _ _ _ dependents valid]
          split
          · rename_i awakened
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
            rw [publish_tail_result]
            simp [publishHeight, combined, appended, lookedUp, awakened]
          · rename_i notAwakened
            simp [publishHeight, notAwakened]
        · rename_i notObtained
          omega
      · rename_i notLookedUp
        simp [publishHeight, notLookedUp]
    · rename_i notAppended
      simp [publishHeight, notAppended]
  · rename_i notCombined
    simp [publishHeight, notCombined]

/-- Publishing preserves the arbitrary final answer exactly, in both
directions. This relates two actual source calls; neither call's termination
or final answer is assumed or manufactured. -/
theorem run_publish_iff (productive : Bool) (item : Item) (dependents : List Item)
    (reverse index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (children following : Heap PlainBnfHeapSourceExecution.Item) (scheduled : NameIndex)
    (valid : Valid index history)
    (bucket : PlainBnfReverseReferencesSourceExecution.dependents (lookup (key item.2.name) reverse) = nodes dependents)
    (output : Pattern) :
    Step (engineBasePremises relations) language
      (runCall productive reverse lexicals index history
        (.node (heapItem item) children .nil, following, scheduled)) output ↔
    Step (engineBasePremises relations) language
      (runCall productive reverse lexicals (publishedIndex item index) (publishedHistory item history)
        (publishedQueues productive item dependents history lexicals children following scheduled)) output := by
  rw [← exists_mem_rewriteAt_iff_step, ← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    cases fuel with
    | zero => cases member
    | succ fuel =>
        rw [run_publish_answers _ _ _ _ _ _ _ _ _ _ _ valid bucket] at member
        split at member
        · exact ⟨fuel, member⟩
        · cases member
  · rintro ⟨fuel, member⟩
    let later := max fuel
      (publishHeight productive item dependents reverse index history lexicals children following scheduled + 1)
    refine ⟨later + 1, ?_⟩
    rw [run_publish_answers _ _ _ _ _ _ _ _ _ _ _ valid bucket, if_pos (by dsimp [later]; omega)]
    exact depth_mono _ _ (Nat.le_max_left _ _) _ member

/-- Successful termination returns the exact trie and ordered occurrence
history, rather than merely an extensionally equal membership set. -/
theorem run_done_decoded_iff (productive : Bool) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) (index : NameIndex) (history : List SExpr)
    (scheduled afterIndex : NameIndex) (afterHistory : List SExpr) :
    Step (engineBasePremises relations) language
      (runCall productive reverse lexicals index history (.nil, .nil, scheduled))
      (result (known afterIndex afterHistory)) ↔ afterIndex = index ∧ afterHistory = history := by
  rw [run_done, PlainBnfTrieSourceExecution.result_injective.eq_iff,
    PlainBnfKnownNamesSourceExecution.known_eq_iff]

theorem run_done_cannot_drop_occurrence (productive : Bool) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) (index scheduled : NameIndex)
    (occurrence : SExpr) (history : List SExpr) :
    ¬ Step (engineBasePremises relations) language
      (runCall productive reverse lexicals index (occurrence :: occurrence :: history) (.nil, .nil, scheduled))
      (result (known index (occurrence :: history))) := by
  rw [run_done_decoded_iff]
  rintro ⟨_, same⟩
  have lengths := congrArg List.length same
  simp only [List.length_cons] at lengths
  omega

/-- The actual publication clause requires a sibling-free current root.
This malformed shape is stuck, not silently normalized by the theorem. -/
theorem run_sibling_root_answers (productive : Bool) (fuel : Nat) (reverse index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (item : Item)
    (children : Heap PlainBnfHeapSourceExecution.Item) (sibling : PlainBnfHeapSourceExecution.Item)
    (siblingChildren siblingSiblings following : Heap PlainBnfHeapSourceExecution.Item) (scheduled : NameIndex) :
    rewriteAt (engineBasePremises relations) language fuel
      (runCall productive reverse lexicals index history
        (.node (heapItem item) children (.node sibling siblingChildren siblingSiblings), following, scheduled)) = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [PlainBnfRunSourceFamily.run_rewriteAt fuel _ (run_head _ _ _ _ _ _)]
      simp [rules_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
        applyRuleUsing, runCall, encodeQueues, PlainBnfScheduleSourceExecution.queues,
        PlainBnfHeapSourceExecution.heap, call, pattern, patternList,
        SourceIntegerProvider.sourceVariableToken, encode, encodeList,
        matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem run_sibling_root_stuck (productive : Bool) (reverse index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (item : Item)
    (children : Heap PlainBnfHeapSourceExecution.Item) (sibling : PlainBnfHeapSourceExecution.Item)
    (siblingChildren siblingSiblings following : Heap PlainBnfHeapSourceExecution.Item) (scheduled : NameIndex)
    (output : Pattern) :
    ¬ Step (engineBasePremises relations) language
      (runCall productive reverse lexicals index history
        (.node (heapItem item) children (.node sibling siblingChildren siblingSiblings), following, scheduled)) output := by
  rw [← exists_mem_rewriteAt_iff_step]
  simp [run_sibling_root_answers]

end Mettapedia.GSLT.Parsing.PlainBnfRunSourceExecution
