import Mettapedia.GSLT.Parsing.PlainBnfRankSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfPairingHeapObservation
import Mettapedia.GSLT.Parsing.PlainBnfIndexedCollectorSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfEnumerationSourceExecution

/-!
# Authored discovery heap merge

The executable rules are translated from the original admitted discovery
source. The independent observation is Batteries' existing pairing heap,
with every ranked definition payload retained. Rank comparison executes its
authored contextual rules; no provider computes a heap result.

This selected source-language connection does not assert generated PeTTa or
native runtime correspondence, whole-scheduler reachability, or heap combine.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfHeapSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList
  applyRuleBindings_of_binderFree binderFree_pattern)
open PlainBnfSourceRank (Rank rankLE compareRank)
open PlainBnfRankSourceExecution (rank order call result compareCall compareHeight)
open PlainBnfIndexedCollectorSourceExecution
  (headedBy premiseClosed closed_extension disjoint_heads_do_not_match)
open Batteries.PairingHeapImp (Heap)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

abbrev Definition := PlainBnfDeclarationSemantics.Definition SExpr SExpr SExpr
abbrev Item := Rank × Definition

def rankedDefinition (item : Item) : SExpr :=
  .list [.atom "BNFDiscoveryDefinitionV1", rank item.1,
    item.2.name, item.2.expression, item.2.span]

def heap : Heap Item → SExpr
  | .nil => .atom "BNFDiscoveryHeapNilV1"
  | .node item children siblings =>
      .list [.atom "BNFDiscoveryHeapV1", rankedDefinition item, heap children, heap siblings]

def itemLE (left right : Item) : Bool := rankLE left.1 right.1

def mode? (name : String) : Option (Nat × Nat) :=
  match name with
  | "BNFDiscoveryHeapMergeV1" => some (2, 1)
  | "BNFDiscoveryHeapMergeAfterCompareV1" => some (3, 1)
  | _ => PlainBnfRankSourceExecution.mode? name

def splitCall? : SExpr → Option (SExpr × SExpr)
  | .list (.atom relation :: arguments) => do
      let (inputs, outputs) ← mode? relation
      if arguments.length = inputs + outputs then
        some (.list (.atom relation :: arguments.take inputs), .list (arguments.drop inputs))
      else none
  | _ => none

def lowerPremise? (source : SExpr) : Option Premise := do
  let (input, output) ← splitCall? source
  some (.congruence (pattern input) (pattern output))

def lowerRule? (source : Rewrite) : Option RewriteRule := do
  let (input, output) ← splitCall? source.head
  let premises ← decodeList lowerPremise? source.body
  some {
    name := source.name
    typeContext := []
    premises := premises
    left := pattern input
    right := pattern output }

def rows : List Rewrite :=
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 22).take 7

def rules? : Option (List RewriteRule) := rows.mapM lowerRule?

theorem rules_present : rules?.isSome = true := rfl

def heapRules : List RewriteRule := rules?.get rules_present

def language : LanguageDef :=
  { name := "PlainBnfAuthoredHeapMerge", types := [], terms := [], equations := [],
    rewrites := PlainBnfRankSourceExecution.language.rewrites ++ heapRules }

theorem language_rewrites : language.rewrites =
    PlainBnfRankSourceExecution.language.rewrites ++ heapRules := rfl

theorem translation_exact : rows.mapM lowerRule? = some heapRules := rfl

theorem source_occurrences_exact : rows.zipIdx 22 =
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 22).take 7 := rfl

theorem source_family_translation_exact :
    (PlainBnfRankSourceExecution.rows ++ rows).mapM lowerRule? = some language.rewrites := rfl

theorem source_rule_count : language.rewrites.length = 22 := rfl

def observed (name : String) (input output : SExpr)
    (premises : List Premise := []) : RewriteRule :=
  PlainBnfTrieSourceExecution.observedRule name input output premises

/-- Checked observations only; the executable language is decoded above. -/
def observedRules : List RewriteRule := [
  observed "bnf-discovery-heap-merge-nil-v1"
    (metta_sexpr% petta "(BNFDiscoveryHeapMergeV1 BNFDiscoveryHeapNilV1 BNFDiscoveryHeapNilV1)")
    (metta_sexpr% petta "(BNFDiscoveryHeapNilV1)"),
  observed "bnf-discovery-heap-merge-left-nil-v1"
    (metta_sexpr% petta "(BNFDiscoveryHeapMergeV1 BNFDiscoveryHeapNilV1 (BNFDiscoveryHeapV1 ?node ?children ?siblings))")
    (metta_sexpr% petta "((BNFDiscoveryHeapV1 ?node ?children BNFDiscoveryHeapNilV1))"),
  observed "bnf-discovery-heap-merge-right-nil-v1"
    (metta_sexpr% petta "(BNFDiscoveryHeapMergeV1 (BNFDiscoveryHeapV1 ?node ?children ?siblings) BNFDiscoveryHeapNilV1)")
    (metta_sexpr% petta "((BNFDiscoveryHeapV1 ?node ?children BNFDiscoveryHeapNilV1))"),
  observed "bnf-discovery-heap-merge-nodes-v1"
    (metta_sexpr% petta "(BNFDiscoveryHeapMergeV1 (BNFDiscoveryHeapV1 (BNFDiscoveryDefinitionV1 ?lr ?ln ?le ?ls) ?lc ?lrest) (BNFDiscoveryHeapV1 (BNFDiscoveryDefinitionV1 ?rr ?rn ?re ?rs) ?rc ?rrest))")
    (metta_sexpr% petta "(?result)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryRankCompareV1 ?lr ?rr)"))
        (pattern (metta_sexpr% petta "(?order)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryHeapMergeAfterCompareV1 ?order (BNFDiscoveryHeapV1 (BNFDiscoveryDefinitionV1 ?lr ?ln ?le ?ls) ?lc ?lrest) (BNFDiscoveryHeapV1 (BNFDiscoveryDefinitionV1 ?rr ?rn ?re ?rs) ?rc ?rrest))"))
        (pattern (metta_sexpr% petta "(?result)"))],
  observed "bnf-discovery-heap-merge-less-v1"
    (metta_sexpr% petta "(BNFDiscoveryHeapMergeAfterCompareV1 BNFDiscoveryLessV1 (BNFDiscoveryHeapV1 ?left ?lc ?ls) (BNFDiscoveryHeapV1 ?right ?rc ?rs))")
    (metta_sexpr% petta "((BNFDiscoveryHeapV1 ?left (BNFDiscoveryHeapV1 ?right ?rc ?lc) BNFDiscoveryHeapNilV1))"),
  observed "bnf-discovery-heap-merge-equal-v1"
    (metta_sexpr% petta "(BNFDiscoveryHeapMergeAfterCompareV1 BNFDiscoveryEqualV1 (BNFDiscoveryHeapV1 ?left ?lc ?ls) (BNFDiscoveryHeapV1 ?right ?rc ?rs))")
    (metta_sexpr% petta "((BNFDiscoveryHeapV1 ?left (BNFDiscoveryHeapV1 ?right ?rc ?lc) BNFDiscoveryHeapNilV1))"),
  observed "bnf-discovery-heap-merge-greater-v1"
    (metta_sexpr% petta "(BNFDiscoveryHeapMergeAfterCompareV1 BNFDiscoveryGreaterV1 (BNFDiscoveryHeapV1 ?left ?lc ?ls) (BNFDiscoveryHeapV1 ?right ?rc ?rs))")
    (metta_sexpr% petta "((BNFDiscoveryHeapV1 ?right (BNFDiscoveryHeapV1 ?left ?lc ?rc) BNFDiscoveryHeapNilV1))")]

theorem rules_exact : heapRules = observedRules := rfl

def rankNames : List String :=
  ["BNFDiscoveryRankNextV1", "BNFDiscoveryRankCompareV1", "BNFDiscoveryRankTieV1"]

def heapNames : List String :=
  ["BNFDiscoveryHeapMergeV1", "BNFDiscoveryHeapMergeAfterCompareV1"]

theorem rank_closed : PlainBnfRankSourceExecution.language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed rankNames)) = true := by
  simp [PlainBnfRankSourceExecution.rules_exact, PlainBnfRankSourceExecution.observedRules,
    PlainBnfRankSourceExecution.observed, premiseClosed, headedBy, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, rankNames, encode]

theorem rank_heads : PlainBnfRankSourceExecution.language.rewrites.all
    (fun rule => headedBy rankNames rule.left) = true := by
  simp [PlainBnfRankSourceExecution.rules_exact, PlainBnfRankSourceExecution.observedRules,
    PlainBnfRankSourceExecution.observed, headedBy, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, rankNames, encode]

theorem heap_heads : heapRules.all (fun rule => headedBy heapNames rule.left) = true := by
  simp [rules_exact, observedRules, observed, PlainBnfTrieSourceExecution.observedRule,
    headedBy, pattern, patternList, SourceIntegerProvider.sourceVariableToken, heapNames, encode]

theorem names_disjoint : List.Disjoint heapNames rankNames := by
  simp [heapNames, rankNames, List.disjoint_left]

theorem rank_conservative_extension (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy rankNames source = true) :
    rewriteAt (engineBasePremises env) language fuel source =
      rewriteAt (engineBasePremises env) PlainBnfRankSourceExecution.language fuel source := by
  apply closed_extension rankNames env _ _ [] heapRules
  · simp [language]
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp rank_closed rule member) premise present
  · intro rule member source headed
    simp only [List.nil_append] at member
    exact disjoint_heads_do_not_match heapNames rankNames names_disjoint _ _
      (List.all_eq_true.mp heap_heads rule member) headed
  · exact headed

theorem skip_unmatched_prefix (base : BasePremiseEvaluator) (lang : LanguageDef)
    (before after : List RewriteRule) (partition : lang.rewrites = before ++ after)
    (fuel : Nat) (source : Pattern)
    (unmatched : ∀ rule ∈ before, matchPattern rule.left source = []) :
    rewriteAt base lang (fuel + 1) source =
      after.flatMap (fun rule => applyRuleUsing base lang (rewriteAt base lang fuel) rule source) := by
  rw [rewriteAt, partition, List.flatMap_append]
  have absent : before.flatMap
      (fun rule => applyRuleUsing base lang (rewriteAt base lang fuel) rule source) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    simp [applyRuleUsing, unmatched rule member]
  rw [absent]
  rfl

private theorem heap_rewriteAt (base : BasePremiseEvaluator) (fuel : Nat) (source : Pattern)
    (headed : headedBy heapNames source = true) :
    rewriteAt base language (fuel + 1) source =
      heapRules.flatMap (fun rule => applyRuleUsing base language
        (rewriteAt base language fuel) rule source) := by
  apply skip_unmatched_prefix base language _ _ language_rewrites
  intro rule member
  exact disjoint_heads_do_not_match rankNames heapNames names_disjoint.symm
    rule.left source (List.all_eq_true.mp rank_heads rule member) headed

def mergeCall (left right : Heap Item) : Pattern :=
  call "BNFDiscoveryHeapMergeV1" [heap left, heap right]

def afterCall (comparison : Ordering) (left right : Heap Item) : Pattern :=
  call "BNFDiscoveryHeapMergeAfterCompareV1" [order comparison, heap left, heap right]

theorem after_answers (base : BasePremiseEvaluator) (fuel : Nat) (comparison : Ordering)
    (left right : Item) (lc ls rc rs : Heap Item) :
    rewriteAt base language (fuel + 1)
      (afterCall comparison (.node left lc ls) (.node right rc rs)) =
      [result (heap ((Heap.node left lc ls).merge
        (fun _ _ => comparison.isLE) (.node right rc rs)))] := by
  rw [heap_rewriteAt base fuel _ (by
    simp [afterCall, call, encode, encodeList, headedBy, heapNames])]
  cases comparison <;>
    simp [rules_exact, observedRules, observed, PlainBnfTrieSourceExecution.observedRule,
      applyRuleUsing, afterCall, call, result, heap, order, Heap.merge,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

theorem rank_compare_answers (env : RelationEnv) (fuel : Nat) (left right : Rank) :
    rewriteAt (engineBasePremises env) language fuel (compareCall left right) =
      if compareHeight left right < fuel then
        [result (order (compareRank left right))] else [] := by
  rw [rank_conservative_extension env fuel _ (by
    simp [compareCall, call, encode, encodeList, headedBy, rankNames])]
  exact PlainBnfRankSourceExecution.compare_answers _ fuel left right

private theorem merge_nil (base : BasePremiseEvaluator) (fuel : Nat) :
    rewriteAt base language (fuel + 1) (mergeCall .nil .nil) = [result (heap .nil)] := by
  rw [heap_rewriteAt base fuel _ (by
    simp [mergeCall, call, encode, encodeList, headedBy, heapNames])]
  simp [rules_exact, observedRules, observed, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, mergeCall, call, result, heap,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem merge_left_nil (base : BasePremiseEvaluator) (fuel : Nat)
    (item : Item) (children siblings : Heap Item) :
    rewriteAt base language (fuel + 1) (mergeCall .nil (.node item children siblings)) =
      [result (heap (.node item children .nil))] := by
  rw [heap_rewriteAt base fuel _ (by
    simp [mergeCall, call, encode, encodeList, headedBy, heapNames])]
  simp [rules_exact, observedRules, observed, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, mergeCall, call, result, heap,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem merge_right_nil (base : BasePremiseEvaluator) (fuel : Nat)
    (item : Item) (children siblings : Heap Item) :
    rewriteAt base language (fuel + 1) (mergeCall (.node item children siblings) .nil) =
      [result (heap (.node item children .nil))] := by
  rw [heap_rewriteAt base fuel _ (by
    simp [mergeCall, call, encode, encodeList, headedBy, heapNames])]
  simp [rules_exact, observedRules, observed, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, mergeCall, call, result, heap,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private def nodeRule : RewriteRule := heapRules[3]'(by rw [rules_exact]; decide)

private theorem nodeRule_exact : nodeRule = observedRules[3]'(by decide) := rfl

private def nodeBindings (left right : Item) (lc ls rc rs : Heap Item) : Bindings :=
  [("?lc", encode (heap lc)), ("?lrest", encode (heap ls)),
   ("?lr", encode (rank left.1)), ("?le", encode left.2.expression),
   ("?ls", encode left.2.span), ("?ln", encode left.2.name),
   ("?rn", encode right.2.name), ("?rs", encode right.2.span),
   ("?re", encode right.2.expression), ("?rr", encode (rank right.1)),
   ("?rrest", encode (heap rs)), ("?rc", encode (heap rc))]

private theorem node_match (left right : Item) (lc ls rc rs : Heap Item) :
    matchPattern nodeRule.left (mergeCall (.node left lc ls) (.node right rc rs)) =
      [nodeBindings left right lc ls rc rs] := by
  simp [nodeRule_exact, observedRules, observed, PlainBnfTrieSourceExecution.observedRule,
    mergeCall, call, heap, rankedDefinition, nodeBindings,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem node_only (base : BasePremiseEvaluator) (fuel : Nat)
    (left right : Item) (lc ls rc rs : Heap Item) :
    rewriteAt base language (fuel + 1)
      (mergeCall (.node left lc ls) (.node right rc rs)) =
      applyRuleUsing base language (rewriteAt base language fuel) nodeRule
        (mergeCall (.node left lc ls) (.node right rc rs)) := by
  rw [heap_rewriteAt base fuel _ (by
    simp [mergeCall, call, encode, encodeList, headedBy, heapNames])]
  rw [rules_exact, nodeRule_exact]
  simp only [observedRules, List.flatMap_cons, List.flatMap_nil]
  simp [observed, PlainBnfTrieSourceExecution.observedRule, applyRuleUsing,
    mergeCall, call, heap, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem merge_nodes_none (base : BasePremiseEvaluator) (fuel : Nat)
    (left right : Item) (lc ls rc rs : Heap Item)
    (comparison : rewriteAt base language fuel (compareCall left.1 right.1) = []) :
    rewriteAt base language (fuel + 1)
      (mergeCall (.node left lc ls) (.node right rc rs)) = [] := by
  rw [node_only, applyRuleUsing, matchPatternForRule_eq_syntactic, node_match]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [nodeRule_exact, observedRules, observed, PlainBnfTrieSourceExecution.observedRule,
    nodeBindings, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode,
    mergeBindings, premisesUsing,
    premiseStepUsing, applyBindings]
  simp only [compareCall, call, encode, encodeList] at comparison
  rw [comparison]
  simp

private theorem merge_nodes_some (base : BasePremiseEvaluator) (fuel : Nat)
    (left right : Item) (lc ls rc rs : Heap Item) (comparison : Ordering)
    (compared : rewriteAt base language (fuel + 1) (compareCall left.1 right.1) =
      [result (order comparison)]) :
    rewriteAt base language (fuel + 2)
      (mergeCall (.node left lc ls) (.node right rc rs)) =
      [result (heap ((Heap.node left lc ls).merge
        (fun _ _ => comparison.isLE) (.node right rc rs)))] := by
  rw [node_only, applyRuleUsing, matchPatternForRule_eq_syntactic, node_match]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [nodeRule_exact, observedRules, observed, PlainBnfTrieSourceExecution.observedRule,
    nodeBindings, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode,
    mergeBindings, premisesUsing, applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    premiseStepUsing, applyBindings]
  simp only [compareCall, call, result, encode, encodeList] at compared
  rw [compared]
  simp [order, matchPattern, matchArgs, mergeBindings, List.foldlM]
  have after := after_answers base fuel comparison left right lc ls rc rs
  simp only [afterCall, call, heap, rankedDefinition, order, encode, encodeList] at after
  rw [after]
  simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

/-- Required contextual-rule depth; this does not compute a merge result. -/
def mergeHeight : Heap Item → Heap Item → Nat
  | .node left _ _, .node right _ _ => compareHeight left.1 right.1 + 1
  | _, _ => 0

theorem merge_answers (env : RelationEnv) (fuel : Nat) (left right : Heap Item) :
    rewriteAt (engineBasePremises env) language fuel (mergeCall left right) =
      if mergeHeight left right < fuel then
        [result (heap (left.merge itemLE right))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
      cases left with
      | nil =>
          cases right with
          | nil => simpa [mergeHeight, Heap.merge] using merge_nil (engineBasePremises env) fuel
          | node item children siblings =>
              simpa [mergeHeight, Heap.merge] using merge_left_nil (engineBasePremises env) fuel
                item children siblings
      | node left lc ls =>
          cases right with
          | nil =>
              simpa [mergeHeight, Heap.merge] using merge_right_nil (engineBasePremises env) fuel
                left lc ls
          | node right rc rs =>
              by_cases enough : compareHeight left.1 right.1 < fuel
              · have compared := rank_compare_answers env fuel left.1 right.1
                simp only [enough, ↓reduceIte] at compared
                cases fuel with
                | zero => simp at enough
                | succ fuel =>
                    have step := merge_nodes_some (engineBasePremises env) fuel left right lc ls rc rs
                      (compareRank left.1 right.1) compared
                    have merge_eq : (Heap.node left lc ls).merge
                        (fun _ _ => (compareRank left.1 right.1).isLE) (.node right rc rs) =
                        (Heap.node left lc ls).merge itemLE (.node right rc rs) := by
                      simp only [Heap.merge, itemLE, rankLE]
                      rfl
                    rw [merge_eq] at step
                    simpa only [mergeHeight, Nat.add_lt_add_iff_right, enough, ↓reduceIte] using step
              · have compared := rank_compare_answers env fuel left.1 right.1
                simp only [enough, ↓reduceIte] at compared
                have step := merge_nodes_none (engineBasePremises env) fuel left right lc ls rc rs compared
                simpa [mergeHeight, enough] using step

theorem merge_step_iff (env : RelationEnv) (left right : Heap Item) (target : Pattern) :
    Step (engineBasePremises env) language (mergeCall left right) target ↔
      target = result (heap (left.merge itemLE right)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [merge_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨mergeHeight left right + 1, by simp [merge_answers]⟩

theorem ranked_definition_agrees_with_enumeration (item : Item) :
    rankedDefinition item = PlainBnfEnumerationSourceExecution.rankedDefinition item := rfl

theorem ranked_definition_injective : Function.Injective rankedDefinition :=
  PlainBnfEnumerationSourceExecution.rankedDefinition_injective

theorem heap_injective : Function.Injective heap := by
  intro left
  induction left with
  | nil =>
      intro right same
      cases right with
      | nil => rfl
      | node => simp [heap] at same
  | node item children siblings ihc ihs =>
      intro right same
      cases right with
      | nil => simp [heap] at same
      | node other otherChildren otherSiblings =>
          have parts : rankedDefinition item = rankedDefinition other ∧
              heap children = heap otherChildren ∧ heap siblings = heap otherSiblings := by
            simpa only [heap, SExpr.list.injEq, List.cons.injEq, true_and, and_true] using same
          rw [ranked_definition_injective parts.1, ihc parts.2.1, ihs parts.2.2]

theorem result_heap_injective : Function.Injective (fun input => result (heap input)) := by
  intro left right same
  apply heap_injective
  have encoded := SourceSExprPatternCodec.encode_injective same
  simpa only [SExpr.list.injEq, List.cons.injEq, and_true] using encoded

theorem merge_decoded_step_iff (env : RelationEnv) (left right output : Heap Item) :
    Step (engineBasePremises env) language (mergeCall left right) (result (heap output)) ↔
      output = left.merge itemLE right := by
  rw [merge_step_iff, result_heap_injective.eq_iff]

theorem merge_source_contents (env : RelationEnv) (left right output : Heap Item)
    (singleLeft : left.NoSibling) (singleRight : right.NoSibling)
    (returned : Step (engineBasePremises env) language (mergeCall left right) (result (heap output))) :
    PlainBnfPairingHeapObservation.contents output =
      PlainBnfPairingHeapObservation.contents left + PlainBnfPairingHeapObservation.contents right := by
  rw [(merge_decoded_step_iff env left right output).mp returned]
  exact PlainBnfPairingHeapObservation.contents_merge itemLE singleLeft singleRight

theorem merge_source_no_sibling (env : RelationEnv) (left right output : Heap Item)
    (returned : Step (engineBasePremises env) language (mergeCall left right) (result (heap output))) :
    output.NoSibling := by
  rw [(merge_decoded_step_iff env left right output).mp returned]
  exact Heap.noSibling_merge itemLE left right

instance : Batteries.TotalBLE itemLE where
  total {left right} :=
    Batteries.TotalBLE.total (le := rankLE) (a := left.1) (b := right.1)

theorem merge_source_WF (env : RelationEnv) (left right output : Heap Item)
    (leftOrdered : left.WF itemLE) (rightOrdered : right.WF itemLE)
    (returned : Step (engineBasePremises env) language (mergeCall left right) (result (heap output))) :
    output.WF itemLE := by
  rw [(merge_decoded_step_iff env left right output).mp returned]
  exact Heap.WF.merge leftOrdered rightOrdered

theorem duplicate_payload_occurrences_preserved (env : RelationEnv) (item : Item) :
    let input := Heap.node item Heap.nil Heap.nil
    ∃ output, Step (engineBasePremises env) language (mergeCall input input) (result (heap output)) ∧
      PlainBnfPairingHeapObservation.contents output = item ::ₘ item ::ₘ 0 ∧
      PlainBnfPairingHeapObservation.contents output ≠ item ::ₘ 0 := by
  dsimp
  refine ⟨(Heap.node item .nil .nil).merge itemLE (.node item .nil .nil),
    (merge_decoded_step_iff _ _ _ _).mpr rfl, ?_, ?_⟩
  all_goals
    rw [PlainBnfPairingHeapObservation.contents_merge itemLE (.node _ _) (.node _ _)]
    simp [PlainBnfPairingHeapObservation.contents]
  intro same
  have sizes := congrArg Multiset.card same
  simp at sizes

theorem equal_ranks_retain_distinct_payloads (env : RelationEnv) (position : Rank)
    (left right : Definition) :
    ∃ output, Step (engineBasePremises env) language
        (mergeCall (.node (position, left) .nil .nil) (.node (position, right) .nil .nil))
        (result (heap output)) ∧
      PlainBnfPairingHeapObservation.contents output = (position, left) ::ₘ (position, right) ::ₘ 0 := by
  refine ⟨(Heap.node (position, left) .nil .nil).merge itemLE (.node (position, right) .nil .nil),
    (merge_decoded_step_iff _ _ _ _).mpr rfl, ?_⟩
  rw [PlainBnfPairingHeapObservation.contents_merge itemLE (.node _ _) (.node _ _)]
  simp [PlainBnfPairingHeapObservation.contents]

/-- Raw merge intentionally drops root siblings. This is why the preceding
whole-content theorem has a NoSibling premise; no source occurrence is hidden. -/
theorem forest_sibling_drop_is_observable (env : RelationEnv) (first second : Item) :
    let forest := Heap.node first Heap.nil (Heap.node second Heap.nil Heap.nil)
    let output := Heap.node first Heap.nil Heap.nil
    Step (engineBasePremises env) language (mergeCall forest Heap.nil) (result (heap output)) ∧
      PlainBnfPairingHeapObservation.contents output ≠ PlainBnfPairingHeapObservation.contents forest := by
  dsimp
  constructor
  · rw [merge_step_iff]
    rfl
  · intro same
    have sizes := congrArg Multiset.card same
    simp [PlainBnfPairingHeapObservation.contents] at sizes

theorem insufficient_depth_has_no_merge_answer (env : RelationEnv) (left right : Heap Item)
    (fuel : Nat) (short : fuel ≤ mergeHeight left right) :
    rewriteAt (engineBasePremises env) language fuel (mergeCall left right) = [] := by
  simp [merge_answers, Nat.not_lt.mpr short]

theorem omitted_output_refused :
    splitCall? (.list [.atom "BNFDiscoveryHeapMergeV1", heap .nil, heap .nil]) = none := rfl

theorem combine_not_silently_admitted :
    splitCall? (.list [.atom "BNFDiscoveryHeapCombineV1", heap .nil, heap .nil]) = none := rfl

#print axioms merge_answers
#print axioms merge_step_iff
#print axioms merge_source_contents
#print axioms merge_source_WF
#print axioms forest_sibling_drop_is_observable

end Mettapedia.GSLT.Parsing.PlainBnfHeapSourceExecution
