import Mettapedia.GSLT.Parsing.PlainBnfHeapSourceExecution

/-!
# Authored discovery scheduling

Seven original scheduling rules compose the existing authored rank, heap
merge and sparse-trie insertion languages. The independent observation keeps
both actual heap partitions and the persistent first-binding trie. This is a
selected source/contextual execution connection, not a generated runtime,
whole discovery-loop correctness theorem, or alternative queue implementation.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfScheduleSourceExecution

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
open PlainBnfSourceRank (Rank compareRank)
open PlainBnfRankSourceExecution (rank order call result compareCall compareHeight)
open PlainBnfHeapSourceExecution (Item heap rankedDefinition itemLE mergeCall mergeHeight)
open PlainBnfGraphNameTrie (Trie insertFirst)
open PlainBnfCollectorSourceExecution (NameScalarCodec name)
open PlainBnfTrieSourceExecution (trie scalarRelations insertCall insertHeight)
open PlainBnfIndexedCollectorSourceExecution
  (headedBy premiseClosed closed_extension disjoint_heads_do_not_match trieNames)
open Batteries.PairingHeapImp (Heap)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def mode? (relation : String) : Option (Nat × Nat) :=
  match relation with
  | "BNFDiscoveryScheduleV1" | "BNFDiscoveryScheduleAtV1" => some (3, 1)
  | "BNFDiscoveryScheduleCurrentV1" | "BNFDiscoveryScheduleNextV1" => some (2, 1)
  | _ => (PlainBnfHeapSourceExecution.mode? relation).orElse
      (fun _ => PlainBnfCollectorSourceExecution.mode? relation)

def splitCall? : SExpr → Option (SExpr × SExpr)
  | .list (.atom relation :: arguments) => do
      let (inputs, outputs) ← mode? relation
      if arguments.length = inputs + outputs then
        some (.list (.atom relation :: arguments.take inputs), .list (arguments.drop inputs))
      else none
  | _ => none

def lowerPremise? : SExpr → Option Premise
  | .list [.atom "different", left, right] =>
      some (.relationQuery "different" [pattern left, pattern right])
  | source => do
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
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 60).take 7

def rules? : Option (List RewriteRule) := rows.mapM lowerRule?

theorem rules_present : rules?.isSome = true := rfl

def scheduleRules : List RewriteRule := rules?.get rules_present

def language : LanguageDef :=
  { name := "PlainBnfAuthoredScheduling", types := [], terms := [], equations := [],
    rewrites := PlainBnfHeapSourceExecution.language.rewrites ++
      PlainBnfTrieSourceExecution.language.rewrites ++ scheduleRules }

theorem translation_exact : rows.mapM lowerRule? = some scheduleRules := rfl

theorem source_occurrences_exact : rows.zipIdx 60 =
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 60).take 7 := rfl

theorem source_family_translation_exact :
    (PlainBnfRankSourceExecution.rows ++ PlainBnfHeapSourceExecution.rows ++
      PlainBnfCollectorSourceAdmission.indexSource.rewrites.take 14 ++ rows).mapM lowerRule? =
        some language.rewrites := by
  have hr : PlainBnfRankSourceExecution.rows.mapM lowerRule? =
      some PlainBnfRankSourceExecution.language.rewrites := rfl
  have hm : PlainBnfHeapSourceExecution.rows.mapM lowerRule? =
      some PlainBnfHeapSourceExecution.heapRules := rfl
  have ht : (PlainBnfCollectorSourceAdmission.indexSource.rewrites.take 14).mapM lowerRule? =
      some PlainBnfTrieSourceExecution.language.rewrites := rfl
  simp only [List.mapM_append, hr, hm, ht, translation_exact]
  rfl

theorem source_rule_count : language.rewrites.length = 43 := rfl

private def observed (name : String) (input output : SExpr)
    (premises : List Premise) : RewriteRule :=
  PlainBnfTrieSourceExecution.observedRule name input output premises

/-- Displayed source observations, checked against the executed translation. -/
private def observedRules : List RewriteRule := [
  observed "bnf-discovery-schedule-initial-v1"
    (metta_sexpr% petta "(BNFDiscoveryScheduleV1 ?node BNFDiscoveryInitialV1 ?before)")
    (metta_sexpr% petta "(?after)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryScheduleCurrentV1 ?node ?before)"))
      (pattern (metta_sexpr% petta "(?after)"))],
  observed "bnf-discovery-schedule-after-position-v1"
    (metta_sexpr% petta "(BNFDiscoveryScheduleV1 (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) (BNFDiscoveryAfterPositionV1 ?origin) ?before)")
    (metta_sexpr% petta "(?after)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryRankCompareV1 ?rank ?origin)"))
        (pattern (metta_sexpr% petta "(?order)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryScheduleAtV1 ?order (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) ?before)"))
        (pattern (metta_sexpr% petta "(?after)"))],
  observed "bnf-discovery-schedule-later-v1"
    (metta_sexpr% petta "(BNFDiscoveryScheduleAtV1 BNFDiscoveryGreaterV1 ?node ?before)")
    (metta_sexpr% petta "(?after)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryScheduleCurrentV1 ?node ?before)"))
      (pattern (metta_sexpr% petta "(?after)"))],
  observed "bnf-discovery-schedule-earlier-v1"
    (metta_sexpr% petta "(BNFDiscoveryScheduleAtV1 BNFDiscoveryLessV1 ?node ?before)")
    (metta_sexpr% petta "(?after)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryScheduleNextV1 ?node ?before)"))
      (pattern (metta_sexpr% petta "(?after)"))],
  observed "bnf-discovery-schedule-equal-v1"
    (metta_sexpr% petta "(BNFDiscoveryScheduleAtV1 BNFDiscoveryEqualV1 ?node ?before)")
    (metta_sexpr% petta "(?after)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryScheduleNextV1 ?node ?before)"))
      (pattern (metta_sexpr% petta "(?after)"))],
  observed "bnf-discovery-schedule-current-v1"
    (metta_sexpr% petta "(BNFDiscoveryScheduleCurrentV1 (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) (BNFDiscoveryQueuesV1 ?current ?following ?scheduled))")
    (metta_sexpr% petta "((BNFDiscoveryQueuesV1 ?nextCurrent ?following ?nextScheduled))")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryHeapMergeV1 (BNFDiscoveryHeapV1 (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) BNFDiscoveryHeapNilV1 BNFDiscoveryHeapNilV1) ?current)"))
        (pattern (metta_sexpr% petta "(?nextCurrent)")),
     .congruence (pattern (metta_sexpr% petta "(BNFGraphTrieInsertFirstV1 ?name ?name ?scheduled)"))
        (pattern (metta_sexpr% petta "(?nextScheduled)"))],
  observed "bnf-discovery-schedule-next-v1"
    (metta_sexpr% petta "(BNFDiscoveryScheduleNextV1 (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) (BNFDiscoveryQueuesV1 ?current ?following ?scheduled))")
    (metta_sexpr% petta "((BNFDiscoveryQueuesV1 ?current ?nextFollowing ?nextScheduled))")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryHeapMergeV1 (BNFDiscoveryHeapV1 (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) BNFDiscoveryHeapNilV1 BNFDiscoveryHeapNilV1) ?following)"))
        (pattern (metta_sexpr% petta "(?nextFollowing)")),
     .congruence (pattern (metta_sexpr% petta "(BNFGraphTrieInsertFirstV1 ?name ?name ?scheduled)"))
        (pattern (metta_sexpr% petta "(?nextScheduled)"))]]

private theorem rules_exact : scheduleRules = observedRules := rfl

def heapNames := PlainBnfHeapSourceExecution.rankNames ++ PlainBnfHeapSourceExecution.heapNames
def scheduleNames := ["BNFDiscoveryScheduleV1", "BNFDiscoveryScheduleAtV1",
  "BNFDiscoveryScheduleCurrentV1", "BNFDiscoveryScheduleNextV1"]

private theorem heap_closed : PlainBnfHeapSourceExecution.language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed heapNames)) = true := by
  simp [PlainBnfHeapSourceExecution.language_rewrites,
    PlainBnfRankSourceExecution.rules_exact, PlainBnfRankSourceExecution.observedRules,
    PlainBnfRankSourceExecution.observed, PlainBnfHeapSourceExecution.rules_exact,
    PlainBnfHeapSourceExecution.observedRules, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.observedRule, premiseClosed, headedBy, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, heapNames,
    PlainBnfHeapSourceExecution.rankNames, PlainBnfHeapSourceExecution.heapNames, encode]

private theorem heap_heads : PlainBnfHeapSourceExecution.language.rewrites.all
    (fun rule => headedBy heapNames rule.left) = true := by
  simp [PlainBnfHeapSourceExecution.language_rewrites,
    PlainBnfRankSourceExecution.rules_exact, PlainBnfRankSourceExecution.observedRules,
    PlainBnfRankSourceExecution.observed, PlainBnfHeapSourceExecution.rules_exact,
    PlainBnfHeapSourceExecution.observedRules, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.observedRule, headedBy, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, heapNames,
    PlainBnfHeapSourceExecution.rankNames, PlainBnfHeapSourceExecution.heapNames, encode]

private theorem trie_heads : PlainBnfTrieSourceExecution.language.rewrites.all
    (fun rule => headedBy trieNames rule.left) = true := by
  simp [PlainBnfTrieSourceExecution.source_rules_exact, PlainBnfTrieSourceExecution.observedRules,
    PlainBnfTrieSourceExecution.observedRule, headedBy, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, trieNames, encode]

theorem schedule_heads : scheduleRules.all (fun rule => headedBy scheduleNames rule.left) = true := by
  simp [rules_exact, observedRules, observed, PlainBnfTrieSourceExecution.observedRule,
    headedBy, pattern, patternList, SourceIntegerProvider.sourceVariableToken, scheduleNames, encode]

def relationHeads := heapNames ++ trieNames ++ scheduleNames

theorem family_heads : language.rewrites.all (fun rule => headedBy relationHeads rule.left) = true := by
  simp [language, PlainBnfHeapSourceExecution.language_rewrites,
    PlainBnfRankSourceExecution.rules_exact, PlainBnfRankSourceExecution.observedRules,
    PlainBnfRankSourceExecution.observed, PlainBnfHeapSourceExecution.rules_exact,
    PlainBnfHeapSourceExecution.observedRules, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.source_rules_exact, PlainBnfTrieSourceExecution.observedRules,
    PlainBnfTrieSourceExecution.observedRule, rules_exact, observedRules, observed,
    headedBy, relationHeads, heapNames, trieNames, scheduleNames,
    PlainBnfHeapSourceExecution.rankNames, PlainBnfHeapSourceExecution.heapNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem family_closed : language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed relationHeads)) = true := by
  simp [language, PlainBnfHeapSourceExecution.language_rewrites,
    PlainBnfRankSourceExecution.rules_exact, PlainBnfRankSourceExecution.observedRules,
    PlainBnfRankSourceExecution.observed, PlainBnfHeapSourceExecution.rules_exact,
    PlainBnfHeapSourceExecution.observedRules, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.source_rules_exact, PlainBnfTrieSourceExecution.observedRules,
    PlainBnfTrieSourceExecution.observedRule, rules_exact, observedRules, observed,
    premiseClosed, headedBy, relationHeads, heapNames, trieNames, scheduleNames,
    PlainBnfHeapSourceExecution.rankNames, PlainBnfHeapSourceExecution.heapNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

private theorem heap_disjoint : List.Disjoint (trieNames ++ scheduleNames) heapNames := by
  simp [trieNames, scheduleNames, heapNames, PlainBnfHeapSourceExecution.rankNames,
    PlainBnfHeapSourceExecution.heapNames]

private theorem trie_disjoint : List.Disjoint (heapNames ++ scheduleNames) trieNames := by
  simp [trieNames, scheduleNames, heapNames, PlainBnfHeapSourceExecution.rankNames,
    PlainBnfHeapSourceExecution.heapNames]

theorem heap_conservative_extension (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy heapNames source = true) :
    rewriteAt (engineBasePremises env) language fuel source =
      rewriteAt (engineBasePremises env) PlainBnfHeapSourceExecution.language fuel source := by
  apply closed_extension heapNames env _ _ []
    (PlainBnfTrieSourceExecution.language.rewrites ++ scheduleRules)
  · simp [language, List.append_assoc]
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp heap_closed rule member) premise present
  · intro rule member term termHead
    simp only [List.nil_append, List.mem_append] at member
    rcases member with member | member
    · exact disjoint_heads_do_not_match trieNames heapNames
        (List.disjoint_append_left.mp heap_disjoint).1 _ _
        (List.all_eq_true.mp trie_heads rule member) termHead
    · exact disjoint_heads_do_not_match scheduleNames heapNames
        (List.disjoint_append_left.mp heap_disjoint).2 _ _
        (List.all_eq_true.mp schedule_heads rule member) termHead
  · exact headed

theorem trie_conservative_extension (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy trieNames source = true) :
    rewriteAt (engineBasePremises env) language fuel source =
      rewriteAt (engineBasePremises env) PlainBnfTrieSourceExecution.language fuel source := by
  apply closed_extension trieNames env _ _ PlainBnfHeapSourceExecution.language.rewrites scheduleRules
  · rfl
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp
      PlainBnfIndexedCollectorSourceExecution.trie_closed rule member) premise present
  · intro rule member term termHead
    rcases List.mem_append.mp member with member | member
    · exact disjoint_heads_do_not_match heapNames trieNames
        (List.disjoint_append_left.mp trie_disjoint).1 _ _
        (List.all_eq_true.mp heap_heads rule member) termHead
    · exact disjoint_heads_do_not_match scheduleNames trieNames
        (List.disjoint_append_left.mp trie_disjoint).2 _ _
        (List.all_eq_true.mp schedule_heads rule member) termHead
  · exact headed

private theorem schedule_rewriteAt (base : BasePremiseEvaluator) (fuel : Nat) (source : Pattern)
    (headed : headedBy scheduleNames source = true) :
    rewriteAt base language (fuel + 1) source =
      scheduleRules.flatMap (fun rule =>
        applyRuleUsing base language (rewriteAt base language fuel) rule source) := by
  apply PlainBnfHeapSourceExecution.skip_unmatched_prefix base language
    (PlainBnfHeapSourceExecution.language.rewrites ++ PlainBnfTrieSourceExecution.language.rewrites)
    scheduleRules rfl
  intro rule member
  rcases List.mem_append.mp member with member | member
  · exact disjoint_heads_do_not_match heapNames scheduleNames
      ((List.disjoint_append_left.mp heap_disjoint).2.symm) _ _
      (List.all_eq_true.mp heap_heads rule member) headed
  · exact disjoint_heads_do_not_match trieNames scheduleNames
      ((List.disjoint_append_left.mp trie_disjoint).2.symm) _ _
      (List.all_eq_true.mp trie_heads rule member) headed

theorem merge_answers (fuel : Nat) (left right : Heap Item) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (mergeCall left right) =
      if mergeHeight left right < fuel then [result (heap (left.merge itemLE right))] else [] := by
  rw [heap_conservative_extension _ fuel _ (by
    simp [mergeCall, call, encode, encodeList, headedBy, heapNames,
      PlainBnfHeapSourceExecution.rankNames, PlainBnfHeapSourceExecution.heapNames])]
  exact PlainBnfHeapSourceExecution.merge_answers _ fuel left right

theorem rank_answers (fuel : Nat) (left right : Rank) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (compareCall left right) =
      if compareHeight left right < fuel then [result (order (compareRank left right))] else [] := by
  rw [heap_conservative_extension _ fuel _ (by
    simp [compareCall, call, encode, encodeList, headedBy, heapNames,
      PlainBnfHeapSourceExecution.rankNames, PlainBnfHeapSourceExecution.heapNames])]
  exact PlainBnfHeapSourceExecution.rank_compare_answers _ fuel left right

variable {Scalar : Type} [NameScalarCodec Scalar] [DecidableEq Scalar]

theorem insert_answers (fuel : Nat) (key : List Scalar) (payload : SExpr) (scheduled : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (insertCall key payload scheduled) =
      if insertHeight key scheduled < fuel then
        [result (trie (insertFirst key payload scheduled))] else [] := by
  rw [trie_conservative_extension _ fuel _ (by
    simp [insertCall, PlainBnfTrieSourceExecution.call, encode, encodeList, headedBy, trieNames])]
  exact (PlainBnfTrieSourceExecution.insert_answers fuel).1 key payload scheduled

def node (priority : Rank) (key : List Scalar) (expression span : SExpr) : Item :=
  (priority, ⟨name key, expression, span⟩)

def queues (current following : Heap Item) (scheduled : Trie SExpr Scalar) : SExpr :=
  .list [.atom "BNFDiscoveryQueuesV1", heap current, heap following, trie scheduled]

def singleton (item : Item) : Heap Item := .node item .nil .nil

def sideSymbol (toCurrent : Bool) : String :=
  if toCurrent then "BNFDiscoveryScheduleCurrentV1" else "BNFDiscoveryScheduleNextV1"

def sideCall (toCurrent : Bool) (item : Item) (current following : Heap Item)
    (scheduled : Trie SExpr Scalar) : Pattern :=
  call (sideSymbol toCurrent) [rankedDefinition item, queues current following scheduled]

def updated (toCurrent : Bool) (priority : Rank) (key : List Scalar) (expression span : SExpr)
    (current following : Heap Item) (scheduled : Trie SExpr Scalar) : SExpr :=
  queues
    (if toCurrent then (singleton (node priority key expression span)).merge itemLE current else current)
    (if toCurrent then following else (singleton (node priority key expression span)).merge itemLE following)
    (insertFirst key (name key) scheduled)

/-- Contextual depth only; no scheduling result is supplied by this bound. -/
def sideHeight (toCurrent : Bool) (priority : Rank) (key : List Scalar) (expression span : SExpr)
    (current following : Heap Item) (scheduled : Trie SExpr Scalar) : Nat :=
  max (mergeHeight (singleton (node priority key expression span))
    (if toCurrent then current else following)) (insertHeight key scheduled) + 1

private theorem side_step (fuel : Nat) (toCurrent : Bool) (priority : Rank) (key : List Scalar)
    (expression span : SExpr) (current following : Heap Item) (scheduled : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (sideCall toCurrent (node priority key expression span) current following scheduled) =
      if mergeHeight (singleton (node priority key expression span))
          (if toCurrent then current else following) < fuel ∧ insertHeight key scheduled < fuel then
        [result (updated toCurrent priority key expression span current following scheduled)] else [] := by
  rw [schedule_rewriteAt _ fuel _ (by
    cases toCurrent <;> simp [sideCall, sideSymbol, call, headedBy, scheduleNames, encode, encodeList])]
  have merged := merge_answers fuel (singleton (node priority key expression span))
    (if toCurrent then current else following)
  have inserted := insert_answers fuel key (name key) scheduled
  cases toCurrent <;>
    simp [rules_exact, observedRules, observed, PlainBnfTrieSourceExecution.observedRule,
      applyRuleUsing, sideCall, sideSymbol, call, node, queues, rankedDefinition,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte, mergeCall, call, singleton, heap,
      node, rankedDefinition, encode, encodeList] at merged
    rw [merged]
    split
    · rename_i mergeEnough
      simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
      simp only [insertCall, PlainBnfTrieSourceExecution.call, result, encode, encodeList] at inserted
      rw [inserted]
      split
      · rename_i insertEnough
        simp [matchPattern, matchArgs, mergeBindings, List.foldlM, updated,
          queues, node, singleton, encode, encodeList, mergeEnough, insertEnough]
      · rename_i insertShort
        simp [insertShort]
    · rename_i mergeShort
      simp [singleton, mergeShort]

theorem side_answers (fuel : Nat) (toCurrent : Bool) (priority : Rank) (key : List Scalar)
    (expression span : SExpr) (current following : Heap Item) (scheduled : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (sideCall toCurrent (node priority key expression span) current following scheduled) =
      if sideHeight toCurrent priority key expression span current following scheduled < fuel then
        [result (updated toCurrent priority key expression span current following scheduled)] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
      rw [side_step]
      simp [sideHeight]

def atCall (comparison : Ordering) (item : Item) (current following : Heap Item)
    (scheduled : Trie SExpr Scalar) : Pattern :=
  call "BNFDiscoveryScheduleAtV1" [order comparison, rankedDefinition item, queues current following scheduled]

def atHeight (comparison : Ordering) (priority : Rank) (key : List Scalar) (expression span : SExpr)
    (current following : Heap Item) (scheduled : Trie SExpr Scalar) : Nat :=
  sideHeight comparison.isGT priority key expression span current following scheduled + 1

private theorem at_step (fuel : Nat) (comparison : Ordering) (priority : Rank) (key : List Scalar)
    (expression span : SExpr) (current following : Heap Item) (scheduled : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (atCall comparison (node priority key expression span) current following scheduled) =
      if sideHeight comparison.isGT priority key expression span current following scheduled < fuel then
        [result (updated comparison.isGT priority key expression span current following scheduled)] else [] := by
  rw [schedule_rewriteAt _ fuel _ (by
    simp [atCall, call, encode, encodeList, headedBy, scheduleNames])]
  have recursive := side_answers fuel comparison.isGT priority key expression span current following scheduled
  cases comparison <;>
    simp [rules_exact, observedRules, observed, PlainBnfTrieSourceExecution.observedRule,
      applyRuleUsing, atCall, call, order, Ordering.isGT,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  all_goals
    simp [Ordering.isGT, sideCall, sideSymbol, call, encode, encodeList] at recursive
    rw [recursive]
    split_ifs with enough <;>
      simp [enough, result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem at_answers (fuel : Nat) (comparison : Ordering) (priority : Rank) (key : List Scalar)
    (expression span : SExpr) (current following : Heap Item) (scheduled : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (atCall comparison (node priority key expression span) current following scheduled) =
      if atHeight comparison priority key expression span current following scheduled < fuel then
        [result (updated comparison.isGT priority key expression span current following scheduled)] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel => simpa [atHeight] using at_step fuel comparison priority key expression span current following scheduled

def position : Option Rank → SExpr
  | none => .atom "BNFDiscoveryInitialV1"
  | some origin => .list [.atom "BNFDiscoveryAfterPositionV1", rank origin]

def scheduleCall (origin : Option Rank) (item : Item) (current following : Heap Item)
    (scheduled : Trie SExpr Scalar) : Pattern :=
  call "BNFDiscoveryScheduleV1" [rankedDefinition item, position origin, queues current following scheduled]

def toCurrent (priority : Rank) : Option Rank → Bool
  | none => true
  | some origin => (compareRank priority origin).isGT

def scheduleHeight (priority : Rank) (key : List Scalar) (expression span : SExpr)
    (current following : Heap Item) (scheduled : Trie SExpr Scalar) : Option Rank → Nat
  | none => sideHeight true priority key expression span current following scheduled + 1
  | some origin => max (compareHeight priority origin)
      (atHeight (compareRank priority origin) priority key expression span current following scheduled) + 1

private theorem initial_step (fuel : Nat) (priority : Rank) (key : List Scalar)
    (expression span : SExpr) (current following : Heap Item) (scheduled : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (scheduleCall none (node priority key expression span) current following scheduled) =
      if sideHeight true priority key expression span current following scheduled < fuel then
        [result (updated true priority key expression span current following scheduled)] else [] := by
  rw [schedule_rewriteAt _ fuel _ (by
    simp [scheduleCall, call, encode, encodeList, headedBy, scheduleNames])]
  have recursive := side_answers fuel true priority key expression span current following scheduled
  simp [rules_exact, observedRules, observed, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, scheduleCall, position, call, node, rankedDefinition,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [sideCall, sideSymbol, ↓reduceIte, call, node, rankedDefinition, encode, encodeList] at recursive
  rw [recursive]
  split <;> simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem after_step (fuel : Nat) (origin priority : Rank) (key : List Scalar)
    (expression span : SExpr) (current following : Heap Item) (scheduled : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (scheduleCall (some origin) (node priority key expression span) current following scheduled) =
      if compareHeight priority origin < fuel ∧
          atHeight (compareRank priority origin) priority key expression span current following scheduled < fuel then
        [result (updated (compareRank priority origin).isGT priority key expression span current following scheduled)]
      else [] := by
  rw [schedule_rewriteAt _ fuel _ (by
    simp [scheduleCall, call, encode, encodeList, headedBy, scheduleNames])]
  have compared := rank_answers fuel priority origin
  have followingDone := at_answers fuel (compareRank priority origin) priority key expression span
    current following scheduled
  simp [rules_exact, observedRules, observed, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, scheduleCall, position, call, node, rankedDefinition,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [compareCall, call, result, encode, encodeList] at compared
  rw [compared]
  split
  · rename_i compareEnough
    simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
    simp only [atCall, call, node, rankedDefinition, encode, encodeList] at followingDone
    rw [followingDone]
    split <;>
      simp_all [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
  · rename_i compareShort
    simp [compareShort]

/-- Exact bounded ordered answers. A short contextual search returns no
derived answer at that bound; it is not a semantic refutation. -/
theorem schedule_answers (fuel : Nat) (origin : Option Rank) (priority : Rank) (key : List Scalar)
    (expression span : SExpr) (current following : Heap Item) (scheduled : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (scheduleCall origin (node priority key expression span) current following scheduled) =
      if scheduleHeight priority key expression span current following scheduled origin < fuel then
        [result (updated (toCurrent priority origin) priority key expression span current following scheduled)]
      else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
      cases origin with
      | none =>
          simpa [scheduleHeight, toCurrent] using
            (initial_step fuel priority key expression span current following scheduled)
      | some cursor =>
          simpa [scheduleHeight, toCurrent] using
            (after_step fuel cursor priority key expression span current following scheduled)

theorem schedule_step_iff (origin : Option Rank) (priority : Rank) (key : List Scalar)
    (expression span : SExpr) (current following : Heap Item) (scheduled : Trie SExpr Scalar)
    (target : Pattern) :
    Step (engineBasePremises scalarRelations) language
      (scheduleCall origin (node priority key expression span) current following scheduled) target ↔
        target = result (updated (toCurrent priority origin) priority key expression span current following scheduled) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [schedule_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨scheduleHeight priority key expression span current following scheduled origin + 1,
      by simp [schedule_answers]⟩

omit [DecidableEq Scalar] in
theorem queues_eq_iff (current following current' following' : Heap Item)
    (scheduled scheduled' : Trie SExpr Scalar) :
    queues current following scheduled = queues current' following' scheduled' ↔
      current = current' ∧ following = following' ∧ scheduled = scheduled' := by
  constructor
  · intro same
    have parts : heap current = heap current' ∧ heap following = heap following' ∧
        trie scheduled = trie scheduled' := by
      simpa only [queues, SExpr.list.injEq, List.cons.injEq, true_and, and_true] using same
    exact ⟨PlainBnfHeapSourceExecution.heap_injective parts.1,
      PlainBnfHeapSourceExecution.heap_injective parts.2.1,
      PlainBnfTrieSourceExecution.trie_injective parts.2.2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- The exact source transition, decoded into the two original heaps and trie.
No freshness premise is imposed or inferred by these scheduling rules. -/
theorem schedule_decoded_step_iff (origin : Option Rank) (priority : Rank) (key : List Scalar)
    (expression span : SExpr) (current following current' following' : Heap Item)
    (scheduled scheduled' : Trie SExpr Scalar) :
    Step (engineBasePremises scalarRelations) language
      (scheduleCall origin (node priority key expression span) current following scheduled)
      (result (queues current' following' scheduled')) ↔
        current' = (if toCurrent priority origin then
          (singleton (node priority key expression span)).merge itemLE current else current) ∧
        following' = (if toCurrent priority origin then following else
          (singleton (node priority key expression span)).merge itemLE following) ∧
        scheduled' = insertFirst key (name key) scheduled := by
  have injective : Function.Injective result := by
    intro left right same
    exact (List.cons.inj (SExpr.list.inj (SourceSExprPatternCodec.encode_injective same))).1
  rw [schedule_step_iff, injective.eq_iff]
  exact queues_eq_iff _ _ _ _ _ _

theorem toCurrent_after_iff (priority origin : Rank) :
    toCurrent priority (some origin) = true ↔
      PlainBnfSourceRank.value origin < PlainBnfSourceRank.value priority := by
  change (compareRank priority origin).isGT = true ↔ _
  rw [← PlainBnfSourceRank.compareRank_gt_iff]
  cases compareRank priority origin <;> decide

theorem equal_rank_goes_to_following (priority : Rank) :
    toCurrent priority (some priority) = false := by
  have same := (PlainBnfSourceRank.compareRank_eq_iff priority priority).mpr rfl
  simp [toCurrent, same, Ordering.isGT]

theorem initial_goes_to_current (priority : Rank) : toCurrent priority none = true := rfl

theorem source_step_preserves_first_binding (origin : Option Rank) (priority : Rank)
    (key query : List Scalar) (expression span : SExpr)
    (current following current' following' : Heap Item) (scheduled scheduled' : Trie SExpr Scalar)
    (returned : Step (engineBasePremises scalarRelations) language
      (scheduleCall origin (node priority key expression span) current following scheduled)
      (result (queues current' following' scheduled'))) :
    PlainBnfGraphNameTrie.lookup query scheduled' =
      if query = key then (PlainBnfGraphNameTrie.lookup key scheduled).or (some (name key))
      else PlainBnfGraphNameTrie.lookup query scheduled := by
  rw [((schedule_decoded_step_iff origin priority key expression span current following
    current' following' scheduled scheduled').mp returned).2.2]
  exact PlainBnfGraphNameTrie.lookup_insertFirst key (name key) query scheduled

theorem source_step_keeps_existing_payload (origin : Option Rank) (priority : Rank)
    (key : List Scalar) (expression span payload : SExpr)
    (current following current' following' : Heap Item) (scheduled scheduled' : Trie SExpr Scalar)
    (old : PlainBnfGraphNameTrie.lookup key scheduled = some payload)
    (returned : Step (engineBasePremises scalarRelations) language
      (scheduleCall origin (node priority key expression span) current following scheduled)
      (result (queues current' following' scheduled'))) :
    PlainBnfGraphNameTrie.lookup key scheduled' = some payload := by
  rw [source_step_preserves_first_binding origin priority key key expression span
    current following current' following' scheduled scheduled' returned]
  simp [old]

/-- Equality of ranks is not the strictly-later case, even with nonempty heaps. -/
theorem source_equal_rank_iff (priority : Rank) (key : List Scalar) (expression span : SExpr)
    (current following current' following' : Heap Item) (scheduled scheduled' : Trie SExpr Scalar) :
    Step (engineBasePremises scalarRelations) language
      (scheduleCall (some priority) (node priority key expression span) current following scheduled)
      (result (queues current' following' scheduled')) ↔
        current' = current ∧
        following' = (singleton (node priority key expression span)).merge itemLE following ∧
        scheduled' = insertFirst key (name key) scheduled := by
  simp only [schedule_decoded_step_iff, equal_rank_goes_to_following, Bool.false_eq_true, ↓reduceIte]

theorem source_initial_iff (priority : Rank) (key : List Scalar) (expression span : SExpr)
    (current following current' following' : Heap Item) (scheduled scheduled' : Trie SExpr Scalar) :
    Step (engineBasePremises scalarRelations) language
      (scheduleCall none (node priority key expression span) current following scheduled)
      (result (queues current' following' scheduled')) ↔
        current' = (singleton (node priority key expression span)).merge itemLE current ∧
        following' = following ∧ scheduled' = insertFirst key (name key) scheduled := by
  simp only [schedule_decoded_step_iff, initial_goes_to_current, ↓reduceIte]

/-- An existing scheduled binding does not suppress this source call. The
caller must perform the wake check if it needs unique pending occurrences. -/
theorem existing_name_still_inserts (priority : Rank) (key : List Scalar)
    (expression span payload : SExpr) (scheduled : Trie SExpr Scalar)
    (old : PlainBnfGraphNameTrie.lookup key scheduled = some payload) :
    let item := node priority key expression span
    ∃ current' scheduled',
      Step (engineBasePremises scalarRelations) language
        (scheduleCall none item (singleton item) .nil scheduled)
        (result (queues current' .nil scheduled')) ∧
      PlainBnfPairingHeapObservation.contents current' = item ::ₘ item ::ₘ 0 ∧
      PlainBnfPairingHeapObservation.contents current' ≠ item ::ₘ 0 ∧
      PlainBnfGraphNameTrie.lookup key scheduled' = some payload := by
  dsimp
  let item := node priority key expression span
  refine ⟨(singleton item).merge itemLE (singleton item), insertFirst key (name key) scheduled,
    (source_initial_iff _ _ _ _ _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · simp only [singleton]
    rw [PlainBnfPairingHeapObservation.contents_merge itemLE (.node _ _) (.node _ _)]
    simp [PlainBnfPairingHeapObservation.contents, item]
  · simp only [singleton]
    rw [PlainBnfPairingHeapObservation.contents_merge itemLE (.node _ _) (.node _ _)]
    intro same
    have sizes := congrArg Multiset.card same
    simp [PlainBnfPairingHeapObservation.contents] at sizes
  · rw [PlainBnfGraphNameTrie.lookup_inserted, old]
    rfl

theorem equal_rank_not_strictly_later (priority : Rank) :
    ¬ toCurrent priority (some priority) = true := by
  simp [equal_rank_goes_to_following]

end Mettapedia.GSLT.Parsing.PlainBnfScheduleSourceExecution
