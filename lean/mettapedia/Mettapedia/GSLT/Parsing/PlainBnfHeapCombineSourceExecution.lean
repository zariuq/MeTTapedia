import Mettapedia.GSLT.Parsing.PlainBnfHeapSourceExecution

/-!
# Authored discovery heap combine

The three original combine clauses execute beside their actual rank/merge
dependencies. The independent result is Batteries' existing pairing-heap
combine. Complete source answers preserve the whole forest, including every
sibling and opaque payload occurrence. No generated or native correspondence
is asserted here.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfHeapCombineSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList)
open PlainBnfRankSourceExecution (call result)
open PlainBnfHeapSourceExecution (Item heap rankedDefinition itemLE mergeCall mergeHeight)
open PlainBnfIndexedCollectorSourceExecution
  (headedBy premiseClosed closed_extension disjoint_heads_do_not_match)
open Batteries.PairingHeapImp (Heap)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def mode? (name : String) : Option (Nat × Nat) :=
  if name = "BNFDiscoveryHeapCombineV1" then some (1, 1)
  else PlainBnfHeapSourceExecution.mode? name

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
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 29).take 3

def rules? : Option (List RewriteRule) := rows.mapM lowerRule?

theorem rules_present : rules?.isSome = true := rfl

def combineRules : List RewriteRule := rules?.get rules_present

def language : LanguageDef :=
  { name := "PlainBnfAuthoredHeapCombine", types := [], terms := [], equations := [],
    rewrites := PlainBnfHeapSourceExecution.language.rewrites ++ combineRules }

theorem language_partition : language.rewrites =
    PlainBnfHeapSourceExecution.language.rewrites ++ combineRules := rfl

theorem translation_exact : rows.mapM lowerRule? = some combineRules := rfl

theorem source_occurrences_exact : rows.zipIdx 29 =
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 29).take 3 := rfl

theorem source_family_translation_exact :
    (PlainBnfRankSourceExecution.rows ++ PlainBnfHeapSourceExecution.rows ++ rows).mapM lowerRule? =
      some language.rewrites := rfl

theorem source_rule_count : language.rewrites.length = 25 := rfl

def observed (name : String) (input output : SExpr)
    (premises : List Premise := []) : RewriteRule :=
  PlainBnfHeapSourceExecution.observed name input output premises

/-- Checked observations only; executable rules come from admitted source rows. -/
def observedRules : List RewriteRule := [
  observed "bnf-discovery-heap-combine-nil-v1"
    (metta_sexpr% petta "(BNFDiscoveryHeapCombineV1 BNFDiscoveryHeapNilV1)")
    (metta_sexpr% petta "(BNFDiscoveryHeapNilV1)"),
  observed "bnf-discovery-heap-combine-one-v1"
    (metta_sexpr% petta "(BNFDiscoveryHeapCombineV1 (BNFDiscoveryHeapV1 ?node ?children BNFDiscoveryHeapNilV1))")
    (metta_sexpr% petta "((BNFDiscoveryHeapV1 ?node ?children BNFDiscoveryHeapNilV1))"),
  observed "bnf-discovery-heap-combine-pair-v1"
    (metta_sexpr% petta "(BNFDiscoveryHeapCombineV1 (BNFDiscoveryHeapV1 ?left ?lc (BNFDiscoveryHeapV1 ?right ?rc ?rest)))")
    (metta_sexpr% petta "(?result)")
    [.congruence
      (pattern (metta_sexpr% petta "(BNFDiscoveryHeapMergeV1 (BNFDiscoveryHeapV1 ?left ?lc BNFDiscoveryHeapNilV1) (BNFDiscoveryHeapV1 ?right ?rc BNFDiscoveryHeapNilV1))"))
      (pattern (metta_sexpr% petta "(?pair)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryHeapCombineV1 ?rest)"))
      (pattern (metta_sexpr% petta "(?following)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryHeapMergeV1 ?pair ?following)"))
      (pattern (metta_sexpr% petta "(?result)"))]]

theorem rules_exact : combineRules = observedRules := rfl

def dependencyNames : List String :=
  PlainBnfHeapSourceExecution.rankNames ++ PlainBnfHeapSourceExecution.heapNames

def combineNames : List String := ["BNFDiscoveryHeapCombineV1"]

theorem dependencies_closed : PlainBnfHeapSourceExecution.language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed dependencyNames)) = true := by
  simp [PlainBnfHeapSourceExecution.language_rewrites,
    PlainBnfRankSourceExecution.rules_exact, PlainBnfRankSourceExecution.observedRules,
    PlainBnfRankSourceExecution.observed, PlainBnfHeapSourceExecution.rules_exact,
    PlainBnfHeapSourceExecution.observedRules, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.observedRule, premiseClosed, headedBy, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, dependencyNames,
    PlainBnfHeapSourceExecution.rankNames, PlainBnfHeapSourceExecution.heapNames, encode]

theorem dependencies_heads : PlainBnfHeapSourceExecution.language.rewrites.all
    (fun rule => headedBy dependencyNames rule.left) = true := by
  simp [PlainBnfHeapSourceExecution.language_rewrites,
    PlainBnfRankSourceExecution.rules_exact, PlainBnfRankSourceExecution.observedRules,
    PlainBnfRankSourceExecution.observed, PlainBnfHeapSourceExecution.rules_exact,
    PlainBnfHeapSourceExecution.observedRules, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.observedRule, headedBy, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, dependencyNames,
    PlainBnfHeapSourceExecution.rankNames, PlainBnfHeapSourceExecution.heapNames, encode]

theorem combine_heads : combineRules.all (fun rule => headedBy combineNames rule.left) = true := by
  simp [rules_exact, observedRules, observed, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.observedRule, headedBy, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, combineNames, encode]

theorem names_disjoint : List.Disjoint combineNames dependencyNames := by
  simp [combineNames, dependencyNames, PlainBnfHeapSourceExecution.rankNames,
    PlainBnfHeapSourceExecution.heapNames]

theorem dependencies_conservative_extension (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy dependencyNames source = true) :
    rewriteAt (engineBasePremises env) language fuel source =
      rewriteAt (engineBasePremises env) PlainBnfHeapSourceExecution.language fuel source := by
  apply closed_extension dependencyNames env _ _ [] combineRules
  · simpa using language_partition
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp dependencies_closed rule member) premise present
  · intro rule member term termHead
    exact disjoint_heads_do_not_match combineNames dependencyNames names_disjoint _ _
      (List.all_eq_true.mp combine_heads rule (by simpa using member)) termHead
  · exact headed

theorem merge_answers (env : RelationEnv) (fuel : Nat) (left right : Heap Item) :
    rewriteAt (engineBasePremises env) language fuel (mergeCall left right) =
      if mergeHeight left right < fuel then [result (heap (left.merge itemLE right))] else [] := by
  rw [dependencies_conservative_extension env fuel _ (by
    simp [mergeCall, call, encode, encodeList, headedBy, dependencyNames,
      PlainBnfHeapSourceExecution.heapNames, PlainBnfHeapSourceExecution.rankNames])]
  exact PlainBnfHeapSourceExecution.merge_answers env fuel left right

private theorem combine_rewriteAt (base : BasePremiseEvaluator) (fuel : Nat) (source : Pattern)
    (headed : headedBy combineNames source = true) :
    rewriteAt base language (fuel + 1) source =
      combineRules.flatMap (fun rule => applyRuleUsing base language
        (rewriteAt base language fuel) rule source) := by
  apply PlainBnfHeapSourceExecution.skip_unmatched_prefix base language _ _ language_partition
  intro rule member
  exact disjoint_heads_do_not_match dependencyNames combineNames names_disjoint.symm
    rule.left source (List.all_eq_true.mp dependencies_heads rule member) headed

def combineCall (input : Heap Item) : Pattern :=
  call "BNFDiscoveryHeapCombineV1" [heap input]

private theorem combine_nil (base : BasePremiseEvaluator) (fuel : Nat) :
    rewriteAt base language (fuel + 1) (combineCall .nil) = [result (heap .nil)] := by
  rw [combine_rewriteAt base fuel _ (by rfl)]
  simp [rules_exact, observedRules, observed, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.observedRule, applyRuleUsing,
    combineCall, call, result, heap, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem combine_one (base : BasePremiseEvaluator) (fuel : Nat)
    (item : Item) (children : Heap Item) :
    rewriteAt base language (fuel + 1) (combineCall (.node item children .nil)) =
      [result (heap (.node item children .nil))] := by
  rw [combine_rewriteAt base fuel _ (by rfl)]
  simp [rules_exact, observedRules, observed, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.observedRule, applyRuleUsing,
    combineCall, call, result, heap, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private def pairRule : RewriteRule := combineRules[2]'(by rw [rules_exact]; decide)

private theorem pairRule_exact : pairRule = observedRules[2]'(by decide) := rfl

private def pairBindings (left right : Item) (lc rc rest : Heap Item) : Bindings :=
  [("?lc", encode (heap lc)), ("?right", encode (rankedDefinition right)),
   ("?rest", encode (heap rest)), ("?rc", encode (heap rc)),
   ("?left", encode (rankedDefinition left))]

private theorem pair_match (left right : Item) (lc rc rest : Heap Item) :
    matchPattern pairRule.left (combineCall (.node left lc (.node right rc rest))) =
      [pairBindings left right lc rc rest] := by
  conv_lhs =>
    simp [pairRule_exact, observedRules, observed, PlainBnfHeapSourceExecution.observed,
      PlainBnfTrieSourceExecution.observedRule,
      combineCall, call, heap, pattern, patternList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM]
  rfl

private theorem pair_only (base : BasePremiseEvaluator) (fuel : Nat)
    (left right : Item) (lc rc rest : Heap Item) :
    rewriteAt base language (fuel + 1) (combineCall (.node left lc (.node right rc rest))) =
      applyRuleUsing base language (rewriteAt base language fuel) pairRule
        (combineCall (.node left lc (.node right rc rest))) := by
  rw [combine_rewriteAt base fuel _ (by rfl)]
  simp [rules_exact, observedRules, observed, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.observedRule, pairRule_exact, applyRuleUsing,
    combineCall, call, heap, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem pair_first_none (base : BasePremiseEvaluator) (fuel : Nat)
    (left right : Item) (lc rc rest : Heap Item)
    (first : rewriteAt base language fuel (mergeCall (.node left lc .nil) (.node right rc .nil)) = []) :
    rewriteAt base language (fuel + 1) (combineCall (.node left lc (.node right rc rest))) = [] := by
  rw [pair_only, applyRuleUsing, matchPatternForRule_eq_syntactic, pair_match]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [pairRule_exact, observedRules, observed, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.observedRule, pairBindings, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, mergeBindings, premisesUsing,
    premiseStepUsing, applyBindings]
  simp only [mergeCall, call, heap, encode, encodeList] at first
  rw [first]
  simp

private theorem pair_following_none (base : BasePremiseEvaluator) (fuel : Nat)
    (left right : Item) (lc rc rest pair : Heap Item)
    (first : rewriteAt base language fuel (mergeCall (.node left lc .nil) (.node right rc .nil)) =
      [result (heap pair)])
    (following : rewriteAt base language fuel (combineCall rest) = []) :
    rewriteAt base language (fuel + 1) (combineCall (.node left lc (.node right rc rest))) = [] := by
  rw [pair_only, applyRuleUsing, matchPatternForRule_eq_syntactic, pair_match]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [pairRule_exact, observedRules, observed, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.observedRule, pairBindings, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, mergeBindings, premisesUsing,
    premiseStepUsing, applyBindings]
  simp only [mergeCall, call, result, heap, encode, encodeList] at first
  rw [first]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [combineCall, call, encode, encodeList] at following
  rw [following]
  simp

private theorem pair_last_none (base : BasePremiseEvaluator) (fuel : Nat)
    (left right : Item) (lc rc rest pair following : Heap Item)
    (first : rewriteAt base language fuel (mergeCall (.node left lc .nil) (.node right rc .nil)) =
      [result (heap pair)])
    (second : rewriteAt base language fuel (combineCall rest) = [result (heap following)])
    (last : rewriteAt base language fuel (mergeCall pair following) = []) :
    rewriteAt base language (fuel + 1) (combineCall (.node left lc (.node right rc rest))) = [] := by
  rw [pair_only, applyRuleUsing, matchPatternForRule_eq_syntactic, pair_match]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [pairRule_exact, observedRules, observed, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.observedRule, pairBindings, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, mergeBindings, premisesUsing,
    premiseStepUsing, applyBindings]
  simp only [mergeCall, call, result, heap, encode, encodeList] at first
  rw [first]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [combineCall, call, result, encode, encodeList] at second
  rw [second]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [mergeCall, call, encode, encodeList] at last
  rw [last]
  simp

private theorem pair_complete (base : BasePremiseEvaluator) (fuel : Nat)
    (left right : Item) (lc rc rest pair following output : Heap Item)
    (first : rewriteAt base language fuel (mergeCall (.node left lc .nil) (.node right rc .nil)) =
      [result (heap pair)])
    (second : rewriteAt base language fuel (combineCall rest) = [result (heap following)])
    (last : rewriteAt base language fuel (mergeCall pair following) = [result (heap output)]) :
    rewriteAt base language (fuel + 1) (combineCall (.node left lc (.node right rc rest))) =
      [result (heap output)] := by
  rw [pair_only, applyRuleUsing, matchPatternForRule_eq_syntactic, pair_match]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [pairRule_exact, observedRules, observed, PlainBnfHeapSourceExecution.observed,
    PlainBnfTrieSourceExecution.observedRule, pairBindings, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, mergeBindings, premisesUsing,
    premiseStepUsing, applyBindings]
  simp only [mergeCall, call, result, heap, encode, encodeList] at first
  rw [first]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [combineCall, call, result, encode, encodeList] at second
  rw [second]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [mergeCall, call, result, encode, encodeList] at last
  rw [last]
  simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

/-- Contextual depth of the three ordered source premises. This bound is not
used to compute an executable heap answer. -/
def combineHeight : Heap Item → Nat
  | .node left lc (.node right rc rest) =>
      max (mergeHeight (.node left lc .nil) (.node right rc .nil))
        (max (combineHeight rest)
          (mergeHeight ((Heap.node left lc .nil).merge itemLE (.node right rc .nil))
            (rest.combine itemLE))) + 1
  | _ => 0
termination_by forest => forest.size
decreasing_by simp [Heap.size]

theorem combine_pair_eq (left right : Item) (lc rc rest : Heap Item) :
    (Heap.node left lc (.node right rc rest)).combine itemLE =
      ((Heap.node left lc .nil).merge itemLE (.node right rc .nil)).merge itemLE
        (rest.combine itemLE) := rfl

theorem combine_answers (env : RelationEnv) (fuel : Nat) (input : Heap Item) :
    rewriteAt (engineBasePremises env) language fuel (combineCall input) =
      if combineHeight input < fuel then [result (heap (input.combine itemLE))] else [] := by
  induction fuel generalizing input with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
      cases input with
      | nil => simpa [combineHeight, Heap.combine] using combine_nil (engineBasePremises env) fuel
      | node left lc siblings =>
          cases siblings with
          | nil => simpa [combineHeight, Heap.combine] using combine_one (engineBasePremises env) fuel left lc
          | node right rc rest =>
              have first := merge_answers env fuel (.node left lc .nil) (.node right rc .nil)
              have second := ih rest
              have last := merge_answers env fuel
                ((Heap.node left lc .nil).merge itemLE (.node right rc .nil)) (rest.combine itemLE)
              by_cases hfirst : mergeHeight (.node left lc .nil) (.node right rc .nil) < fuel
              · simp only [hfirst, ↓reduceIte] at first
                by_cases hsecond : combineHeight rest < fuel
                · simp only [hsecond, ↓reduceIte] at second
                  by_cases hlast : mergeHeight
                      ((Heap.node left lc .nil).merge itemLE (.node right rc .nil))
                      (rest.combine itemLE) < fuel
                  · simp only [hlast, ↓reduceIte] at last
                    have completed := pair_complete (engineBasePremises env) fuel left right lc rc rest
                      _ _ _ first second last
                    simpa [combineHeight, Nat.add_lt_add_iff_right, max_lt_iff,
                      hfirst, hsecond, hlast, combine_pair_eq] using completed
                  · simp only [hlast, ↓reduceIte] at last
                    have absent := pair_last_none (engineBasePremises env) fuel left right lc rc rest
                      _ _ first second last
                    simpa [combineHeight, Nat.add_lt_add_iff_right, max_lt_iff,
                      hfirst, hsecond, hlast] using absent
                · simp only [hsecond, ↓reduceIte] at second
                  have absent := pair_following_none (engineBasePremises env) fuel left right lc rc rest
                    _ first second
                  simpa [combineHeight, Nat.add_lt_add_iff_right, max_lt_iff,
                    hfirst, hsecond] using absent
              · simp only [hfirst, ↓reduceIte] at first
                have absent := pair_first_none (engineBasePremises env) fuel left right lc rc rest first
                simpa [combineHeight, Nat.add_lt_add_iff_right, max_lt_iff, hfirst] using absent

theorem combine_step_iff (env : RelationEnv) (input : Heap Item) (target : Pattern) :
    Step (engineBasePremises env) language (combineCall input) target ↔
      target = result (heap (input.combine itemLE)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [combine_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨combineHeight input + 1, by simp [combine_answers]⟩

theorem combine_decoded_step_iff (env : RelationEnv) (input output : Heap Item) :
    Step (engineBasePremises env) language (combineCall input) (result (heap output)) ↔
      output = input.combine itemLE := by
  rw [combine_step_iff, PlainBnfHeapSourceExecution.result_heap_injective.eq_iff]

theorem combine_source_contents (env : RelationEnv) (input output : Heap Item)
    (returned : Step (engineBasePremises env) language (combineCall input) (result (heap output))) :
    PlainBnfPairingHeapObservation.contents output = PlainBnfPairingHeapObservation.contents input := by
  rw [(combine_decoded_step_iff env input output).mp returned]
  exact PlainBnfPairingHeapObservation.contents_combine itemLE input

theorem combine_source_no_sibling (env : RelationEnv) (input output : Heap Item)
    (returned : Step (engineBasePremises env) language (combineCall input) (result (heap output))) :
    output.NoSibling := by
  rw [(combine_decoded_step_iff env input output).mp returned]
  exact Heap.noSibling_combine itemLE input

/-- A child forest ordered beneath a root produces a well-formed heap. -/
theorem combine_source_WF (env : RelationEnv) (input output : Heap Item) (root : Item)
    (ordered : input.NodeWF itemLE root)
    (returned : Step (engineBasePremises env) language (combineCall input) (result (heap output))) :
    output.WF itemLE := by
  rw [(combine_decoded_step_iff env input output).mp returned]
  exact Heap.WF.combine ordered

theorem two_siblings_preserved (env : RelationEnv) (first second : Item) :
    let forest := Heap.node first Heap.nil (Heap.node second Heap.nil Heap.nil)
    ∃ output, Step (engineBasePremises env) language (combineCall forest) (result (heap output)) ∧
      output.NoSibling ∧
      PlainBnfPairingHeapObservation.contents output = first ::ₘ second ::ₘ 0 := by
  dsimp
  refine ⟨(Heap.node first .nil (.node second .nil .nil)).combine itemLE,
    (combine_decoded_step_iff _ _ _).mpr rfl, Heap.noSibling_combine _ _, ?_⟩
  rw [PlainBnfPairingHeapObservation.contents_combine]
  simp [PlainBnfPairingHeapObservation.contents]

theorem duplicate_payload_occurrences_preserved (env : RelationEnv) (item : Item) :
    let forest := Heap.node item Heap.nil (Heap.node item Heap.nil Heap.nil)
    ∃ output, Step (engineBasePremises env) language (combineCall forest) (result (heap output)) ∧
      PlainBnfPairingHeapObservation.contents output = item ::ₘ item ::ₘ 0 ∧
      PlainBnfPairingHeapObservation.contents output ≠ item ::ₘ 0 := by
  obtain ⟨output, returned, _, contents⟩ := two_siblings_preserved env item item
  exact ⟨output, returned, contents, by
    rw [contents]
    intro same
    have sizes := congrArg Multiset.card same
    simp at sizes⟩

theorem recursive_siblings_preserved (env : RelationEnv) (first second third : Item) :
    let forest := Heap.node first Heap.nil
      (Heap.node second Heap.nil (Heap.node third Heap.nil Heap.nil))
    ∃ output, Step (engineBasePremises env) language (combineCall forest) (result (heap output)) ∧
      PlainBnfPairingHeapObservation.contents output = first ::ₘ second ::ₘ third ::ₘ 0 := by
  dsimp
  refine ⟨(Heap.node first .nil (.node second .nil (.node third .nil .nil))).combine itemLE,
    (combine_decoded_step_iff _ _ _).mpr rfl, ?_⟩
  rw [PlainBnfPairingHeapObservation.contents_combine]
  simp [PlainBnfPairingHeapObservation.contents]

theorem recursive_tail_not_omitted (env : RelationEnv) (first second third : Item) :
    ¬ Step (engineBasePremises env) language
      (combineCall (.node first .nil (.node second .nil (.node third .nil .nil))))
      (result (heap ((Heap.node first .nil .nil).merge itemLE (.node second .nil .nil)))) := by
  intro returned
  have preserved := combine_source_contents env _ _ returned
  rw [PlainBnfPairingHeapObservation.contents_merge itemLE (.node _ _) (.node _ _)] at preserved
  have sizes := congrArg Multiset.card preserved
  simp [PlainBnfPairingHeapObservation.contents] at sizes

theorem missed_sibling_refused (env : RelationEnv) (first second : Item) :
    ¬ Step (engineBasePremises env) language
      (combineCall (.node first .nil (.node second .nil .nil)))
      (result (heap (.node first .nil .nil))) := by
  intro returned
  have preserved := combine_source_contents env _ _ returned
  have sizes := congrArg Multiset.card preserved
  simp [PlainBnfPairingHeapObservation.contents] at sizes

theorem combine_is_not_merge_with_nil (env : RelationEnv) (first second : Item) :
    let forest := Heap.node first Heap.nil (Heap.node second Heap.nil Heap.nil)
    ¬ Step (engineBasePremises env) language (combineCall forest)
      (result (heap (forest.merge itemLE Heap.nil))) := by
  exact missed_sibling_refused env first second

theorem insufficient_depth_has_no_answer (env : RelationEnv) (input : Heap Item)
    (fuel : Nat) (short : fuel ≤ combineHeight input) :
    rewriteAt (engineBasePremises env) language fuel (combineCall input) = [] := by
  simp [combine_answers, Nat.not_lt.mpr short]

theorem omitted_output_refused :
    splitCall? (.list [.atom "BNFDiscoveryHeapCombineV1", heap .nil]) = none := rfl

theorem extra_argument_refused :
    splitCall? (.list [.atom "BNFDiscoveryHeapCombineV1", heap .nil, heap .nil, heap .nil]) = none := rfl

theorem scheduler_not_silently_admitted :
    mode? "BNFDiscoveryRunV1" = none := rfl

#print axioms combine_answers
#print axioms combine_step_iff
#print axioms combine_source_contents
#print axioms combine_source_WF
#print axioms duplicate_payload_occurrences_preserved
#print axioms missed_sibling_refused

end Mettapedia.GSLT.Parsing.PlainBnfHeapCombineSourceExecution
