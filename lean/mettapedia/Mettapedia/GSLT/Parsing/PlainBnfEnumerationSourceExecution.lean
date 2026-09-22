import Mettapedia.GSLT.Parsing.PlainBnfRankSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfIndexedCollectorSourceExecution
import Mathlib.Logic.Function.Iterate

/-!
# Authored definition enumeration

The original enumeration clauses and their rank dependencies are translated
from admitted structured source. Existing contextual execution is compared
with independent list indices, preserving opaque declaration payloads and
answer occurrences. This is not heap, scheduler, or generated-runtime adequacy.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfEnumerationSourceExecution

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
open PlainBnfSourceRank (Rank value successor)
open PlainBnfRankSourceExecution (rank call result nextCall nextHeight)
open PlainBnfIndexedCollectorSourceExecution
  (headedBy premiseClosed closed_extension disjoint_heads_do_not_match)

def mode? (relation : String) : Option (Nat × Nat) :=
  if relation = "BNFDiscoveryRankDefinitionsV1" then some (2, 1)
  else PlainBnfRankSourceExecution.mode? relation

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
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 5).take 17

def enumerationRows : List Rewrite :=
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 20).take 2

def rules? : Option (List RewriteRule) := rows.mapM lowerRule?

theorem rules_present : rules?.isSome = true := rfl

def language : LanguageDef :=
  { name := "PlainBnfAuthoredDefinitionEnumeration", types := [], terms := [], equations := [],
    rewrites := rules?.get rules_present }

def enumerationRules : List RewriteRule :=
  (enumerationRows.mapM lowerRule?).get (by rfl)

theorem source_translation_exact : rows.mapM lowerRule? = some language.rewrites := by rfl

theorem source_occurrences_exact : rows.zipIdx 5 =
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 5).take 17 := by rfl

theorem enumeration_occurrences_exact : enumerationRows.zipIdx 20 =
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 20).take 2 := by rfl

theorem language_partition :
    language.rewrites = PlainBnfRankSourceExecution.language.rewrites ++ enumerationRules := by rfl

/-- Checked observations of translated source, not executable replacement rules. -/
private def observed (ruleName : String) (input output : SExpr)
    (premises : List Premise := []) : RewriteRule :=
  { name := ruleName, typeContext := [], premises, left := pattern input,
    right := pattern (.list [output]) }

private def observedRules : List RewriteRule := [
  observed "bnf-discovery-rank-definitions-nil-v1"
    (.list [.atom "BNFDiscoveryRankDefinitionsV1", .atom "BNFDefinitionsNilV1", .atom "?rank"])
    (.atom "BNFDiscoveryDefinitionsNilV1"),
  observed "bnf-discovery-rank-definitions-cons-v1"
    (.list [.atom "BNFDiscoveryRankDefinitionsV1",
      .list [.atom "BNFDefinitionsConsV1",
        .list [.atom "BNFDefinitionV1", .atom "?name", .atom "?expression", .atom "?span"],
        .atom "?tail"], .atom "?rank"])
    (.list [.atom "BNFDiscoveryDefinitionsConsV1",
      .list [.atom "BNFDiscoveryDefinitionV1", .atom "?rank", .atom "?name",
        .atom "?expression", .atom "?span"], .atom "?after"])
    [.congruence (pattern (.list [.atom "BNFDiscoveryRankNextV1", .atom "?rank"]))
      (pattern (.list [.atom "?next"])),
     .congruence (pattern (.list [.atom "BNFDiscoveryRankDefinitionsV1", .atom "?tail", .atom "?next"]))
      (pattern (.list [.atom "?after"]))]]

private theorem enumeration_rules_exact : enumerationRules = observedRules := by rfl

def rankNames : List String :=
  ["BNFDiscoveryRankNextV1", "BNFDiscoveryRankCompareV1", "BNFDiscoveryRankTieV1"]

def enumerationNames : List String := ["BNFDiscoveryRankDefinitionsV1"]

theorem rank_closed : PlainBnfRankSourceExecution.language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed rankNames)) = true := by
  simp [PlainBnfRankSourceExecution.rules_exact, PlainBnfRankSourceExecution.observedRules,
    PlainBnfRankSourceExecution.observed, premiseClosed, headedBy, rankNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem rank_heads : PlainBnfRankSourceExecution.language.rewrites.all
    (fun rule => headedBy rankNames rule.left) = true := by
  simp [PlainBnfRankSourceExecution.rules_exact, PlainBnfRankSourceExecution.observedRules,
    PlainBnfRankSourceExecution.observed, headedBy, rankNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem enumeration_heads : enumerationRules.all
    (fun rule => headedBy enumerationNames rule.left) = true := by
  simp [enumeration_rules_exact, observedRules, observed, headedBy, enumerationNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem names_disjoint : List.Disjoint enumerationNames rankNames := by
  simp [enumerationNames, rankNames]

theorem rank_conservative_extension (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy rankNames source = true) :
    rewriteAt (engineBasePremises env) language fuel source =
      rewriteAt (engineBasePremises env) PlainBnfRankSourceExecution.language fuel source := by
  apply closed_extension rankNames env PlainBnfRankSourceExecution.language language [] enumerationRules
    (by simpa using language_partition) ?_ ?_ fuel source headed
  · intro rule member premise inside
    exact List.all_eq_true.mp (List.all_eq_true.mp rank_closed rule member) premise inside
  · intro rule member term termHead
    exact disjoint_heads_do_not_match enumerationNames rankNames names_disjoint _ _
      (List.all_eq_true.mp enumeration_heads rule (by simpa using member)) termHead

theorem next_answers (env : RelationEnv) (fuel : Nat) (input : Rank) :
    rewriteAt (engineBasePremises env) language fuel (nextCall input) =
      if nextHeight input < fuel then [result (rank (successor input))] else [] := by
  rw [rank_conservative_extension env fuel _ (by rfl)]
  exact PlainBnfRankSourceExecution.next_answers (engineBasePremises env) fuel input

abbrev Definition := PlainBnfDeclarationSemantics.Definition SExpr SExpr SExpr

def definition (item : Definition) : SExpr :=
  .list [.atom "BNFDefinitionV1", item.name, item.expression, item.span]

def definitions (input : List Definition) : SExpr :=
  PlainBnfCollectorSourceExecution.definitions (input.map definition)

def rankedDefinition (item : Rank × Definition) : SExpr :=
  .list [.atom "BNFDiscoveryDefinitionV1", rank item.1,
    item.2.name, item.2.expression, item.2.span]

def rankedDefinitions : List (Rank × Definition) → SExpr
  | [] => .atom "BNFDiscoveryDefinitionsNilV1"
  | head :: tail => .list [.atom "BNFDiscoveryDefinitionsConsV1", rankedDefinition head,
      rankedDefinitions tail]

def enumerationCall (input : List Definition) (start : Rank) : Pattern :=
  call "BNFDiscoveryRankDefinitionsV1" [definitions input, rank start]

/-- The reference assigns coordinates by ordinary list indices. It is not
used to construct any executable source clause. -/
def enumerate (input : List Definition) (start : Rank) : List (Rank × Definition) :=
  input.zipIdx.map fun (item, position) => ((successor^[position]) start, item)

theorem enumerate_nil (start : Rank) : enumerate [] start = [] := rfl

theorem enumerate_cons (head : Definition) (tail : List Definition) (start : Rank) :
    enumerate (head :: tail) start = (start, head) :: enumerate tail (successor start) := by
  simp only [enumerate, List.zipIdx_cons', List.map_cons, List.map_map]
  rfl

private theorem enumeration_rewriteAt (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy enumerationNames source = true) :
    rewriteAt (engineBasePremises env) language (fuel + 1) source =
      enumerationRules.flatMap (fun rule => applyRuleUsing (engineBasePremises env) language
        (rewriteAt (engineBasePremises env) language fuel) rule source) := by
  rw [rewriteAt, language_partition, List.flatMap_append]
  have noRank : PlainBnfRankSourceExecution.language.rewrites.flatMap
      (fun rule => applyRuleUsing (engineBasePremises env) language
        (rewriteAt (engineBasePremises env) language fuel) rule source) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    have absent := disjoint_heads_do_not_match rankNames enumerationNames names_disjoint.symm
      _ _ (List.all_eq_true.mp rank_heads rule member) headed
    simp [applyRuleUsing, absent]
  rw [noRank, List.nil_append]

private theorem enumeration_nil (env : RelationEnv) (fuel : Nat) (start : Rank) :
    rewriteAt (engineBasePremises env) language (fuel + 1) (enumerationCall [] start) =
      [result (rankedDefinitions [])] := by
  rw [enumeration_rewriteAt env fuel _ (by rfl)]
  simp [enumeration_rules_exact, observedRules, observed, applyRuleUsing,
    enumerationCall, definitions, PlainBnfCollectorSourceExecution.definitions,
    call, result, rankedDefinitions, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem enumeration_cons (env : RelationEnv) (fuel : Nat)
    (head : Definition) (tail : List Definition) (start : Rank) (answers : List SExpr)
    (next : rewriteAt (engineBasePremises env) language fuel (nextCall start) =
      [result (rank (successor start))])
    (recursive : rewriteAt (engineBasePremises env) language fuel
      (enumerationCall tail (successor start)) = answers.map result) :
    rewriteAt (engineBasePremises env) language (fuel + 1)
      (enumerationCall (head :: tail) start) =
      answers.map (fun after => result (.list [.atom "BNFDiscoveryDefinitionsConsV1",
        rankedDefinition (start, head), after])) := by
  rw [enumeration_rewriteAt env fuel _ (by rfl)]
  simp [enumeration_rules_exact, observedRules, observed, applyRuleUsing,
    enumerationCall, definitions, definition, PlainBnfCollectorSourceExecution.definitions,
    call, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [nextCall, call, result, encode, encodeList] at next
  rw [next]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [enumerationCall, definitions, call, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp [← List.map_eq_flatMap, rankedDefinition, encode, encodeList]

private theorem enumeration_next_exhausted (env : RelationEnv) (fuel : Nat)
    (head : Definition) (tail : List Definition) (start : Rank)
    (next : rewriteAt (engineBasePremises env) language fuel (nextCall start) = []) :
    rewriteAt (engineBasePremises env) language (fuel + 1)
      (enumerationCall (head :: tail) start) = [] := by
  rw [enumeration_rewriteAt env fuel _ (by rfl)]
  simp [enumeration_rules_exact, observedRules, observed, applyRuleUsing,
    enumerationCall, definitions, definition, PlainBnfCollectorSourceExecution.definitions,
    call, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [nextCall, call, encode, encodeList] at next
  rw [next]
  simp

/-- The needed contextual depth records both genuine recursive dependencies;
it does not compute a result or stand in for either source call. -/
def enumerationHeight : List Definition → Rank → Nat
  | [], _ => 0
  | _ :: tail, start => max (nextHeight start) (enumerationHeight tail (successor start)) + 1

theorem enumeration_answers (env : RelationEnv) (fuel : Nat)
    (input : List Definition) (start : Rank) :
    rewriteAt (engineBasePremises env) language fuel (enumerationCall input start) =
      if enumerationHeight input start < fuel then
        [result (rankedDefinitions (enumerate input start))] else [] := by
  induction fuel generalizing input start with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
      cases input with
      | nil => simpa [enumerationHeight, enumerate_nil] using enumeration_nil env fuel start
      | cons head tail =>
          by_cases rankEnough : nextHeight start < fuel
          · have next := next_answers env fuel start
            simp only [rankEnough, ↓reduceIte] at next
            by_cases tailEnough : enumerationHeight tail (successor start) < fuel
            · have recursive := ih tail (successor start)
              simp only [tailEnough, ↓reduceIte] at recursive
              have step := enumeration_cons env fuel head tail start
                [rankedDefinitions (enumerate tail (successor start))] next (by simpa using recursive)
              have enough : enumerationHeight (head :: tail) start < fuel + 1 := by
                simp only [enumerationHeight]
                omega
              simpa [enough, enumerate_cons, rankedDefinitions] using step
            · have recursive := ih tail (successor start)
              simp only [tailEnough, ↓reduceIte] at recursive
              have step := enumeration_cons env fuel head tail start [] next (by simpa using recursive)
              have short : ¬ enumerationHeight (head :: tail) start < fuel + 1 := by
                simp only [enumerationHeight]
                omega
              simpa [short] using step
          · have next := next_answers env fuel start
            simp only [rankEnough, ↓reduceIte] at next
            have step := enumeration_next_exhausted env fuel head tail start next
            have short : ¬ enumerationHeight (head :: tail) start < fuel + 1 := by
              simp only [enumerationHeight]
              omega
            simpa [short] using step

theorem enumeration_step_iff (env : RelationEnv) (input : List Definition) (start : Rank)
    (target : Pattern) :
    Step (engineBasePremises env) language (enumerationCall input start) target ↔
      target = result (rankedDefinitions (enumerate input start)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [enumeration_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨enumerationHeight input start + 1, by simp [enumeration_answers]⟩

theorem enumerate_payloads (input : List Definition) (start : Rank) :
    (enumerate input start).map Prod.snd = input := by
  induction input generalizing start with
  | nil => rfl
  | cons head tail ih => simp [enumerate_cons, ih]

theorem value_iterate (count : Nat) (start : Rank) :
    value ((successor^[count]) start) = value start + count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply, ih, PlainBnfSourceRank.value_successor]
      omega

/-- Position coordinates are the original zero-based list indices, shifted
by the supplied initial rank. Names, expressions, and spans remain attached. -/
theorem enumerate_numeric_coordinates (input : List Definition) (start : Rank) :
    (enumerate input start).map (fun (position, item) => (value position, item)) =
      input.zipIdx.map (fun (item, index) => (value start + index, item)) := by
  simp [enumerate, List.map_map, Function.comp_def, value_iterate]

theorem rank_injective : Function.Injective rank := by
  intro left
  induction left with
  | zero =>
      intro right same
      cases right <;> simp_all [rank]
  | one rest ih =>
      intro right same
      cases right with
      | zero => simp [rank] at same
      | one other =>
          apply congrArg Rank.one
          exact ih (by simpa [rank] using same)
      | two other => simp [rank] at same
  | two rest ih =>
      intro right same
      cases right with
      | zero => simp [rank] at same
      | one other => simp [rank] at same
      | two other =>
          apply congrArg Rank.two
          exact ih (by simpa [rank] using same)

theorem rankedDefinition_injective : Function.Injective rankedDefinition := by
  rintro ⟨leftRank, ⟨leftName, leftExpression, leftSpan⟩⟩
    ⟨rightRank, ⟨rightName, rightExpression, rightSpan⟩⟩ same
  simp only [rankedDefinition, SExpr.list.injEq, List.cons.injEq, true_and, and_true] at same
  obtain ⟨ranks, rfl, rfl, rfl⟩ := same
  have equalRanks := rank_injective ranks
  subst rightRank
  rfl

theorem rankedDefinitions_injective : Function.Injective rankedDefinitions := by
  intro left
  induction left with
  | nil =>
      intro right same
      cases right <;> simp_all [rankedDefinitions]
  | cons head tail ih =>
      intro right same
      cases right with
      | nil => simp [rankedDefinitions] at same
      | cons other rest =>
          simp only [rankedDefinitions, SExpr.list.injEq, List.cons.injEq, true_and, and_true] at same
          exact congrArg₂ List.cons (rankedDefinition_injective same.1) (ih same.2)

theorem result_injective : Function.Injective result := by
  intro left right same
  have decoded := SourceSExprPatternCodec.encode_injective same
  simpa [result] using decoded

theorem enumeration_decoded_step_iff (env : RelationEnv) (input : List Definition)
    (start : Rank) (output : List (Rank × Definition)) :
    Step (engineBasePremises env) language (enumerationCall input start)
      (result (rankedDefinitions output)) ↔ output = enumerate input start := by
  rw [enumeration_step_iff, result_injective.eq_iff, rankedDefinitions_injective.eq_iff]

theorem execution_preserves_ordered_payloads (env : RelationEnv) (input : List Definition)
    (start : Rank) (output : List (Rank × Definition))
    (executed : Step (engineBasePremises env) language (enumerationCall input start)
      (result (rankedDefinitions output))) :
    output.map Prod.snd = input := by
  rw [(enumeration_decoded_step_iff env input start output).mp executed]
  exact enumerate_payloads input start

theorem execution_preserves_source_coordinates (env : RelationEnv) (input : List Definition)
    (start : Rank) (output : List (Rank × Definition))
    (executed : Step (engineBasePremises env) language (enumerationCall input start)
      (result (rankedDefinitions output))) :
    output.map (fun (position, item) => (value position, item)) =
      input.zipIdx.map (fun (item, index) => (value start + index, item)) := by
  rw [(enumeration_decoded_step_iff env input start output).mp executed]
  exact enumerate_numeric_coordinates input start

theorem repeated_definition_occurrences_survive (env : RelationEnv) (item : Definition)
    (start : Rank) :
    Step (engineBasePremises env) language (enumerationCall [item, item] start)
      (result (rankedDefinitions [(start, item), (successor start, item)])) := by
  simp [enumeration_decoded_step_iff, enumerate_cons, enumerate_nil]

theorem repeated_definition_cannot_collapse (env : RelationEnv) (item : Definition)
    (start : Rank) :
    ¬ Step (engineBasePremises env) language (enumerationCall [item, item] start)
      (result (rankedDefinitions [(start, item)])) := by
  simp [enumeration_decoded_step_iff, enumerate_cons, enumerate_nil]

theorem changed_span_is_not_an_enumeration (env : RelationEnv)
    (name expression original changed : SExpr) (different : original ≠ changed) :
    ¬ Step (engineBasePremises env) language
      (enumerationCall [⟨name, expression, original⟩] .zero)
      (result (rankedDefinitions [(.zero, ⟨name, expression, changed⟩)])) := by
  simp [enumeration_decoded_step_iff, enumerate_cons, enumerate_nil, Ne.symm different]

theorem incomplete_depth_returns_no_prefix (env : RelationEnv) (input : List Definition)
    (start : Rank) (fuel : Nat) (short : fuel ≤ enumerationHeight input start) :
    rewriteAt (engineBasePremises env) language fuel (enumerationCall input start) = [] := by
  simp [enumeration_answers, Nat.not_lt.mpr short]

#print axioms enumeration_answers
#print axioms enumeration_step_iff
#print axioms enumerate_numeric_coordinates
#print axioms execution_preserves_ordered_payloads
#print axioms execution_preserves_source_coordinates

end Mettapedia.GSLT.Parsing.PlainBnfEnumerationSourceExecution
