import Mettapedia.GSLT.Parsing.PlainBnfCollectorSourceAdmission
import Mettapedia.GSLT.Parsing.PlainBnfSourceRank

/-!
# Authored worklist rank execution

The admitted discovery source supplies all executable rules. A checked local
input/output mode translates its rank calls to the existing contextual
relation. The independently defined structural ranks specify the observation;
they are not providers used by execution. Source quotation, generated PeTTa,
heap execution, and the complete discovery loop remain separate boundaries.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfRankSourceExecution

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
open PlainBnfSourceRank (Rank value successor compareRank)

def mode? : String → Option (Nat × Nat)
  | "BNFDiscoveryRankNextV1" => some (1, 1)
  | "BNFDiscoveryRankCompareV1" | "BNFDiscoveryRankTieV1" => some (2, 1)
  | _ => none

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
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 5).take 15

def rules? : Option (List RewriteRule) := rows.mapM lowerRule?

theorem rules_present : rules?.isSome = true := rfl

def language : LanguageDef :=
  { name := "PlainBnfAuthoredStructuralRanks", types := [], terms := [], equations := [],
    rewrites := rules?.get rules_present }

theorem translation_exact : rows.mapM lowerRule? = some language.rewrites := by rfl

theorem source_occurrences_exact :
    rows.zipIdx 5 =
      ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 5).take 15 := by rfl

theorem source_rule_count : language.rewrites.length = 15 := by rfl

def rank : Rank → SExpr
  | .zero => .atom "BNFDiscoveryRankZeroV1"
  | .one rest => .list [.atom "BNFDiscoveryRankOneV1", rank rest]
  | .two rest => .list [.atom "BNFDiscoveryRankTwoV1", rank rest]

def order : Ordering → SExpr
  | .lt => .atom "BNFDiscoveryLessV1"
  | .eq => .atom "BNFDiscoveryEqualV1"
  | .gt => .atom "BNFDiscoveryGreaterV1"

def call (relation : String) (arguments : List SExpr) : Pattern :=
  encode (.list (.atom relation :: arguments))

def result (output : SExpr) : Pattern := encode (.list [output])

def nextCall (input : Rank) : Pattern := call "BNFDiscoveryRankNextV1" [rank input]

def compareCall (left right : Rank) : Pattern :=
  call "BNFDiscoveryRankCompareV1" [rank left, rank right]

def tieCall (comparison tie : Ordering) : Pattern :=
  call "BNFDiscoveryRankTieV1" [order comparison, order tie]

/-- These displayed shapes are observations of translated source, not a
replacement executable artifact. -/
def observed (ruleName : String) (input output : SExpr)
    (premises : List Premise := []) : RewriteRule :=
  { name := ruleName, typeContext := [], premises, left := pattern input,
    right := pattern (.list [output]) }

def observedRules : List RewriteRule := [
  observed "bnf-discovery-rank-next-zero-v1"
    (.list [.atom "BNFDiscoveryRankNextV1", rank .zero]) (rank (.one .zero)),
  observed "bnf-discovery-rank-next-one-v1"
    (.list [.atom "BNFDiscoveryRankNextV1", .list [.atom "BNFDiscoveryRankOneV1", .atom "?rank"]])
    (.list [.atom "BNFDiscoveryRankTwoV1", .atom "?rank"]),
  observed "bnf-discovery-rank-next-two-v1"
    (.list [.atom "BNFDiscoveryRankNextV1", .list [.atom "BNFDiscoveryRankTwoV1", .atom "?rank"]])
    (.list [.atom "BNFDiscoveryRankOneV1", .atom "?next"])
    [.congruence (pattern (.list [.atom "BNFDiscoveryRankNextV1", .atom "?rank"]))
      (pattern (.list [.atom "?next"]))],
  observed "bnf-discovery-rank-compare-zero-v1"
    (.list [.atom "BNFDiscoveryRankCompareV1", rank .zero, rank .zero]) (order .eq),
  observed "bnf-discovery-rank-zero-one-v1"
    (.list [.atom "BNFDiscoveryRankCompareV1", rank .zero,
      .list [.atom "BNFDiscoveryRankOneV1", .atom "?rank"]]) (order .lt),
  observed "bnf-discovery-rank-zero-two-v1"
    (.list [.atom "BNFDiscoveryRankCompareV1", rank .zero,
      .list [.atom "BNFDiscoveryRankTwoV1", .atom "?rank"]]) (order .lt),
  observed "bnf-discovery-rank-one-zero-v1"
    (.list [.atom "BNFDiscoveryRankCompareV1",
      .list [.atom "BNFDiscoveryRankOneV1", .atom "?rank"], rank .zero]) (order .gt),
  observed "bnf-discovery-rank-two-zero-v1"
    (.list [.atom "BNFDiscoveryRankCompareV1",
      .list [.atom "BNFDiscoveryRankTwoV1", .atom "?rank"], rank .zero]) (order .gt),
  observed "bnf-discovery-rank-one-one-v1"
    (.list [.atom "BNFDiscoveryRankCompareV1",
      .list [.atom "BNFDiscoveryRankOneV1", .atom "?left"],
      .list [.atom "BNFDiscoveryRankOneV1", .atom "?right"]]) (.atom "?result")
    [.congruence (pattern (.list [.atom "BNFDiscoveryRankCompareV1", .atom "?left", .atom "?right"]))
      (pattern (.list [.atom "?result"]))],
  observed "bnf-discovery-rank-two-two-v1"
    (.list [.atom "BNFDiscoveryRankCompareV1",
      .list [.atom "BNFDiscoveryRankTwoV1", .atom "?left"],
      .list [.atom "BNFDiscoveryRankTwoV1", .atom "?right"]]) (.atom "?result")
    [.congruence (pattern (.list [.atom "BNFDiscoveryRankCompareV1", .atom "?left", .atom "?right"]))
      (pattern (.list [.atom "?result"]))],
  observed "bnf-discovery-rank-one-two-v1"
    (.list [.atom "BNFDiscoveryRankCompareV1",
      .list [.atom "BNFDiscoveryRankOneV1", .atom "?left"],
      .list [.atom "BNFDiscoveryRankTwoV1", .atom "?right"]]) (.atom "?result")
    [.congruence (pattern (.list [.atom "BNFDiscoveryRankCompareV1", .atom "?left", .atom "?right"]))
      (pattern (.list [.atom "?high"])),
     .congruence (pattern (.list [.atom "BNFDiscoveryRankTieV1", .atom "?high", order .lt]))
      (pattern (.list [.atom "?result"]))],
  observed "bnf-discovery-rank-two-one-v1"
    (.list [.atom "BNFDiscoveryRankCompareV1",
      .list [.atom "BNFDiscoveryRankTwoV1", .atom "?left"],
      .list [.atom "BNFDiscoveryRankOneV1", .atom "?right"]]) (.atom "?result")
    [.congruence (pattern (.list [.atom "BNFDiscoveryRankCompareV1", .atom "?left", .atom "?right"]))
      (pattern (.list [.atom "?high"])),
     .congruence (pattern (.list [.atom "BNFDiscoveryRankTieV1", .atom "?high", order .gt]))
      (pattern (.list [.atom "?result"]))],
  observed "bnf-discovery-rank-tie-less-v1"
    (.list [.atom "BNFDiscoveryRankTieV1", order .lt, .atom "?tie"]) (order .lt),
  observed "bnf-discovery-rank-tie-equal-v1"
    (.list [.atom "BNFDiscoveryRankTieV1", order .eq, .atom "?tie"]) (.atom "?tie"),
  observed "bnf-discovery-rank-tie-greater-v1"
    (.list [.atom "BNFDiscoveryRankTieV1", order .gt, .atom "?tie"]) (order .gt)]

theorem rules_exact : language.rewrites = observedRules := by rfl

theorem tie_answers (base : BasePremiseEvaluator) (fuel : Nat) (comparison tie : Ordering) :
    rewriteAt base language (fuel + 1) (tieCall comparison tie) =
      [result (order (if comparison = .eq then tie else comparison))] := by
  cases comparison <;> cases tie <;>
    simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
      tieCall, call, result, rank, order, pattern, patternList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem next_zero (base : BasePremiseEvaluator) (fuel : Nat) :
    rewriteAt base language (fuel + 1) (nextCall .zero) = [result (rank (.one .zero))] := by
  simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
    nextCall, call, result, rank, order, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem next_one (base : BasePremiseEvaluator) (fuel : Nat) (rest : Rank) :
    rewriteAt base language (fuel + 1) (nextCall (.one rest)) = [result (rank (.two rest))] := by
  simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
    nextCall, call, result, rank, order, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem next_two (base : BasePremiseEvaluator) (fuel : Nat) (rest : Rank)
    (answers : List SExpr)
    (recursive : rewriteAt base language fuel (nextCall rest) = answers.map result) :
    rewriteAt base language (fuel + 1) (nextCall (.two rest)) =
      answers.map (fun answer => result (.list [.atom "BNFDiscoveryRankOneV1", answer])) := by
  rw [rewriteAt]
  simp [rules_exact, observedRules, observed, applyRuleUsing,
    nextCall, call, rank, order, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing,
    premiseStepUsing, applyBindings]
  simp only [nextCall, call, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap]

/-- Contextual recursion depth, not a computation of the successor answer. -/
def nextHeight : Rank → Nat
  | .zero | .one _ => 0
  | .two rest => nextHeight rest + 1

theorem next_answers (base : BasePremiseEvaluator) (fuel : Nat) (input : Rank) :
    rewriteAt base language fuel (nextCall input) =
      if nextHeight input < fuel then [result (rank (successor input))] else [] := by
  induction fuel generalizing input with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
      cases input with
      | zero => simpa [nextHeight, successor] using next_zero base fuel
      | one rest => simpa [nextHeight, successor] using next_one base fuel rest
      | two rest =>
          by_cases enough : nextHeight rest < fuel
          · have recursive := ih rest
            simp only [enough, ↓reduceIte] at recursive
            have step := next_two base fuel rest [rank (successor rest)] (by simpa using recursive)
            simpa [nextHeight, enough, successor, rank] using step
          · have recursive := ih rest
            simp only [enough, ↓reduceIte] at recursive
            have step := next_two base fuel rest [] (by simpa using recursive)
            simpa [nextHeight, enough] using step

private theorem compare_zero (base : BasePremiseEvaluator) (fuel : Nat) (right : Rank) :
    rewriteAt base language (fuel + 1) (compareCall .zero right) =
      [result (order (compareRank .zero right))] := by
  cases right <;>
    simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
      compareCall, call, result, rank, order, compareRank, pattern, patternList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem compare_right_zero (base : BasePremiseEvaluator) (fuel : Nat) (left : Rank) :
    rewriteAt base language (fuel + 1) (compareCall left .zero) =
      [result (order (compareRank left .zero))] := by
  cases left <;>
    simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
      compareCall, call, result, rank, order, compareRank, pattern, patternList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private def digit (one : Bool) (rest : Rank) : Rank := if one then .one rest else .two rest

private theorem compare_same (base : BasePremiseEvaluator) (fuel : Nat)
    (one : Bool) (left right : Rank) (answers : List SExpr)
    (recursive : rewriteAt base language fuel (compareCall left right) = answers.map result) :
    rewriteAt base language (fuel + 1) (compareCall (digit one left) (digit one right)) =
      answers.map result := by
  rw [rewriteAt]
  cases one <;>
    simp [rules_exact, observedRules, observed, applyRuleUsing, digit,
      compareCall, call, rank, order, pattern, patternList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing,
      premiseStepUsing, applyBindings]
  all_goals
    simp only [compareCall, call, encode, encodeList] at recursive
    rw [recursive]
    simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
      List.foldlM, mergeBindings]
    simp [← List.map_eq_flatMap, result, encode, encodeList]

private theorem compare_mixed_none (base : BasePremiseEvaluator) (fuel : Nat)
    (one : Bool) (left right : Rank)
    (recursive : rewriteAt base language fuel (compareCall left right) = []) :
    rewriteAt base language (fuel + 1) (compareCall (digit one left) (digit (!one) right)) = [] := by
  rw [rewriteAt]
  cases one <;>
    simp [rules_exact, observedRules, observed, applyRuleUsing, digit,
      compareCall, call, rank, order, pattern, patternList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing,
      premiseStepUsing, applyBindings]
  all_goals
    simp only [compareCall, call, encode, encodeList] at recursive
    rw [recursive]
    simp

private theorem compare_mixed_some (base : BasePremiseEvaluator) (fuel : Nat)
    (one : Bool) (left right : Rank) (comparison : Ordering)
    (recursive : rewriteAt base language (fuel + 1) (compareCall left right) =
      [result (order comparison)]) :
    rewriteAt base language (fuel + 2) (compareCall (digit one left) (digit (!one) right)) =
      [result (order (if comparison = .eq then (if one then .lt else .gt) else comparison))] := by
  rw [rewriteAt]
  cases one <;>
    simp [rules_exact, observedRules, observed, applyRuleUsing, digit,
      compareCall, call, rank, order, pattern, patternList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing,
      premiseStepUsing, applyBindings]
  all_goals
    simp only [compareCall, call, result, encode, encodeList] at recursive
    rw [recursive]
    simp [order, matchPattern, matchArgs, mergeBindings, List.foldlM]
    first
    | have tie := tie_answers base fuel comparison .gt
      simp only [tieCall, call, result, order, encode, encodeList] at tie
      rw [tie]
    | have tie := tie_answers base fuel comparison .lt
      simp only [tieCall, call, result, order, encode, encodeList] at tie
      rw [tie]
    simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

/-- Depth of common positive prefixes. Every compared tail is smaller;
the tie clause shares the recursive layer rather than consuming a new one. -/
def compareHeight : Rank → Rank → Nat
  | .zero, _ | _, .zero => 0
  | .one left, .one right | .one left, .two right
  | .two left, .one right | .two left, .two right => compareHeight left right + 1

theorem compare_answers (base : BasePremiseEvaluator) (fuel : Nat) (left right : Rank) :
    rewriteAt base language fuel (compareCall left right) =
      if compareHeight left right < fuel then
        [result (order (compareRank left right))] else [] := by
  induction fuel generalizing left right with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
      cases left with
      | zero => simpa [compareHeight] using compare_zero base fuel right
      | one left =>
          cases right with
          | zero => simpa [compareHeight] using compare_right_zero base fuel (.one left)
          | one right =>
              by_cases enough : compareHeight left right < fuel
              · have recursive := ih left right
                simp only [enough, ↓reduceIte] at recursive
                have step := compare_same base fuel true left right [order (compareRank left right)]
                  (by simpa using recursive)
                simpa [digit, compareHeight, enough, compareRank] using step
              · have recursive := ih left right
                simp only [enough, ↓reduceIte] at recursive
                have step := compare_same base fuel true left right [] (by simpa using recursive)
                simpa [digit, compareHeight, enough] using step
          | two right =>
              by_cases enough : compareHeight left right < fuel
              · have recursive := ih left right
                simp only [enough, ↓reduceIte] at recursive
                cases fuel with
                | zero => simp at enough
                | succ fuel =>
                    have step := compare_mixed_some base fuel true left right
                      (compareRank left right) recursive
                    have bound : compareHeight left right ≤ fuel := Nat.lt_succ_iff.mp enough
                    cases comparison : compareRank left right <;>
                      simpa [digit, compareHeight, bound, compareRank, comparison] using step
              · have recursive := ih left right
                simp only [enough, ↓reduceIte] at recursive
                have step := compare_mixed_none base fuel true left right recursive
                simpa [digit, compareHeight, enough] using step
      | two left =>
          cases right with
          | zero => simpa [compareHeight] using compare_right_zero base fuel (.two left)
          | one right =>
              by_cases enough : compareHeight left right < fuel
              · have recursive := ih left right
                simp only [enough, ↓reduceIte] at recursive
                cases fuel with
                | zero => simp at enough
                | succ fuel =>
                    have step := compare_mixed_some base fuel false left right
                      (compareRank left right) recursive
                    have bound : compareHeight left right ≤ fuel := Nat.lt_succ_iff.mp enough
                    cases comparison : compareRank left right <;>
                      simpa [digit, compareHeight, bound, compareRank, comparison] using step
              · have recursive := ih left right
                simp only [enough, ↓reduceIte] at recursive
                have step := compare_mixed_none base fuel false left right recursive
                simpa [digit, compareHeight, enough] using step
          | two right =>
              by_cases enough : compareHeight left right < fuel
              · have recursive := ih left right
                simp only [enough, ↓reduceIte] at recursive
                have step := compare_same base fuel false left right [order (compareRank left right)]
                  (by simpa using recursive)
                simpa [digit, compareHeight, enough, compareRank] using step
              · have recursive := ih left right
                simp only [enough, ↓reduceIte] at recursive
                have step := compare_same base fuel false left right [] (by simpa using recursive)
                simpa [digit, compareHeight, enough] using step

/-- No arbitrary target outside the exact result is introduced, regardless
of the base provider: every selected premise is contextual, not external. -/
theorem next_step_iff (base : BasePremiseEvaluator) (input : Rank) (target : Pattern) :
    Step base language (nextCall input) target ↔ target = result (rank (successor input)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [next_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨nextHeight input + 1, by simp [next_answers]⟩

theorem compare_step_iff (base : BasePremiseEvaluator) (left right : Rank) (target : Pattern) :
    Step base language (compareCall left right) target ↔
      target = result (order (compareRank left right)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [compare_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨compareHeight left right + 1, by simp [compare_answers]⟩

theorem compare_numeric_step_iff (base : BasePremiseEvaluator) (left right : Rank)
    (target : Pattern) :
    Step base language (compareCall left right) target ↔
      target = result (order (compare (value left) (value right))) := by
  rw [compare_step_iff, PlainBnfSourceRank.compareRank_eq_value]

theorem comparison_result_injective : Function.Injective (fun comparison => result (order comparison)) := by
  intro left right
  cases left <;> cases right <;> simp [result, order, encode, encodeList]

theorem compare_decoded_step_iff (base : BasePremiseEvaluator) (left right : Rank)
    (comparison : Ordering) :
    Step base language (compareCall left right) (result (order comparison)) ↔
      comparison = compare (value left) (value right) := by
  rw [compare_numeric_step_iff, comparison_result_injective.eq_iff]

/-- This is the comparison premise used by the existing ranked pairing-heap
observer. It does not prove that authored heap operations execute that heap. -/
theorem source_order_authorizes_rankLE (base : BasePremiseEvaluator) (left right : Rank) :
    (Step base language (compareCall left right) (result (order .lt)) ∨
     Step base language (compareCall left right) (result (order .eq))) ↔
      PlainBnfSourceRank.rankLE left right = true := by
  simp only [compare_step_iff, comparison_result_injective.eq_iff, PlainBnfSourceRank.rankLE]
  cases compareRank left right <;> decide

theorem insufficient_comparison_depth_has_no_answer (base : BasePremiseEvaluator)
    (left right : Rank) (fuel : Nat) (short : fuel ≤ compareHeight left right) :
    rewriteAt base language fuel (compareCall left right) = [] := by
  simp [compare_answers, Nat.not_lt.mpr short]

theorem source_carry_executes (base : BasePremiseEvaluator) :
    Step base language (nextCall (.two (.two .zero)))
      (result (rank (.one (.one (.one .zero))))) := by
  rw [next_step_iff]
  rfl

theorem source_compares_tails_before_digits (base : BasePremiseEvaluator) :
    Step base language (compareCall (.one (.two .zero)) (.two .zero)) (result (order .gt)) ∧
    ¬ Step base language (compareCall (.one (.two .zero)) (.two .zero)) (result (order .lt)) := by
  simp [compare_step_iff, compareRank, result, order, encode, encodeList]

theorem equal_ranks_have_one_answer_occurrence (base : BasePremiseEvaluator) (input : Rank) :
    rewriteAt base language (compareHeight input input + 1) (compareCall input input) =
      [result (order .eq)] := by
  simp [compare_answers, (PlainBnfSourceRank.compareRank_eq_iff input input).mpr rfl]

theorem missing_output_mode_refused :
    splitCall? (.list [.atom "BNFDiscoveryRankCompareV1", rank .zero, rank .zero]) = none := rfl

theorem unknown_call_refused :
    splitCall? (.list [.atom "NotARankOperation", rank .zero, rank .zero]) = none := rfl

/-- Duplicating an actual clause adds an answer occurrence. Source occurrence
preservation is therefore stronger than equality of distinct answer values. -/
theorem duplicated_source_clause_retains_two_answers (base : BasePremiseEvaluator) (fuel : Nat) :
    let duplicated := { language with rewrites := language.rewrites.take 1 ++ language.rewrites }
    rewriteAt base duplicated (fuel + 1) (nextCall .zero) =
      [result (rank (.one .zero)), result (rank (.one .zero))] := by
  dsimp
  simp [rewriteAt, rules_exact, observedRules, observed, applyRuleUsing,
    nextCall, call, result, rank, order, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

#print axioms next_answers
#print axioms compare_answers
#print axioms compare_numeric_step_iff
#print axioms source_order_authorizes_rankLE

end Mettapedia.GSLT.Parsing.PlainBnfRankSourceExecution
