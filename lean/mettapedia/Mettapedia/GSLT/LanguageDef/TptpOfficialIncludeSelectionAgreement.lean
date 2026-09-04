import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeSelectionLanguageDef
import Mettapedia.OSLF.MeTTaIL.ContextualRootDispatch

/-!
# Exact agreement for official TPTP include selection

This module connects the independent list algorithm used by include
resolution to the declared, premise-bearing selection `LanguageDef`.  The
proofs preserve the complete singleton reduct list, hence also preserve
source order, duplicate occurrences, and failure outcomes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeSelectionAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolution
open Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeSelectionLanguageDef

namespace Carrier

abbrev encodeString :=
  TptpOfficialIncludeResolutionResultCarrier.encodeString
abbrev encodeStrings :=
  TptpOfficialIncludeResolutionResultCarrier.encodeStrings
abbrev encodeOptionalString :=
  TptpOfficialIncludeResolutionResultCarrier.encodeOptionalString
abbrev encodeFormulaOrigin :=
  TptpOfficialIncludeResolutionResultCarrier.encodeFormulaOrigin
abbrev encodeResolvedFormula :=
  TptpOfficialIncludeResolutionResultCarrier.encodeResolvedFormula
abbrev encodeResolvedFormulas :=
  TptpOfficialIncludeResolutionResultCarrier.encodeResolvedFormulas
abbrev encodeFormulaSelection :=
  TptpOfficialIncludeResolutionResultCarrier.encodeFormulaSelection
abbrev encodeResolutionError :=
  TptpOfficialIncludeResolutionResultCarrier.encodeResolutionError

end Carrier

private theorem encodeResolvedFormula_eq (formula : ResolvedFormula) :
    Carrier.encodeResolvedFormula formula =
      resolvedFormula (Carrier.encodeString formula.name) formula.input
        (Carrier.encodeFormulaOrigin formula.origin) := by
  rfl

private theorem encodeResolvedFormulas_cons (formula : ResolvedFormula)
    (formulas : List ResolvedFormula) :
    Carrier.encodeResolvedFormulas (formula :: formulas) =
      formulasCons (Carrier.encodeResolvedFormula formula)
        (Carrier.encodeResolvedFormulas formulas) := by
  rfl

private theorem encodeAmbiguousSelectionError_eq (target name : String) :
    Carrier.encodeResolutionError (.ambiguousSelectionName target name) =
      errorAmbiguous (Carrier.encodeString target) (Carrier.encodeString name) := by
  rfl

private theorem encodeDuplicateSelectionError_eq (target name : String) :
    Carrier.encodeResolutionError (.duplicateSelectionName target name) =
      errorDuplicate (Carrier.encodeString target) (Carrier.encodeString name) := by
  rfl

private theorem encodeRequest_implicit_eq (target : String)
    (formulas : List ResolvedFormula) :
    encodeRequest target .implicitAll formulas =
      TptpOfficialIncludeSelectionLanguageDef.applySelection
        (Carrier.encodeString target) selectionImplicitAll
        (Carrier.encodeResolvedFormulas formulas) := by
  rfl

private theorem encodeRequest_explicit_eq (target : String)
    (formulas : List ResolvedFormula) :
    encodeRequest target .explicitAll formulas =
      TptpOfficialIncludeSelectionLanguageDef.applySelection
        (Carrier.encodeString target) selectionExplicitAll
        (Carrier.encodeResolvedFormulas formulas) := by
  rfl

private theorem encodeRequest_named_eq (target : String)
    (requested : List String) (formulas : List ResolvedFormula) :
    encodeRequest target (.named requested) formulas =
      TptpOfficialIncludeSelectionLanguageDef.applySelection
        (Carrier.encodeString target)
        (selectionNamed (Carrier.encodeStrings requested))
        (Carrier.encodeResolvedFormulas formulas) := by
  rfl

private theorem encodeStrings_nil_eq : Carrier.encodeStrings [] = stringsNil := by
  rfl

private abbrev base : BasePremiseEvaluator :=
  engineBasePremises relations

/-- Exact singleton results are stable above a finite contextual depth. -/
def EventuallyExact (source result : Pattern) : Prop :=
  ∃ requiredFuel, ∀ fuel, requiredFuel ≤ fuel →
    rewriteAt base language fuel source = [result]

private theorem eventuallyExact_of_one_step (source result : Pattern)
    (step : ∀ fuel, rewriteAt base language (fuel + 1) source = [result]) :
    EventuallyExact source result := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using step predecessor

private theorem eventuallyExact_of_one_premise
    (premiseSource premiseResult source result : Pattern)
    (premiseExact : EventuallyExact premiseSource premiseResult)
    (step : ∀ fuel,
      rewriteAt base language fuel premiseSource = [premiseResult] →
        rewriteAt base language (fuel + 1) source = [result]) :
    EventuallyExact source result := by
  rcases premiseExact with ⟨requiredFuel, premiseExact⟩
  refine ⟨requiredFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using
        step predecessor (premiseExact predecessor (by omega))

private theorem eventuallyExact_of_two_premises
    (firstSource firstResult secondSource secondResult source result : Pattern)
    (firstExact : EventuallyExact firstSource firstResult)
    (secondExact : EventuallyExact secondSource secondResult)
    (step : ∀ fuel,
      rewriteAt base language fuel firstSource = [firstResult] →
      rewriteAt base language fuel secondSource = [secondResult] →
        rewriteAt base language (fuel + 1) source = [result]) :
    EventuallyExact source result := by
  rcases firstExact with ⟨firstFuel, firstExact⟩
  rcases secondExact with ⟨secondFuel, secondExact⟩
  refine ⟨max firstFuel secondFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using step predecessor
        (firstExact predecessor (by omega))
        (secondExact predecessor (by omega))

private theorem eventuallyExact_of_three_premises
    (firstSource firstResult secondSource secondResult
      thirdSource thirdResult source result : Pattern)
    (firstExact : EventuallyExact firstSource firstResult)
    (secondExact : EventuallyExact secondSource secondResult)
    (thirdExact : EventuallyExact thirdSource thirdResult)
    (step : ∀ fuel,
      rewriteAt base language fuel firstSource = [firstResult] →
      rewriteAt base language fuel secondSource = [secondResult] →
      rewriteAt base language fuel thirdSource = [thirdResult] →
        rewriteAt base language (fuel + 1) source = [result]) :
    EventuallyExact source result := by
  rcases firstExact with ⟨firstFuel, firstExact⟩
  rcases secondExact with ⟨secondFuel, secondExact⟩
  rcases thirdExact with ⟨thirdFuel, thirdExact⟩
  refine ⟨max firstFuel (max secondFuel thirdFuel) + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using step predecessor
        (firstExact predecessor (by omega))
        (secondExact predecessor (by omega))
        (thirdExact predecessor (by omega))

private theorem encodeString_injective : Function.Injective Carrier.encodeString := by
  intro left right equalEncoding
  have decoded := congrArg
    TptpOfficialIncludeResolutionCarrier.decodeString? equalEncoding
  simpa using decoded

private theorem containsRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-selection:contains") =
      [containsRules.get ⟨0, by decide⟩,
       containsRules.get ⟨1, by decide⟩] := by
  rfl

private theorem containsDecisionRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-selection:contains-decision") =
      [containsRules.get ⟨2, by decide⟩,
       containsRules.get ⟨3, by decide⟩] := by
  rfl

private theorem firstDuplicateRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-selection:first-duplicate") =
      [duplicateRules.get ⟨0, by decide⟩,
       duplicateRules.get ⟨1, by decide⟩] := by
  rfl

private theorem firstDuplicateDecisionRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-selection:first-duplicate-decision") =
      [duplicateRules.get ⟨2, by decide⟩,
       duplicateRules.get ⟨3, by decide⟩] := by
  rfl

private theorem eraseFirstRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-selection:erase-first") =
      [eraseRules.get ⟨0, by decide⟩,
       eraseRules.get ⟨1, by decide⟩] := by
  rfl

private theorem eraseFirstDecisionRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-selection:erase-first-decision") =
      [eraseRules.get ⟨2, by decide⟩,
       eraseRules.get ⟨3, by decide⟩] := by
  rfl

private theorem scanRootRules :
    language.rewrites.filter (rootMatches "tptp-include-selection:scan") =
      [scanFinishedRule, scanMissingRule, scanConsRule] := by
  rfl

private theorem scanRequestDecisionRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-selection:scan-request-decision") =
      [scanSkipRule, scanCheckSeenRule] := by
  rfl

private theorem scanSeenDecisionRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-selection:scan-seen-decision") =
      [scanAmbiguousRule, scanSelectRule] := by
  rfl

private theorem prependRootRules :
    language.rewrites.filter (rootMatches "tptp-include-selection:prepend") =
      [prependOkRule, prependErrorRule] := by
  rfl

private theorem applySelectionRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-selection:apply") =
      [applyRules.get ⟨0, by decide⟩,
       applyRules.get ⟨1, by decide⟩,
       applyRules.get ⟨2, by decide⟩] := by
  rfl

private theorem namedDecisionRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-selection:named-decision") =
      [applyRules.get ⟨3, by decide⟩,
       applyRules.get ⟨4, by decide⟩] := by
  rfl

local macro "selection_row_simp" : tactic =>
  `(tactic|
    simp [containsRules, duplicateRules, eraseRules, scanRules, applyRules,
      scanFinishedRule, scanMissingRule, scanConsRule, scanSkipRule,
      scanCheckSeenRule, scanAmbiguousRule, scanSelectRule, prependOkRule,
      prependErrorRule, contains, containsDecision, firstDuplicate,
      firstDuplicateDecision, eraseFirst, eraseFirstDecision, prepend, scan,
      scanRequestDecision, scanSeenDecision,
      TptpOfficialIncludeSelectionLanguageDef.applySelection, namedDecision,
      stringsNil, stringsCons, noString, someString, selectionImplicitAll,
      selectionExplicitAll, selectionNamed, formulasNil, formulasCons,
      resolvedFormula, errorDuplicate, errorMissing, errorAmbiguous,
      boolFalse, boolTrue, selectionOk, selectionError, mkRule,
      congruence, typed, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings, PatternEqualityDecision.equal,
      PatternEqualityDecision.different])

local macro "scan_row_simp" : tactic =>
  `(tactic|
    simp [scanFinishedRule, scanMissingRule, scanConsRule, scanSkipRule,
      scanCheckSeenRule, scanAmbiguousRule, scanSelectRule, prependOkRule,
      prependErrorRule, contains, eraseFirst, prepend, scan,
      scanRequestDecision, scanSeenDecision, stringsNil, stringsCons,
      formulasNil, formulasCons, resolvedFormula, errorMissing,
      errorAmbiguous, boolFalse, boolTrue, selectionOk, selectionError,
      mkRule, congruence, typed, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings, PatternEqualityDecision.equal,
      PatternEqualityDecision.different])

private theorem equalityPremise_equal_exact (needle tail : Pattern) :
    base language
        [("head", needle), ("tail", tail), ("needle", needle)]
        (.relationQuery PatternEqualityDecision.relationName
          [v "needle", v "head", v "decision"]) =
      [[("decision", PatternEqualityDecision.equal),
        ("head", needle), ("tail", tail), ("needle", needle)]] := by
  simp [base, engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relations, PatternEqualityDecision.relationEnv,
    PatternEqualityDecision.relationName,
    PatternEqualityDecision.relationTuples, matchRelationArgs,
    matchRelationArgument, Bindings.lookup, mergeBindings, applyBindings, v]

private theorem equalityPremise_different_exact
    (needle head tail : Pattern) (different : needle ≠ head) :
    base language
        [("head", head), ("tail", tail), ("needle", needle)]
        (.relationQuery PatternEqualityDecision.relationName
          [v "needle", v "head", v "decision"]) =
      [[("decision", PatternEqualityDecision.different),
        ("head", head), ("tail", tail), ("needle", needle)]] := by
  simp [base, engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relations, PatternEqualityDecision.relationEnv,
    PatternEqualityDecision.relationName,
    PatternEqualityDecision.relationTuples, matchRelationArgs,
    matchRelationArgument, Bindings.lookup, mergeBindings, applyBindings, v,
    different]

theorem containsDecision_equal_rewriteAt_exact (fuel : Nat)
    (needle tail : Pattern) :
    rewriteAt base language (fuel + 1)
        (containsDecision PatternEqualityDecision.equal needle tail) =
      [boolTrue] := by
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:contains-decision"
      [PatternEqualityDecision.equal, needle, tail]) = [boolTrue]
  rw [rewriteAt_eq_root_filter, containsDecisionRootRules]
  selection_row_simp

theorem containsDecision_different_rewriteAt_exact (fuel : Nat)
    (needle tail result : Pattern)
    (recursive : rewriteAt base language fuel (contains needle tail) = [result]) :
    rewriteAt base language (fuel + 1)
        (containsDecision PatternEqualityDecision.different needle tail) =
      [result] := by
  simp only [contains, a] at recursive
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:contains-decision"
      [PatternEqualityDecision.different, needle, tail]) = [result]
  rw [rewriteAt_eq_root_filter, containsDecisionRootRules]
  selection_row_simp
  all_goals simp [recursive]

theorem contains_nil_rewriteAt_exact (fuel : Nat) (needle : Pattern) :
    rewriteAt base language (fuel + 1) (contains needle stringsNil) =
      [boolFalse] := by
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:contains"
      [needle, .apply "tptp-include-result:strings-nil" []]) = [boolFalse]
  rw [rewriteAt_eq_root_filter, containsRootRules]
  selection_row_simp

theorem contains_cons_equal_rewriteAt_exact (fuel : Nat)
    (needle tail : Pattern) :
    rewriteAt base language (fuel + 2)
        (contains needle (stringsCons needle tail)) = [boolTrue] := by
  change rewriteAt base language (fuel + 2)
    (.apply "tptp-include-selection:contains"
      [needle, .apply "tptp-include-result:strings-cons" [needle, tail]]) =
        [boolTrue]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    rewriteAt_eq_root_filter, containsRootRules]
  selection_row_simp
  have relationStep := equalityPremise_equal_exact needle tail
  simp only [v] at relationStep
  rw [relationStep]
  simp
  have decisionStep :=
    containsDecision_equal_rewriteAt_exact fuel needle tail
  simp only [base, containsDecision, a] at decisionStep
  rw [decisionStep]
  simp [boolTrue, a]

theorem contains_cons_different_rewriteAt_exact (fuel : Nat)
    (needle head tail result : Pattern) (different : needle ≠ head)
    (recursive : rewriteAt base language fuel (contains needle tail) = [result]) :
    rewriteAt base language (fuel + 2)
        (contains needle (stringsCons head tail)) = [result] := by
  simp only [contains, a] at recursive
  change rewriteAt base language (fuel + 2)
    (.apply "tptp-include-selection:contains"
      [needle, .apply "tptp-include-result:strings-cons" [head, tail]]) =
        [result]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    rewriteAt_eq_root_filter, containsRootRules]
  selection_row_simp
  have relationStep := equalityPremise_different_exact needle head tail different
  simp only [v] at relationStep
  rw [relationStep]
  simp
  have decisionStep :=
    containsDecision_different_rewriteAt_exact fuel needle tail result recursive
  simp only [base, containsDecision, a] at decisionStep
  rw [decisionStep]
  simp

theorem contains_encode_eventuallyExact (needle : String) :
    ∀ strings : List String,
      EventuallyExact
        (contains (Carrier.encodeString needle) (Carrier.encodeStrings strings))
        (if needle ∈ strings then boolTrue else boolFalse) := by
  intro strings
  induction strings with
  | nil =>
      simp only [Carrier.encodeStrings, List.not_mem_nil, ↓reduceIte]
      apply eventuallyExact_of_one_step
      intro fuel
      exact contains_nil_rewriteAt_exact fuel (Carrier.encodeString needle)
  | cons head tail inductionHypothesis =>
      by_cases equalNames : needle = head
      · subst head
        simp only [List.mem_cons, true_or, ↓reduceIte, Carrier.encodeStrings]
        refine ⟨2, ?_⟩
        intro fuel enough
        rw [show fuel = (fuel - 2) + 2 by omega]
        exact contains_cons_equal_rewriteAt_exact
          (fuel - 2) (Carrier.encodeString needle) (Carrier.encodeStrings tail)
      · have differentEncoding :
            Carrier.encodeString needle ≠ Carrier.encodeString head := by
          intro equalEncoding
          exact equalNames (encodeString_injective equalEncoding)
        simp only [List.mem_cons, equalNames, false_or, Carrier.encodeStrings]
        rcases inductionHypothesis with ⟨requiredFuel, inductionHypothesis⟩
        refine ⟨requiredFuel + 2, ?_⟩
        intro fuel enough
        obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_add_of_le
          (show requiredFuel + 2 ≤ fuel by omega)
        change rewriteAt base language (requiredFuel + 2 + predecessor)
          (contains (Carrier.encodeString needle)
            (stringsCons (Carrier.encodeString head)
              (Carrier.encodeStrings tail))) =
          [if needle ∈ tail then boolTrue else boolFalse]
        rw [show requiredFuel + 2 + predecessor =
          (requiredFuel + predecessor) + 2 by omega]
        apply contains_cons_different_rewriteAt_exact
          (requiredFuel + predecessor)
          (Carrier.encodeString needle) (Carrier.encodeString head)
          (Carrier.encodeStrings tail)
          (if needle ∈ tail then boolTrue else boolFalse)
          differentEncoding
        exact inductionHypothesis (requiredFuel + predecessor) (by omega)

theorem firstDuplicateDecision_true_rewriteAt_exact (fuel : Nat)
    (head tail : Pattern) :
    rewriteAt base language (fuel + 1)
        (firstDuplicateDecision boolTrue head tail) = [someString head] := by
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:first-duplicate-decision"
      [boolTrue, head, tail]) = [someString head]
  rw [rewriteAt_eq_root_filter, firstDuplicateDecisionRootRules]
  selection_row_simp

theorem firstDuplicateDecision_false_rewriteAt_exact (fuel : Nat)
    (head tail result : Pattern)
    (recursive :
      rewriteAt base language fuel (firstDuplicate tail) = [result]) :
    rewriteAt base language (fuel + 1)
        (firstDuplicateDecision boolFalse head tail) = [result] := by
  simp only [firstDuplicate, a] at recursive
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:first-duplicate-decision"
      [boolFalse, head, tail]) = [result]
  rw [rewriteAt_eq_root_filter, firstDuplicateDecisionRootRules]
  selection_row_simp
  all_goals simp [recursive]

theorem firstDuplicate_nil_rewriteAt_exact (fuel : Nat) :
    rewriteAt base language (fuel + 1) (firstDuplicate stringsNil) =
      [noString] := by
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:first-duplicate"
      [.apply "tptp-include-result:strings-nil" []]) = [noString]
  rw [rewriteAt_eq_root_filter, firstDuplicateRootRules]
  selection_row_simp

theorem firstDuplicate_cons_rewriteAt_exact (fuel : Nat)
    (head tail membership result : Pattern)
    (containsStep :
      rewriteAt base language fuel (contains head tail) = [membership])
    (decisionStep :
      rewriteAt base language fuel
        (firstDuplicateDecision membership head tail) = [result]) :
    rewriteAt base language (fuel + 1)
        (firstDuplicate (stringsCons head tail)) = [result] := by
  simp only [contains, firstDuplicateDecision, a] at containsStep decisionStep
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:first-duplicate"
      [.apply "tptp-include-result:strings-cons" [head, tail]]) = [result]
  rw [rewriteAt_eq_root_filter, firstDuplicateRootRules]
  selection_row_simp
  all_goals simp [containsStep, decisionStep]

theorem firstDuplicate_encode_eventuallyExact :
    ∀ strings : List String,
      EventuallyExact (firstDuplicate (Carrier.encodeStrings strings))
        (Carrier.encodeOptionalString (firstDuplicate? strings)) := by
  intro strings
  induction strings with
  | nil =>
      simp only [Carrier.encodeStrings, firstDuplicate?,
        Carrier.encodeOptionalString]
      apply eventuallyExact_of_one_step
      intro fuel
      exact firstDuplicate_nil_rewriteAt_exact fuel
  | cons head tail inductionHypothesis =>
      by_cases membership : head ∈ tail
      · simp only [firstDuplicate?, membership, ↓reduceIte,
          Carrier.encodeStrings, Carrier.encodeOptionalString]
        have containsExact := contains_encode_eventuallyExact head tail
        simp only [membership, ↓reduceIte] at containsExact
        have decisionExact : EventuallyExact
            (firstDuplicateDecision boolTrue (Carrier.encodeString head)
              (Carrier.encodeStrings tail))
            (someString (Carrier.encodeString head)) := by
          apply eventuallyExact_of_one_step
          intro fuel
          exact firstDuplicateDecision_true_rewriteAt_exact fuel
            (Carrier.encodeString head) (Carrier.encodeStrings tail)
        apply eventuallyExact_of_two_premises
          (contains (Carrier.encodeString head) (Carrier.encodeStrings tail))
          boolTrue
          (firstDuplicateDecision boolTrue (Carrier.encodeString head)
            (Carrier.encodeStrings tail))
          (someString (Carrier.encodeString head))
          (firstDuplicate (stringsCons (Carrier.encodeString head)
            (Carrier.encodeStrings tail)))
          (someString (Carrier.encodeString head))
          containsExact decisionExact
        intro fuel containsStep decisionStep
        exact firstDuplicate_cons_rewriteAt_exact fuel
          (Carrier.encodeString head) (Carrier.encodeStrings tail)
          boolTrue (someString (Carrier.encodeString head))
          containsStep decisionStep
      · simp only [firstDuplicate?, membership, ↓reduceIte,
          Carrier.encodeStrings]
        have containsExact := contains_encode_eventuallyExact head tail
        simp only [membership, ↓reduceIte] at containsExact
        have decisionExact : EventuallyExact
            (firstDuplicateDecision boolFalse (Carrier.encodeString head)
              (Carrier.encodeStrings tail))
            (Carrier.encodeOptionalString (firstDuplicate? tail)) := by
          apply eventuallyExact_of_one_premise
            (firstDuplicate (Carrier.encodeStrings tail))
            (Carrier.encodeOptionalString (firstDuplicate? tail))
            (firstDuplicateDecision boolFalse (Carrier.encodeString head)
              (Carrier.encodeStrings tail))
            (Carrier.encodeOptionalString (firstDuplicate? tail))
            inductionHypothesis
          intro fuel recursive
          exact firstDuplicateDecision_false_rewriteAt_exact fuel
            (Carrier.encodeString head) (Carrier.encodeStrings tail)
            (Carrier.encodeOptionalString (firstDuplicate? tail)) recursive
        apply eventuallyExact_of_two_premises
          (contains (Carrier.encodeString head) (Carrier.encodeStrings tail))
          boolFalse
          (firstDuplicateDecision boolFalse (Carrier.encodeString head)
            (Carrier.encodeStrings tail))
          (Carrier.encodeOptionalString (firstDuplicate? tail))
          (firstDuplicate (stringsCons (Carrier.encodeString head)
            (Carrier.encodeStrings tail)))
          (Carrier.encodeOptionalString (firstDuplicate? tail))
          containsExact decisionExact
        intro fuel containsStep decisionStep
        exact firstDuplicate_cons_rewriteAt_exact fuel
          (Carrier.encodeString head) (Carrier.encodeStrings tail)
          boolFalse (Carrier.encodeOptionalString (firstDuplicate? tail))
          containsStep decisionStep

theorem eraseFirstDecision_equal_rewriteAt_exact (fuel : Nat)
    (needle head tail : Pattern) :
    rewriteAt base language (fuel + 1)
        (eraseFirstDecision PatternEqualityDecision.equal needle head tail) =
      [tail] := by
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:erase-first-decision"
      [PatternEqualityDecision.equal, needle, head, tail]) = [tail]
  rw [rewriteAt_eq_root_filter, eraseFirstDecisionRootRules]
  selection_row_simp

theorem eraseFirstDecision_different_rewriteAt_exact (fuel : Nat)
    (needle head tail erased : Pattern)
    (recursive : rewriteAt base language fuel (eraseFirst needle tail) = [erased]) :
    rewriteAt base language (fuel + 1)
        (eraseFirstDecision PatternEqualityDecision.different
          needle head tail) = [stringsCons head erased] := by
  simp only [eraseFirst, a] at recursive
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:erase-first-decision"
      [PatternEqualityDecision.different, needle, head, tail]) =
      [.apply "tptp-include-result:strings-cons" [head, erased]]
  rw [rewriteAt_eq_root_filter, eraseFirstDecisionRootRules]
  selection_row_simp
  all_goals simp [recursive]

theorem eraseFirst_nil_rewriteAt_exact (fuel : Nat) (needle : Pattern) :
    rewriteAt base language (fuel + 1) (eraseFirst needle stringsNil) =
      [stringsNil] := by
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:erase-first"
      [needle, .apply "tptp-include-result:strings-nil" []]) =
      [.apply "tptp-include-result:strings-nil" []]
  rw [rewriteAt_eq_root_filter, eraseFirstRootRules]
  selection_row_simp

theorem eraseFirst_cons_equal_rewriteAt_exact (fuel : Nat)
    (needle tail : Pattern) :
    rewriteAt base language (fuel + 2)
        (eraseFirst needle (stringsCons needle tail)) = [tail] := by
  change rewriteAt base language (fuel + 2)
    (.apply "tptp-include-selection:erase-first"
      [needle, .apply "tptp-include-result:strings-cons" [needle, tail]]) =
      [tail]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    rewriteAt_eq_root_filter, eraseFirstRootRules]
  selection_row_simp
  have relationStep := equalityPremise_equal_exact needle tail
  simp only [v] at relationStep
  rw [relationStep]
  simp
  have decisionStep :=
    eraseFirstDecision_equal_rewriteAt_exact fuel needle needle tail
  simp only [base, eraseFirstDecision, a] at decisionStep
  rw [decisionStep]
  simp

theorem eraseFirst_cons_different_rewriteAt_exact (fuel : Nat)
    (needle head tail erased : Pattern) (different : needle ≠ head)
    (recursive : rewriteAt base language fuel (eraseFirst needle tail) = [erased]) :
    rewriteAt base language (fuel + 2)
        (eraseFirst needle (stringsCons head tail)) =
      [stringsCons head erased] := by
  simp only [eraseFirst, a] at recursive
  change rewriteAt base language (fuel + 2)
    (.apply "tptp-include-selection:erase-first"
      [needle, .apply "tptp-include-result:strings-cons" [head, tail]]) =
      [.apply "tptp-include-result:strings-cons" [head, erased]]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    rewriteAt_eq_root_filter, eraseFirstRootRules]
  selection_row_simp
  have relationStep := equalityPremise_different_exact needle head tail different
  simp only [v] at relationStep
  rw [relationStep]
  simp
  have decisionStep := eraseFirstDecision_different_rewriteAt_exact fuel
    needle head tail erased recursive
  simp only [base, eraseFirstDecision, stringsCons, a] at decisionStep
  rw [decisionStep]
  simp

theorem eraseFirst_encode_eventuallyExact (needle : String) :
    ∀ strings : List String,
      EventuallyExact
        (eraseFirst (Carrier.encodeString needle) (Carrier.encodeStrings strings))
        (Carrier.encodeStrings (strings.erase needle)) := by
  intro strings
  induction strings with
  | nil =>
      simp only [Carrier.encodeStrings, List.erase_nil]
      apply eventuallyExact_of_one_step
      intro fuel
      exact eraseFirst_nil_rewriteAt_exact fuel (Carrier.encodeString needle)
  | cons head tail inductionHypothesis =>
      by_cases equalNames : needle = head
      · subst head
        simp only [List.erase_cons_head, Carrier.encodeStrings]
        refine ⟨2, ?_⟩
        intro fuel enough
        rw [show fuel = (fuel - 2) + 2 by omega]
        exact eraseFirst_cons_equal_rewriteAt_exact
          (fuel - 2) (Carrier.encodeString needle) (Carrier.encodeStrings tail)
      · have differentEncoding :
            Carrier.encodeString needle ≠ Carrier.encodeString head := by
          intro equalEncoding
          exact equalNames (encodeString_injective equalEncoding)
        rw [List.erase_cons_tail (not_beq_of_ne (Ne.symm equalNames))]
        simp only [Carrier.encodeStrings]
        rcases inductionHypothesis with ⟨requiredFuel, inductionHypothesis⟩
        refine ⟨requiredFuel + 2, ?_⟩
        intro fuel enough
        obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_add_of_le
          (show requiredFuel + 2 ≤ fuel by omega)
        change rewriteAt base language (requiredFuel + 2 + predecessor)
          (eraseFirst (Carrier.encodeString needle)
            (stringsCons (Carrier.encodeString head)
              (Carrier.encodeStrings tail))) =
          [stringsCons (Carrier.encodeString head)
            (Carrier.encodeStrings (tail.erase needle))]
        rw [show requiredFuel + 2 + predecessor =
          (requiredFuel + predecessor) + 2 by omega]
        apply eraseFirst_cons_different_rewriteAt_exact
          (requiredFuel + predecessor)
          (Carrier.encodeString needle) (Carrier.encodeString head)
          (Carrier.encodeStrings tail) (Carrier.encodeStrings (tail.erase needle))
          differentEncoding
        exact inductionHypothesis (requiredFuel + predecessor) (by omega)

private theorem scanFinishedRule_no_apply_cons
    (recursive : Pattern → List Pattern)
    (target requested remaining seen formula formulas : Pattern) :
    applyRuleUsing base language recursive scanFinishedRule
        (scan target requested remaining seen (formulasCons formula formulas)) =
      [] := by
  simp [scanFinishedRule, scan, formulasNil, formulasCons, selectionOk,
    mkRule, typed, a, v, applyRuleUsing, matchPatternForRule_eq_syntactic,
    matchPattern, matchArgs, mergeBindings]

private theorem scanMissingRule_no_apply_cons
    (recursive : Pattern → List Pattern)
    (target requested remaining seen formula formulas : Pattern) :
    applyRuleUsing base language recursive scanMissingRule
        (scan target requested remaining seen (formulasCons formula formulas)) =
      [] := by
  simp [scanMissingRule, scan, formulasNil, formulasCons, errorMissing,
    selectionError, stringsCons, mkRule, typed, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, matchPattern, matchArgs, mergeBindings]

private theorem scanSkipRule_no_apply_true
    (recursive : Pattern → List Pattern)
    (target requested remaining seen formula formulas : Pattern) :
    applyRuleUsing base language recursive scanSkipRule
        (scanRequestDecision boolTrue target requested remaining seen
          formula formulas) = [] := by
  simp [scanSkipRule, scanRequestDecision, boolFalse, boolTrue, scan,
    mkRule, congruence, typed, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, matchPattern, matchArgs, mergeBindings]

private theorem scanCheckSeenRule_no_apply_false
    (recursive : Pattern → List Pattern)
    (target requested remaining seen formula formulas : Pattern) :
    applyRuleUsing base language recursive scanCheckSeenRule
        (scanRequestDecision boolFalse target requested remaining seen
          formula formulas) = [] := by
  simp [scanCheckSeenRule, scanRequestDecision, boolFalse, boolTrue,
    contains, scanSeenDecision, resolvedFormula, mkRule, congruence, typed,
    a, v, applyRuleUsing, matchPatternForRule_eq_syntactic, matchPattern,
    matchArgs, mergeBindings]

private theorem scanAmbiguousRule_no_apply_false
    (recursive : Pattern → List Pattern)
    (target requested remaining seen formula formulas : Pattern) :
    applyRuleUsing base language recursive scanAmbiguousRule
        (scanSeenDecision boolFalse target requested remaining seen
          formula formulas) = [] := by
  simp [scanAmbiguousRule, scanSeenDecision, boolFalse, boolTrue,
    resolvedFormula, errorAmbiguous, selectionError, mkRule, typed, a, v,
    applyRuleUsing, matchPatternForRule_eq_syntactic, matchPattern, matchArgs,
    mergeBindings]

private theorem scanSelectRule_no_apply_true
    (recursive : Pattern → List Pattern)
    (target requested remaining seen formula formulas : Pattern) :
    applyRuleUsing base language recursive scanSelectRule
        (scanSeenDecision boolTrue target requested remaining seen
          formula formulas) = [] := by
  simp [scanSelectRule, scanSeenDecision, boolFalse, boolTrue, eraseFirst,
    scan, stringsCons, prepend, resolvedFormula, mkRule, congruence, typed,
    a, v, applyRuleUsing, matchPatternForRule_eq_syntactic, matchPattern,
    matchArgs, mergeBindings]

/-- The three scan rows share one linear left-hand-side binding layout.  Keeping
this exact matcher result named prevents each row proof from normalizing the
same eight-field match tree again. -/
private def scanBindings
    (target requested remaining seen name input origin formulas : Pattern) :
    Bindings :=
  [("target", target), ("remaining", remaining), ("name", name),
    ("origin", origin), ("input", input), ("formulas", formulas),
    ("seen", seen), ("requested", requested)]

private def formulaBindings (name input origin : Pattern) : Bindings :=
  [("input", input), ("origin", origin), ("name", name)]

private def formulaTailBindings
    (name input origin formulas : Pattern) : Bindings :=
  [("formulas", formulas), ("input", input), ("origin", origin),
    ("name", name)]

private def seenTailBindings
    (seen name input origin formulas : Pattern) : Bindings :=
  [("name", name), ("origin", origin), ("input", input),
    ("formulas", formulas), ("seen", seen)]

private def remainingTailBindings
    (remaining seen name input origin formulas : Pattern) : Bindings :=
  [("seen", seen), ("formulas", formulas), ("input", input),
    ("origin", origin), ("name", name), ("remaining", remaining)]

private def requestedTailBindings
    (requested remaining seen name input origin formulas : Pattern) : Bindings :=
  [("remaining", remaining), ("name", name), ("origin", origin),
    ("input", input), ("formulas", formulas), ("seen", seen),
    ("requested", requested)]

private def targetTailBindings
    (target requested remaining seen name input origin formulas : Pattern) :
    Bindings :=
  [("requested", requested), ("seen", seen), ("formulas", formulas),
    ("input", input), ("origin", origin), ("name", name),
    ("remaining", remaining), ("target", target)]

private theorem resolvedFormula_match_exact (name input origin : Pattern) :
    matchPattern
        (resolvedFormula (v "name") (v "input") (v "origin"))
        (resolvedFormula name input origin) =
      [formulaBindings name input origin] := by
  simp [formulaBindings, resolvedFormula, a, v, matchPattern, matchArgs,
    mergeBindings]

private theorem matchArgs_cons_singleton
    (pattern term : Pattern) (patterns terms : List Pattern)
    (headBindings tailBindings merged : Bindings)
    (headExact : matchPattern pattern term = [headBindings])
    (tailExact : matchArgs patterns terms = [tailBindings])
    (mergeExact : mergeBindings headBindings tailBindings = some merged) :
    matchArgs (pattern :: patterns) (term :: terms) = [merged] := by
  simp [matchArgs, headExact, tailExact, mergeExact]

private theorem scanShape_match_exact (root decision : String)
    (target requested remaining seen name input origin formulas : Pattern) :
    matchPattern
        (a root
          [a decision, v "target", v "requested", v "remaining", v "seen",
            resolvedFormula (v "name") (v "input") (v "origin"),
            v "formulas"])
        (a root
          [a decision, target, requested, remaining, seen,
            resolvedFormula name input origin, formulas]) =
      [scanBindings target requested remaining seen name input origin formulas] := by
  simp only [a, resolvedFormula, v]
  rw [matchPattern]
  rw [if_pos (by simp)]
  apply matchArgs_cons_singleton (a decision) (a decision) _ _ []
    (targetTailBindings target requested remaining seen name input origin
      formulas)
  · simp [a, matchPattern, matchArgs]
  · apply matchArgs_cons_singleton (v "target") target _ _
      [("target", target)]
      (requestedTailBindings requested remaining seen name input origin formulas)
    · simp [v, matchPattern]
    · apply matchArgs_cons_singleton (v "requested") requested _ _
        [("requested", requested)]
        (remainingTailBindings remaining seen name input origin formulas)
      · simp [v, matchPattern]
      · apply matchArgs_cons_singleton (v "remaining") remaining _ _
          [("remaining", remaining)]
          (seenTailBindings seen name input origin formulas)
        · simp [v, matchPattern]
        · apply matchArgs_cons_singleton (v "seen") seen _ _ [("seen", seen)]
            (formulaTailBindings name input origin formulas)
          · simp [v, matchPattern]
          · apply matchArgs_cons_singleton
              (resolvedFormula (v "name") (v "input") (v "origin"))
              (resolvedFormula name input origin) _ _
              (formulaBindings name input origin) [("formulas", formulas)]
            · exact resolvedFormula_match_exact name input origin
            · simp [matchPattern, matchArgs, mergeBindings]
            · simp [formulaBindings, formulaTailBindings, mergeBindings]
          · simp [formulaTailBindings, seenTailBindings, mergeBindings]
        · simp [seenTailBindings, remainingTailBindings, mergeBindings]
      · simp [remainingTailBindings, requestedTailBindings, mergeBindings]
    · simp [requestedTailBindings, targetTailBindings, mergeBindings]
  · simp [targetTailBindings, scanBindings, mergeBindings]

private theorem scanRequestTrue_match_exact
    (target requested remaining seen name input origin formulas : Pattern) :
    matchPattern
        (scanRequestDecision boolTrue (v "target") (v "requested")
          (v "remaining") (v "seen")
          (resolvedFormula (v "name") (v "input") (v "origin"))
          (v "formulas"))
        (scanRequestDecision boolTrue target requested remaining seen
          (resolvedFormula name input origin) formulas) =
      [scanBindings target requested remaining seen name input origin formulas] := by
  simpa [scanRequestDecision, boolTrue] using
    scanShape_match_exact "tptp-include-selection:scan-request-decision"
      "tptp-include-selection:true" target requested remaining seen name input
      origin formulas

private theorem scanSeenTrue_match_exact
    (target requested remaining seen name input origin formulas : Pattern) :
    matchPattern
        (scanSeenDecision boolTrue (v "target") (v "requested")
          (v "remaining") (v "seen")
          (resolvedFormula (v "name") (v "input") (v "origin"))
          (v "formulas"))
        (scanSeenDecision boolTrue target requested remaining seen
          (resolvedFormula name input origin) formulas) =
      [scanBindings target requested remaining seen name input origin formulas] := by
  simpa [scanSeenDecision, boolTrue] using
    scanShape_match_exact "tptp-include-selection:scan-seen-decision"
      "tptp-include-selection:true" target requested remaining seen name input
      origin formulas

private theorem scanSeenFalse_match_exact
    (target requested remaining seen name input origin formulas : Pattern) :
    matchPattern
        (scanSeenDecision boolFalse (v "target") (v "requested")
          (v "remaining") (v "seen")
          (resolvedFormula (v "name") (v "input") (v "origin"))
          (v "formulas"))
        (scanSeenDecision boolFalse target requested remaining seen
          (resolvedFormula name input origin) formulas) =
      [scanBindings target requested remaining seen name input origin formulas] := by
  simpa [scanSeenDecision, boolFalse] using
    scanShape_match_exact "tptp-include-selection:scan-seen-decision"
      "tptp-include-selection:false" target requested remaining seen name input
      origin formulas

theorem scan_finished_rewriteAt_exact (fuel : Nat)
    (target requested seen : Pattern) :
    rewriteAt base language (fuel + 1)
        (scan target requested stringsNil seen formulasNil) =
      [selectionOk formulasNil] := by
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:scan"
      [target, requested, stringsNil, seen, formulasNil]) =
      [selectionOk formulasNil]
  rw [rewriteAt_eq_root_filter, scanRootRules]
  scan_row_simp

theorem scan_missing_rewriteAt_exact (fuel : Nat)
    (target requested missing remaining seen : Pattern) :
    rewriteAt base language (fuel + 1)
        (scan target requested (stringsCons missing remaining) seen formulasNil) =
      [selectionError (errorMissing target missing)] := by
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:scan"
      [target, requested, stringsCons missing remaining, seen, formulasNil]) =
      [selectionError (errorMissing target missing)]
  rw [rewriteAt_eq_root_filter, scanRootRules]
  scan_row_simp

theorem scan_cons_rewriteAt_exact (fuel : Nat)
    (target requested remaining seen name input origin formulas membership
      result : Pattern)
    (containsStep : rewriteAt base language fuel
      (contains name requested) = [membership])
    (decisionStep : rewriteAt base language fuel
      (scanRequestDecision membership target requested remaining seen
        (resolvedFormula name input origin) formulas) = [result]) :
    rewriteAt base language (fuel + 1)
        (scan target requested remaining seen
          (formulasCons (resolvedFormula name input origin) formulas)) =
      [result] := by
  simp only [contains, scanRequestDecision, resolvedFormula, a]
    at containsStep decisionStep
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:scan"
      [target, requested, remaining, seen,
        .apply "tptp-include-result:resolved-formulas-cons"
          [.apply "tptp-include-result:resolved-formula" [name, input, origin],
            formulas]]) = [result]
  rw [rewriteAt_eq_root_filter, scanRootRules]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have finishedCannotApply := scanFinishedRule_no_apply_cons
    (rewriteAt base language fuel) target requested remaining seen
      (resolvedFormula name input origin) formulas
  have missingCannotApply := scanMissingRule_no_apply_cons
    (rewriteAt base language fuel) target requested remaining seen
      (resolvedFormula name input origin) formulas
  simp only [scan, formulasCons, resolvedFormula, a]
    at finishedCannotApply missingCannotApply
  rw [finishedCannotApply, missingCannotApply]
  scan_row_simp
  all_goals simp [containsStep, decisionStep]

theorem scanRequest_false_rewriteAt_exact (fuel : Nat)
    (target requested remaining seen formula formulas result : Pattern)
    (recursive : rewriteAt base language fuel
      (scan target requested remaining seen formulas) = [result]) :
    rewriteAt base language (fuel + 1)
        (scanRequestDecision boolFalse target requested remaining seen
          formula formulas) = [result] := by
  simp only [scan, a] at recursive
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:scan-request-decision"
      [boolFalse, target, requested, remaining, seen, formula, formulas]) =
      [result]
  rw [rewriteAt_eq_root_filter, scanRequestDecisionRootRules]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have checkSeenCannotApply := scanCheckSeenRule_no_apply_false
    (rewriteAt base language fuel) target requested remaining seen formula formulas
  simp only [scanRequestDecision, a] at checkSeenCannotApply
  rw [checkSeenCannotApply]
  scan_row_simp
  all_goals simp [recursive]

theorem scanRequest_true_rewriteAt_exact (fuel : Nat)
    (target requested remaining seen name input origin formulas membership
      result : Pattern)
    (containsStep : rewriteAt base language fuel
      (contains name seen) = [membership])
    (decisionStep : rewriteAt base language fuel
      (scanSeenDecision membership target requested remaining seen
        (resolvedFormula name input origin) formulas) = [result]) :
    rewriteAt base language (fuel + 1)
        (scanRequestDecision boolTrue target requested remaining seen
          (resolvedFormula name input origin) formulas) = [result] := by
  simp only [contains, scanSeenDecision, resolvedFormula, a]
    at containsStep decisionStep
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:scan-request-decision"
      [boolTrue, target, requested, remaining, seen,
        .apply "tptp-include-result:resolved-formula" [name, input, origin],
        formulas]) = [result]
  rw [rewriteAt_eq_root_filter, scanRequestDecisionRootRules]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have skipCannotApply := scanSkipRule_no_apply_true
    (rewriteAt base language fuel) target requested remaining seen
      (resolvedFormula name input origin) formulas
  simp only [scanRequestDecision, resolvedFormula, a]
    at skipCannotApply
  rw [skipCannotApply]
  simp only [scanCheckSeenRule, mkRule, typed, applyRuleUsing,
    matchPatternForRule_eq_syntactic]
  have initialMatch := scanRequestTrue_match_exact target requested remaining seen
    name input origin formulas
  simp only [scanRequestDecision, resolvedFormula, a] at initialMatch
  simp only [scanRequestDecision, resolvedFormula, a]
  rw [initialMatch]
  simp [scanBindings, premisesUsing, premiseStepUsing, contains, a, v,
    scanSeenDecision, congruence, applyBindingsForRule, applyBindings,
    matchPattern, containsStep, decisionStep, mergeBindings]

theorem scanSeen_true_rewriteAt_exact (fuel : Nat)
    (target requested remaining seen name input origin formulas : Pattern) :
    rewriteAt base language (fuel + 1)
        (scanSeenDecision boolTrue target requested remaining seen
          (resolvedFormula name input origin) formulas) =
      [selectionError (errorAmbiguous target name)] := by
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:scan-seen-decision"
      [boolTrue, target, requested, remaining, seen,
        .apply "tptp-include-result:resolved-formula" [name, input, origin],
        formulas]) = [selectionError (errorAmbiguous target name)]
  rw [rewriteAt_eq_root_filter, scanSeenDecisionRootRules]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have selectCannotApply := scanSelectRule_no_apply_true
    (rewriteAt base language fuel) target requested remaining seen
      (resolvedFormula name input origin) formulas
  simp only [scanSeenDecision, resolvedFormula, a]
    at selectCannotApply
  rw [selectCannotApply]
  simp only [scanAmbiguousRule, mkRule, typed, applyRuleUsing,
    matchPatternForRule_eq_syntactic]
  have initialMatch := scanSeenTrue_match_exact target requested remaining seen
    name input origin formulas
  simp only [scanSeenDecision, resolvedFormula, a] at initialMatch
  simp only [scanSeenDecision, resolvedFormula, a]
  rw [initialMatch]
  simp [scanBindings, premisesUsing, errorAmbiguous, selectionError,
    a, v, applyBindingsForRule, applyBindings]

theorem scanSeen_false_rewriteAt_exact (fuel : Nat)
    (target requested remaining seen name input origin formulas erased rest
      result : Pattern)
    (eraseStep : rewriteAt base language fuel
      (eraseFirst name remaining) = [erased])
    (scanStep : rewriteAt base language fuel
      (scan target requested erased (stringsCons name seen) formulas) = [rest])
    (prependStep : rewriteAt base language fuel
      (prepend (resolvedFormula name input origin) rest) = [result]) :
    rewriteAt base language (fuel + 1)
        (scanSeenDecision boolFalse target requested remaining seen
          (resolvedFormula name input origin) formulas) = [result] := by
  simp only [eraseFirst, scan, prepend, resolvedFormula, stringsCons, a]
    at eraseStep scanStep prependStep
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:scan-seen-decision"
      [boolFalse, target, requested, remaining, seen,
        .apply "tptp-include-result:resolved-formula" [name, input, origin],
        formulas]) = [result]
  rw [rewriteAt_eq_root_filter, scanSeenDecisionRootRules]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have ambiguousCannotApply := scanAmbiguousRule_no_apply_false
    (rewriteAt base language fuel) target requested remaining seen
      (resolvedFormula name input origin) formulas
  simp only [scanSeenDecision, resolvedFormula, a]
    at ambiguousCannotApply
  rw [ambiguousCannotApply]
  simp only [scanSelectRule, mkRule, typed, applyRuleUsing,
    matchPatternForRule_eq_syntactic]
  have initialMatch := scanSeenFalse_match_exact target requested remaining seen
    name input origin formulas
  simp only [scanSeenDecision, resolvedFormula, a] at initialMatch
  simp only [scanSeenDecision, resolvedFormula, a]
  rw [initialMatch]
  simp [scanBindings, premisesUsing, premiseStepUsing, eraseFirst, scan,
    stringsCons, prepend, a, v, congruence,
    applyBindingsForRule, applyBindings, matchPattern, eraseStep, scanStep,
    prependStep, mergeBindings]

theorem prepend_ok_rewriteAt_exact (fuel : Nat)
    (formula formulas : Pattern) :
    rewriteAt base language (fuel + 1)
        (prepend formula (selectionOk formulas)) =
      [selectionOk (formulasCons formula formulas)] := by
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:prepend"
      [formula, selectionOk formulas]) =
      [selectionOk (formulasCons formula formulas)]
  rw [rewriteAt_eq_root_filter, prependRootRules]
  scan_row_simp

theorem prepend_error_rewriteAt_exact (fuel : Nat)
    (formula failure : Pattern) :
    rewriteAt base language (fuel + 1)
        (prepend formula (selectionError failure)) =
      [selectionError failure] := by
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-selection:prepend"
      [formula, selectionError failure]) = [selectionError failure]
  rw [rewriteAt_eq_root_filter, prependRootRules]
  scan_row_simp

theorem prepend_encode_eventuallyExact (formula : ResolvedFormula) :
    ∀ outcome : Except ResolutionError (List ResolvedFormula),
      EventuallyExact
        (prepend (Carrier.encodeResolvedFormula formula) (encodeOutcome outcome))
        (encodeOutcome (outcome.map (formula :: ·))) := by
  intro outcome
  cases outcome with
  | error failure =>
      simp only [encodeOutcome, Except.map]
      apply eventuallyExact_of_one_step
      intro fuel
      exact prepend_error_rewriteAt_exact fuel
        (Carrier.encodeResolvedFormula formula)
        (Carrier.encodeResolutionError failure)
  | ok formulas =>
      simp only [encodeOutcome, Except.map]
      apply eventuallyExact_of_one_step
      intro fuel
      exact prepend_ok_rewriteAt_exact fuel
        (Carrier.encodeResolvedFormula formula)
        (Carrier.encodeResolvedFormulas formulas)

theorem apply_implicit_all_rewriteAt_exact (fuel : Nat)
    (target formulas : Pattern) :
    rewriteAt base language (fuel + 1)
        (TptpOfficialIncludeSelectionLanguageDef.applySelection
          target selectionImplicitAll formulas) =
      [selectionOk formulas] := by
  simp only [TptpOfficialIncludeSelectionLanguageDef.applySelection,
    selectionImplicitAll, a]
  rw [rewriteAt_eq_root_filter, applySelectionRootRules]
  selection_row_simp

theorem apply_explicit_all_rewriteAt_exact (fuel : Nat)
    (target formulas : Pattern) :
    rewriteAt base language (fuel + 1)
        (TptpOfficialIncludeSelectionLanguageDef.applySelection
          target selectionExplicitAll formulas) =
      [selectionOk formulas] := by
  simp only [TptpOfficialIncludeSelectionLanguageDef.applySelection,
    selectionExplicitAll, a]
  rw [rewriteAt_eq_root_filter, applySelectionRootRules]
  selection_row_simp

theorem named_duplicate_rewriteAt_exact (fuel : Nat)
    (target requested formulas duplicate : Pattern) :
    rewriteAt base language (fuel + 1)
        (namedDecision (someString duplicate) target requested formulas) =
      [selectionError (errorDuplicate target duplicate)] := by
  simp only [namedDecision, someString, a]
  rw [rewriteAt_eq_root_filter, namedDecisionRootRules]
  selection_row_simp

theorem named_scan_rewriteAt_exact (fuel : Nat)
    (target requested formulas result : Pattern)
    (scanStep : rewriteAt base language fuel
      (scan target requested requested stringsNil formulas) = [result]) :
    rewriteAt base language (fuel + 1)
        (namedDecision noString target requested formulas) = [result] := by
  simp only [scan, stringsNil, a] at scanStep
  simp only [namedDecision, noString, a]
  rw [rewriteAt_eq_root_filter, namedDecisionRootRules]
  selection_row_simp
  refine ⟨[("result", result), ("target", target), ("formulas", formulas),
    ("requested", requested)], ?_, ?_⟩
  · simp [scanStep]
  · simp

theorem apply_named_rewriteAt_exact (fuel : Nat)
    (target requested formulas duplicate result : Pattern)
    (duplicateStep : rewriteAt base language fuel
      (firstDuplicate requested) = [duplicate])
    (decisionStep : rewriteAt base language fuel
      (namedDecision duplicate target requested formulas) = [result]) :
    rewriteAt base language (fuel + 1)
        (TptpOfficialIncludeSelectionLanguageDef.applySelection target
          (selectionNamed requested) formulas) = [result] := by
  simp only [firstDuplicate, namedDecision, a] at duplicateStep decisionStep
  simp only [TptpOfficialIncludeSelectionLanguageDef.applySelection,
    selectionNamed, a]
  rw [rewriteAt_eq_root_filter, applySelectionRootRules]
  selection_row_simp
  all_goals simp [duplicateStep, decisionStep]

/-- The declared scan is extensionally exact for the independent host
selection algorithm, for arbitrary formula lists and accumulator states. -/
theorem selectNamed_encode_eventuallyExact
    (target : String) (requested remaining seen : List String) :
    ∀ formulas : List ResolvedFormula,
      EventuallyExact
        (scan (Carrier.encodeString target) (Carrier.encodeStrings requested)
          (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
          (Carrier.encodeResolvedFormulas formulas))
        (encodeOutcome (selectNamed target requested remaining seen formulas)) := by
  intro formulas
  induction formulas generalizing remaining seen with
  | nil =>
      cases remaining with
      | nil =>
          simp only [selectNamed, Carrier.encodeStrings,
            Carrier.encodeResolvedFormulas, encodeOutcome]
          apply eventuallyExact_of_one_step
          intro fuel
          exact scan_finished_rewriteAt_exact fuel
            (Carrier.encodeString target) (Carrier.encodeStrings requested)
            (Carrier.encodeStrings seen)
      | cons missing remaining =>
          simp only [selectNamed, Carrier.encodeStrings,
            Carrier.encodeResolvedFormulas, encodeOutcome]
          apply eventuallyExact_of_one_step
          intro fuel
          exact scan_missing_rewriteAt_exact fuel
            (Carrier.encodeString target) (Carrier.encodeStrings requested)
            (Carrier.encodeString missing) (Carrier.encodeStrings remaining)
            (Carrier.encodeStrings seen)
  | cons formula formulas inductionHypothesis =>
      by_cases requestedMember : formula.name ∈ requested
      · have requestedExact :=
          contains_encode_eventuallyExact formula.name requested
        simp only [requestedMember, ↓reduceIte] at requestedExact
        by_cases seenMember : formula.name ∈ seen
        · have seenExact := contains_encode_eventuallyExact formula.name seen
          simp only [seenMember, ↓reduceIte] at seenExact
          have ambiguousExact : EventuallyExact
              (scanSeenDecision boolTrue (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeResolvedFormula formula)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (.error
                (.ambiguousSelectionName target formula.name))) := by
            apply eventuallyExact_of_one_step
            intro fuel
            simpa [encodeResolvedFormula_eq, encodeOutcome,
              encodeAmbiguousSelectionError_eq] using
              scanSeen_true_rewriteAt_exact fuel
                (Carrier.encodeString target) (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeString formula.name) formula.input
                (Carrier.encodeFormulaOrigin formula.origin)
                (Carrier.encodeResolvedFormulas formulas)
          have requestExact : EventuallyExact
              (scanRequestDecision boolTrue (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeResolvedFormula formula)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (.error
                (.ambiguousSelectionName target formula.name))) := by
            apply eventuallyExact_of_two_premises
              (contains (Carrier.encodeString formula.name)
                (Carrier.encodeStrings seen)) boolTrue
              (scanSeenDecision boolTrue (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeResolvedFormula formula)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (.error
                (.ambiguousSelectionName target formula.name)))
              (scanRequestDecision boolTrue (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeResolvedFormula formula)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (.error
                (.ambiguousSelectionName target formula.name)))
              seenExact ambiguousExact
            intro fuel containsStep decisionStep
            simpa [encodeResolvedFormula_eq] using
              scanRequest_true_rewriteAt_exact fuel
                (Carrier.encodeString target) (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeString formula.name) formula.input
                (Carrier.encodeFormulaOrigin formula.origin)
                (Carrier.encodeResolvedFormulas formulas) boolTrue
                (encodeOutcome (.error
                  (.ambiguousSelectionName target formula.name)))
                containsStep decisionStep
          have scanExact : EventuallyExact
              (scan (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeResolvedFormulas (formula :: formulas)))
              (encodeOutcome (.error
                (.ambiguousSelectionName target formula.name))) := by
            rw [encodeResolvedFormulas_cons]
            apply eventuallyExact_of_two_premises
              (contains (Carrier.encodeString formula.name)
                (Carrier.encodeStrings requested)) boolTrue
              (scanRequestDecision boolTrue (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeResolvedFormula formula)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (.error
                (.ambiguousSelectionName target formula.name)))
              (scan (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (formulasCons (Carrier.encodeResolvedFormula formula)
                  (Carrier.encodeResolvedFormulas formulas)))
              (encodeOutcome (.error
                (.ambiguousSelectionName target formula.name)))
              requestedExact requestExact
            intro fuel containsStep decisionStep
            simpa [encodeResolvedFormula_eq] using
              scan_cons_rewriteAt_exact fuel
                (Carrier.encodeString target) (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeString formula.name) formula.input
                (Carrier.encodeFormulaOrigin formula.origin)
                (Carrier.encodeResolvedFormulas formulas) boolTrue
                (encodeOutcome (.error
                  (.ambiguousSelectionName target formula.name)))
                containsStep decisionStep
          simpa [selectNamed, requestedMember, seenMember] using scanExact
        · have seenExact := contains_encode_eventuallyExact formula.name seen
          simp only [seenMember, ↓reduceIte] at seenExact
          have eraseExact :=
            eraseFirst_encode_eventuallyExact formula.name remaining
          have recursiveExact := inductionHypothesis
            (remaining.erase formula.name) (formula.name :: seen)
          let recursiveOutcome := selectNamed target requested
            (remaining.erase formula.name) (formula.name :: seen) formulas
          have prependExact :=
            prepend_encode_eventuallyExact formula recursiveOutcome
          have selectExact : EventuallyExact
              (scanSeenDecision boolFalse (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeResolvedFormula formula)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (recursiveOutcome.map (formula :: ·))) := by
            apply eventuallyExact_of_three_premises
              (eraseFirst (Carrier.encodeString formula.name)
                (Carrier.encodeStrings remaining))
              (Carrier.encodeStrings (remaining.erase formula.name))
              (scan (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings (remaining.erase formula.name))
                (Carrier.encodeStrings (formula.name :: seen))
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome recursiveOutcome)
              (prepend (Carrier.encodeResolvedFormula formula)
                (encodeOutcome recursiveOutcome))
              (encodeOutcome (recursiveOutcome.map (formula :: ·)))
              (scanSeenDecision boolFalse (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeResolvedFormula formula)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (recursiveOutcome.map (formula :: ·)))
              eraseExact recursiveExact prependExact
            intro fuel eraseStep scanStep prependStep
            simpa [encodeResolvedFormula_eq] using
              scanSeen_false_rewriteAt_exact fuel
                (Carrier.encodeString target) (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeString formula.name) formula.input
                (Carrier.encodeFormulaOrigin formula.origin)
                (Carrier.encodeResolvedFormulas formulas)
                (Carrier.encodeStrings (remaining.erase formula.name))
                (encodeOutcome recursiveOutcome)
                (encodeOutcome (recursiveOutcome.map (formula :: ·)))
                eraseStep scanStep prependStep
          have requestExact : EventuallyExact
              (scanRequestDecision boolTrue (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeResolvedFormula formula)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (recursiveOutcome.map (formula :: ·))) := by
            apply eventuallyExact_of_two_premises
              (contains (Carrier.encodeString formula.name)
                (Carrier.encodeStrings seen)) boolFalse
              (scanSeenDecision boolFalse (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeResolvedFormula formula)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (recursiveOutcome.map (formula :: ·)))
              (scanRequestDecision boolTrue (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeResolvedFormula formula)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (recursiveOutcome.map (formula :: ·)))
              seenExact selectExact
            intro fuel containsStep decisionStep
            simpa [encodeResolvedFormula_eq] using
              scanRequest_true_rewriteAt_exact fuel
                (Carrier.encodeString target) (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeString formula.name) formula.input
                (Carrier.encodeFormulaOrigin formula.origin)
                (Carrier.encodeResolvedFormulas formulas) boolFalse
                (encodeOutcome (recursiveOutcome.map (formula :: ·)))
                containsStep decisionStep
          have scanExact : EventuallyExact
              (scan (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeResolvedFormulas (formula :: formulas)))
              (encodeOutcome (recursiveOutcome.map (formula :: ·))) := by
            rw [encodeResolvedFormulas_cons]
            apply eventuallyExact_of_two_premises
              (contains (Carrier.encodeString formula.name)
                (Carrier.encodeStrings requested)) boolTrue
              (scanRequestDecision boolTrue (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeResolvedFormula formula)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (recursiveOutcome.map (formula :: ·)))
              (scan (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (formulasCons (Carrier.encodeResolvedFormula formula)
                  (Carrier.encodeResolvedFormulas formulas)))
              (encodeOutcome (recursiveOutcome.map (formula :: ·)))
              requestedExact requestExact
            intro fuel containsStep decisionStep
            simpa [encodeResolvedFormula_eq] using
              scan_cons_rewriteAt_exact fuel
                (Carrier.encodeString target) (Carrier.encodeStrings requested)
                (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
                (Carrier.encodeString formula.name) formula.input
                (Carrier.encodeFormulaOrigin formula.origin)
                (Carrier.encodeResolvedFormulas formulas) boolTrue
                (encodeOutcome (recursiveOutcome.map (formula :: ·)))
                containsStep decisionStep
          cases recursiveOutcomeEq : recursiveOutcome with
          | error failure =>
              simpa [selectNamed, requestedMember, seenMember,
                recursiveOutcome, recursiveOutcomeEq, Except.map] using scanExact
          | ok selected =>
              simpa [selectNamed, requestedMember, seenMember,
                recursiveOutcome, recursiveOutcomeEq, Except.map] using scanExact
      · have requestedExact :=
          contains_encode_eventuallyExact formula.name requested
        simp only [requestedMember, ↓reduceIte] at requestedExact
        have recursiveExact := inductionHypothesis remaining seen
        have requestExact : EventuallyExact
            (scanRequestDecision boolFalse (Carrier.encodeString target)
              (Carrier.encodeStrings requested)
              (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
              (Carrier.encodeResolvedFormula formula)
              (Carrier.encodeResolvedFormulas formulas))
            (encodeOutcome
              (selectNamed target requested remaining seen formulas)) := by
          apply eventuallyExact_of_one_premise
            (scan (Carrier.encodeString target) (Carrier.encodeStrings requested)
              (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
              (Carrier.encodeResolvedFormulas formulas))
            (encodeOutcome
              (selectNamed target requested remaining seen formulas))
            (scanRequestDecision boolFalse (Carrier.encodeString target)
              (Carrier.encodeStrings requested)
              (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
              (Carrier.encodeResolvedFormula formula)
              (Carrier.encodeResolvedFormulas formulas))
            (encodeOutcome
              (selectNamed target requested remaining seen formulas))
            recursiveExact
          intro fuel recursiveStep
          exact scanRequest_false_rewriteAt_exact fuel
            (Carrier.encodeString target) (Carrier.encodeStrings requested)
            (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
            (Carrier.encodeResolvedFormula formula)
            (Carrier.encodeResolvedFormulas formulas)
            (encodeOutcome
              (selectNamed target requested remaining seen formulas))
            recursiveStep
        have scanExact : EventuallyExact
            (scan (Carrier.encodeString target) (Carrier.encodeStrings requested)
              (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
              (Carrier.encodeResolvedFormulas (formula :: formulas)))
            (encodeOutcome
              (selectNamed target requested remaining seen formulas)) := by
          rw [encodeResolvedFormulas_cons]
          apply eventuallyExact_of_two_premises
            (contains (Carrier.encodeString formula.name)
              (Carrier.encodeStrings requested)) boolFalse
            (scanRequestDecision boolFalse (Carrier.encodeString target)
              (Carrier.encodeStrings requested)
              (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
              (Carrier.encodeResolvedFormula formula)
              (Carrier.encodeResolvedFormulas formulas))
            (encodeOutcome
              (selectNamed target requested remaining seen formulas))
            (scan (Carrier.encodeString target) (Carrier.encodeStrings requested)
              (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
              (formulasCons (Carrier.encodeResolvedFormula formula)
                (Carrier.encodeResolvedFormulas formulas)))
            (encodeOutcome
              (selectNamed target requested remaining seen formulas))
            requestedExact requestExact
          intro fuel containsStep decisionStep
          simpa [encodeResolvedFormula_eq] using
            scan_cons_rewriteAt_exact fuel
              (Carrier.encodeString target) (Carrier.encodeStrings requested)
              (Carrier.encodeStrings remaining) (Carrier.encodeStrings seen)
              (Carrier.encodeString formula.name) formula.input
              (Carrier.encodeFormulaOrigin formula.origin)
              (Carrier.encodeResolvedFormulas formulas) boolFalse
              (encodeOutcome
                (selectNamed target requested remaining seen formulas))
              containsStep decisionStep
        simpa [selectNamed, requestedMember] using scanExact

/-- The complete declared include-selection program agrees exactly with the
independent host algorithm for every selection mode and resolved formula list. -/
theorem applySelection_encode_eventuallyExact (target : String)
    (selection : FormulaSelection) (formulas : List ResolvedFormula) :
    EventuallyExact (encodeRequest target selection formulas)
      (encodeOutcome
        (TptpOfficialIncludeResolution.applySelection target selection formulas)) := by
  cases selection with
  | implicitAll =>
      rw [encodeRequest_implicit_eq]
      simp only [TptpOfficialIncludeResolution.applySelection, encodeOutcome]
      apply eventuallyExact_of_one_step
      intro fuel
      exact apply_implicit_all_rewriteAt_exact fuel
        (Carrier.encodeString target) (Carrier.encodeResolvedFormulas formulas)
  | explicitAll =>
      rw [encodeRequest_explicit_eq]
      simp only [TptpOfficialIncludeResolution.applySelection, encodeOutcome]
      apply eventuallyExact_of_one_step
      intro fuel
      exact apply_explicit_all_rewriteAt_exact fuel
        (Carrier.encodeString target) (Carrier.encodeResolvedFormulas formulas)
  | named requested =>
      rw [encodeRequest_named_eq]
      simp only [TptpOfficialIncludeResolution.applySelection]
      have duplicateExact := firstDuplicate_encode_eventuallyExact requested
      cases duplicateEq : firstDuplicate? requested with
      | some duplicate =>
          simp only [duplicateEq, Carrier.encodeOptionalString] at duplicateExact
          have decisionExact : EventuallyExact
              (namedDecision (someString (Carrier.encodeString duplicate))
                (Carrier.encodeString target) (Carrier.encodeStrings requested)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (.error
                (.duplicateSelectionName target duplicate))) := by
            apply eventuallyExact_of_one_step
            intro fuel
            simpa [encodeOutcome, encodeDuplicateSelectionError_eq] using
              named_duplicate_rewriteAt_exact fuel
                (Carrier.encodeString target) (Carrier.encodeStrings requested)
                (Carrier.encodeResolvedFormulas formulas)
                (Carrier.encodeString duplicate)
          have applyExact : EventuallyExact
              (TptpOfficialIncludeSelectionLanguageDef.applySelection
                (Carrier.encodeString target)
                (selectionNamed (Carrier.encodeStrings requested))
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (.error
                (.duplicateSelectionName target duplicate))) := by
            apply eventuallyExact_of_two_premises
              (firstDuplicate (Carrier.encodeStrings requested))
              (someString (Carrier.encodeString duplicate))
              (namedDecision (someString (Carrier.encodeString duplicate))
                (Carrier.encodeString target) (Carrier.encodeStrings requested)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (.error
                (.duplicateSelectionName target duplicate)))
              (TptpOfficialIncludeSelectionLanguageDef.applySelection
                (Carrier.encodeString target)
                (selectionNamed (Carrier.encodeStrings requested))
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (.error
                (.duplicateSelectionName target duplicate)))
              duplicateExact decisionExact
            intro fuel duplicateStep decisionStep
            exact apply_named_rewriteAt_exact fuel
              (Carrier.encodeString target) (Carrier.encodeStrings requested)
              (Carrier.encodeResolvedFormulas formulas)
              (someString (Carrier.encodeString duplicate))
              (encodeOutcome (.error
                (.duplicateSelectionName target duplicate)))
              duplicateStep decisionStep
          simpa using applyExact
      | none =>
          simp only [duplicateEq, Carrier.encodeOptionalString] at duplicateExact
          have scanExact := selectNamed_encode_eventuallyExact target requested
            requested [] formulas
          have decisionExact : EventuallyExact
              (namedDecision noString (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (selectNamed target requested requested [] formulas)) := by
            apply eventuallyExact_of_one_premise
              (scan (Carrier.encodeString target) (Carrier.encodeStrings requested)
                (Carrier.encodeStrings requested) stringsNil
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (selectNamed target requested requested [] formulas))
              (namedDecision noString (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (selectNamed target requested requested [] formulas))
            · rw [← encodeStrings_nil_eq]
              exact scanExact
            · intro fuel scanStep
              exact named_scan_rewriteAt_exact fuel
                (Carrier.encodeString target) (Carrier.encodeStrings requested)
                (Carrier.encodeResolvedFormulas formulas)
                (encodeOutcome (selectNamed target requested requested [] formulas))
                scanStep
          have applyExact : EventuallyExact
              (TptpOfficialIncludeSelectionLanguageDef.applySelection
                (Carrier.encodeString target)
                (selectionNamed (Carrier.encodeStrings requested))
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (selectNamed target requested requested [] formulas)) := by
            apply eventuallyExact_of_two_premises
              (firstDuplicate (Carrier.encodeStrings requested)) noString
              (namedDecision noString (Carrier.encodeString target)
                (Carrier.encodeStrings requested)
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (selectNamed target requested requested [] formulas))
              (TptpOfficialIncludeSelectionLanguageDef.applySelection
                (Carrier.encodeString target)
                (selectionNamed (Carrier.encodeStrings requested))
                (Carrier.encodeResolvedFormulas formulas))
              (encodeOutcome (selectNamed target requested requested [] formulas))
              duplicateExact decisionExact
            intro fuel duplicateStep decisionStep
            exact apply_named_rewriteAt_exact fuel
              (Carrier.encodeString target) (Carrier.encodeStrings requested)
              (Carrier.encodeResolvedFormulas formulas) noString
              (encodeOutcome (selectNamed target requested requested [] formulas))
              duplicateStep decisionStep
          simpa using applyExact

namespace Canary

open TptpOfficialIncludeSelectionLanguageDef.Canary

theorem source_order_not_request_order :
    EventuallyExact
      (encodeRequest "leaf" (.named ["b", "a"]) orderedFormulas)
      (encodeOutcome (.ok [formula "a" 0, formula "b" 1])) := by
  have exactExecution := applySelection_encode_eventuallyExact "leaf"
    (.named ["b", "a"]) orderedFormulas
  have hostResult :
      TptpOfficialIncludeResolution.applySelection "leaf"
        (.named ["b", "a"]) orderedFormulas =
        .ok [formula "a" 0, formula "b" 1] := by
    rfl
  rw [hostResult] at exactExecution
  exact exactExecution

theorem explicit_all_preserves_duplicate_occurrences :
    EventuallyExact
      (encodeRequest "duplicates" .explicitAll ambiguousFormulas)
      (encodeOutcome (.ok ambiguousFormulas)) := by
  have exactExecution := applySelection_encode_eventuallyExact "duplicates"
    .explicitAll ambiguousFormulas
  have hostResult :
      TptpOfficialIncludeResolution.applySelection "duplicates"
        .explicitAll ambiguousFormulas = .ok ambiguousFormulas := by
    rfl
  rw [hostResult] at exactExecution
  exact exactExecution

theorem duplicate_request_fails_closed :
    EventuallyExact
      (encodeRequest "leaf" (.named ["a", "a"]) orderedFormulas)
      (encodeOutcome (.error (.duplicateSelectionName "leaf" "a"))) := by
  have exactExecution := applySelection_encode_eventuallyExact "leaf"
    (.named ["a", "a"]) orderedFormulas
  have hostResult :
      TptpOfficialIncludeResolution.applySelection "leaf"
        (.named ["a", "a"]) orderedFormulas =
        .error (.duplicateSelectionName "leaf" "a") := by
    rfl
  rw [hostResult] at exactExecution
  exact exactExecution

theorem missing_request_fails_closed :
    EventuallyExact
      (encodeRequest "leaf" (.named ["z"]) orderedFormulas)
      (encodeOutcome (.error (.missingSelectionName "leaf" "z"))) := by
  have exactExecution := applySelection_encode_eventuallyExact "leaf"
    (.named ["z"]) orderedFormulas
  have hostResult :
      TptpOfficialIncludeResolution.applySelection "leaf"
        (.named ["z"]) orderedFormulas =
        .error (.missingSelectionName "leaf" "z") := by
    rfl
  rw [hostResult] at exactExecution
  exact exactExecution

theorem ambiguous_formula_occurrences_fail_closed :
    EventuallyExact
      (encodeRequest "duplicates" (.named ["a"]) ambiguousFormulas)
      (encodeOutcome
        (.error (.ambiguousSelectionName "duplicates" "a"))) := by
  have exactExecution := applySelection_encode_eventuallyExact "duplicates"
    (.named ["a"]) ambiguousFormulas
  have hostResult :
      TptpOfficialIncludeResolution.applySelection "duplicates"
        (.named ["a"]) ambiguousFormulas =
        .error (.ambiguousSelectionName "duplicates" "a") := by
    rfl
  rw [hostResult] at exactExecution
  exact exactExecution

end Canary

#print axioms selectNamed_encode_eventuallyExact
#print axioms applySelection_encode_eventuallyExact
#print axioms Canary.source_order_not_request_order
#print axioms Canary.explicit_all_preserves_duplicate_occurrences
#print axioms Canary.duplicate_request_fails_closed
#print axioms Canary.missing_request_fails_closed
#print axioms Canary.ambiguous_formula_occurrences_fail_closed

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeSelectionAgreement
