import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivePairContext
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Factoring a synchronous source remainder outside the selected pair

The original authored COMM rule accepts arbitrary ambient parallel remainders.
For identical syntactic channels, its step factors through the minimal pair
and the original ParCong rule, with the grouped and flat endpoints agreeing
under the existing source parallel canonicalizer.

This establishes the collection-rest comparison for ordinary source matching.
Reflective channel equality and reflective binder substitution require their
own comparison. No generated-apparatus erasure or located-purse adequacy is
asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairFraming

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Substitution

abbrev base := ActivePairContext.base

def flatSource (channel body sent after : Pattern) (rest : List Pattern) : Pattern :=
  .collection .hashBag
    (.apply "PInput" [channel, .lambda none body] ::
      .apply "POutputK" [channel, sent, after] :: rest) none

def flatResidual (body sent after : Pattern) (rest : List Pattern) : Pattern :=
  .collection .hashBag (instantiateBVar (.apply "NQuote" [sent]) body :: after :: rest) none

/-- The first two selected occurrences witness the original bag matcher;
all unmatched occurrences, with their multiplicities, remain in its rest. -/
theorem original_match_with_rest (channel body sent after : Pattern) (rest : List Pattern) :
    [("k", after), ("q", sent), ("rest", .collection .hashBag rest none),
      ("p", body), ("n", channel)] ∈
    matchPattern rhoSyncCommRewrite.left (flatSource channel body sent after rest) := by
  have input : MatchRel
      (.apply "PInput" [.fvar "n", .lambda none (.fvar "p")])
      (.apply "PInput" [channel, .lambda none body]) [("p", body), ("n", channel)] := by
    apply matchPattern_iff_matchRel.mp
    simp [matchPattern, matchArgs, mergeBindings]
  have output : MatchRel
      (.apply "POutputK" [.fvar "n", .fvar "q", .fvar "k"])
      (.apply "POutputK" [channel, sent, after]) [("q", sent), ("k", after), ("n", channel)] := by
    apply matchPattern_iff_matchRel.mp
    simp [matchPattern, matchArgs, mergeBindings]
  apply matchPattern_iff_matchRel.mpr
  apply MatchRel.collection (by decide)
  apply MatchBagRel.cons (restB := [("rest", .collection .hashBag rest none),
    ("q", sent), ("k", after), ("n", channel)]) 0 (by simp) input
  · apply MatchBagRel.cons 0 (by simp) output MatchBagRel.nilRest
    simp [mergeBindings]
  · simp [mergeBindings]

/-- Actual authored ordinary COMM with every ambient remainder retained. -/
theorem original_step_with_rest (channel body sent after : Pattern) (rest : List Pattern) :
    Step base rhoSyncCalc (flatSource channel body sent after rest)
      (flatResidual body sent after rest) := by
  apply step_of_rule (rule := rhoSyncCommRewrite)
    (initialBindings := [("k", after), ("q", sent), ("rest", .collection .hashBag rest none),
      ("p", body), ("n", channel)])
    (finalBindings := [("k", after), ("q", sent), ("rest", .collection .hashBag rest none),
      ("p", body), ("n", channel)])
  · exact List.mem_cons_self
  · rw [matchPatternForRule_eq_syntactic]
    exact original_match_with_rest channel body sent after rest
  · exact .nil
  · simp [rhoSyncCommRewrite, Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv]
  · simp [applyBindingsForRule, applyBindingsForRuleUsing_empty,
      rhoSyncCommRewrite, applyRuleBindings, applyBindingsScoped, applyBindingsScopedList,
      captureDepth, captureDepthList, restSplice, flatResidual, liftBVars_zero]
    simp [show liftBVars 0 0 = id from funext (fun p => liftBVars_zero p 0)]

/-- The original authored ParCong transports any source step through an
arbitrary external bag remainder. -/
theorem source_parallel_step {source target : Pattern} (rest : List Pattern)
    (step : Step base rhoSyncCalc source target) :
    Step base rhoSyncCalc (.collection .hashBag (source :: rest) none)
      (.collection .hashBag (target :: rest) none) := by
  apply step_of_single_congruence_rule (rule := rhoParCongRewrite)
    (initialBindings := [("rest", .collection .hashBag rest none), ("S", source)])
    (finalBindings := [("T", target), ("rest", .collection .hashBag rest none), ("S", source)])
    (premiseBindings := [("T", target)])
    (premiseSource := .fvar "S") (premiseTarget := .fvar "T") (candidate := target)
  · simp [rhoSyncCalc]
  · rw [matchPatternForRule_eq_syntactic]
    apply matchPattern_iff_matchRel.mpr
    exact .collection (by decide) (.cons 0 (by simp) .fvar .nilRest rfl)
  · rfl
  · simpa [applyBindings] using step
  · simp [matchPattern]
  · rfl
  · simp [applyBindingsForRule, applyBindingsForRuleUsing_empty,
      rhoParCongRewrite, applyRuleBindings, applyBindingsScoped, applyBindingsScopedList,
      captureDepth, captureDepthList, restSplice]
    simp [show liftBVars 0 0 = id from funext (fun p => liftBVars_zero p 0)]

/-- Regrouping at the head uses exactly the source canonicalizer's existing
parallel permutation and flattening laws. -/
theorem canonicalize_grouped_head (declaration : ReflectivePresentationDecl)
    (selected rest : List Pattern) :
    canonicalize declaration (.collection declaration.parallelCollection
      (.collection declaration.parallelCollection selected none :: rest) none) =
    canonicalize declaration
      (.collection declaration.parallelCollection (selected ++ rest) none) := by
  calc
    _ = canonicalize declaration (.collection declaration.parallelCollection
        (rest ++ [.collection declaration.parallelCollection selected none]) none) :=
      canonicalize_parallel_permutation declaration (by simpa using
        (List.perm_append_comm :
          ([Pattern.collection declaration.parallelCollection selected none] ++ rest).Perm
            (rest ++ [Pattern.collection declaration.parallelCollection selected none])))
    _ = canonicalize declaration
        (.collection declaration.parallelCollection (rest ++ selected) none) :=
      canonicalize_parallel_flatten declaration rest selected
    _ = _ := canonicalize_parallel_permutation declaration
      (List.perm_append_comm : (rest ++ selected).Perm (selected ++ rest))

/-- A source interaction with arbitrary rest and the contextualized minimal
interaction are actual authored steps with the same source canonical endpoints. -/
theorem original_rest_factorization (channel body sent after : Pattern) (rest : List Pattern) :
    Step base rhoSyncCalc (flatSource channel body sent after rest)
      (flatResidual body sent after rest) ∧
    Step base rhoSyncCalc
      (.collection .hashBag (ActivePair.sourcePair channel body sent after :: rest) none)
      (.collection .hashBag (ActivePair.sourceResidual body sent after :: rest) none) ∧
    canonicalize rhoReflectivePresentation
        (.collection .hashBag (ActivePair.sourcePair channel body sent after :: rest) none) =
      canonicalize rhoReflectivePresentation (flatSource channel body sent after rest) ∧
    canonicalize rhoReflectivePresentation
        (.collection .hashBag (ActivePair.sourceResidual body sent after :: rest) none) =
      canonicalize rhoReflectivePresentation (flatResidual body sent after rest) := by
  refine ⟨original_step_with_rest channel body sent after rest,
    source_parallel_step rest (ActivePair.source_pair_is_authored channel body sent after), ?_, ?_⟩
  · exact canonicalize_grouped_head rhoReflectivePresentation _ rest
  · exact canonicalize_grouped_head rhoReflectivePresentation _ rest

/-- The retained authored ParCong schema transports every already funded
interpreted step through any wrapped external remainder. -/
theorem generated_parallel_step {source target : Pattern} (rest : List Pattern)
    (step : Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
      ActivePairContext.interpretation base ActivePairContext.language source target) :
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step
      ActivePairContext.interpretation base ActivePairContext.language
      (.collection .hashBag (source :: rest) none)
      (.collection .hashBag (target :: rest) none) := by
  apply Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.step_of_single_congruence_rule
    (rule := ActivePair.parallelRule)
    (initialBindings := [(costSourceSchemaName "rest", .collection .hashBag rest none),
      (costSourceSchemaName "S", source)])
    (finalBindings := [(costSourceSchemaName "T", target),
      (costSourceSchemaName "rest", .collection .hashBag rest none),
      (costSourceSchemaName "S", source)])
    (premiseBindings := [(costSourceSchemaName "T", target)])
    (premiseSource := .fvar (costSourceSchemaName "S"))
    (premiseTarget := .fvar (costSourceSchemaName "T")) (candidate := target)
  · simp [ActivePairContext.language]
  · change [(costSourceSchemaName "rest", .collection .hashBag rest none),
        (costSourceSchemaName "S", source)] ∈
      matchPattern ActivePair.parallelRule.left (.collection .hashBag (source :: rest) none)
    apply matchPattern_iff_matchRel.mpr
    exact .collection (by decide) (.cons 0 (by simp) .fvar .nilRest rfl)
  · rfl
  · simpa [applyBindings, costSourceSchemaName, costSourceSchemaTag] using step
  · simp [matchPattern]
  · rfl
  · change applyRuleBindings ActivePair.parallelRule _ = _
    simp [ActivePair.parallelRule, rhoParCongRewrite,
      mapPatternSchemaNames, mapPatternListSchemaNames,
      applyRuleBindings, applyBindingsScoped, applyBindingsScopedList,
      captureDepth, captureDepthList, restSplice, costSourceSchemaName, costSourceSchemaTag]
    simp [show liftBVars 0 0 = id from funext (fun p => liftBVars_zero p 0)]

/-- The external remainder is typed in the wrapped fibre, independently of
the base-typed active pair enclosed by its own signature. -/
theorem generated_parallel_frame_typed {free : FreeTypeContext} {ambient : List TypeExpr}
    {code : Pattern} {rest : List Pattern}
    (codeTyped : HasSort ActivePairContext.language free ambient code costWrappedSortName)
    (restTyped : ElementsHaveType ActivePairContext.language free ambient rest
      (.base costWrappedSortName)) :
    HasSort ActivePairContext.language free ambient
      (.collection .hashBag (code :: rest) none) costWrappedSortName := by
  apply HasType.collectionConstructor
    (rule := costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[3])
    (parameterName := "ps") (elementType := .base costWrappedSortName)
  · decide +kernel
  · rfl
  · exact .cons codeTyped restTyped

/-- Grouping changes the raw tree; canonical equality is needed in the
source comparison and is not silently replaced by literal syntax equality. -/
theorem grouped_source_not_literal (channel body sent after : Pattern) (rest : List Pattern) :
    .collection .hashBag (ActivePair.sourcePair channel body sent after :: rest) none ≠
      flatSource channel body sent after rest := by
  simp [ActivePair.sourcePair, flatSource]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairFraming
