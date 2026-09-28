import Mettapedia.GSLT.Examples.TypedMixedPremiseHistory
import Mettapedia.OSLF.Syntax.ResultSortedScopedOperationalPresentation
import Mettapedia.OSLF.Syntax.ResultSortedMixedPremises
import Mettapedia.OSLF.Syntax.SelectedResultSortedMixedPremises
import Mettapedia.OSLF.Syntax.ScopedOperationalPresentation
import Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise

/-!
# A mixed authored rule in the recursive sorted classifier

The beta child of the mixed root-query/scoped-step rule is supplied by the
language's own recursive oracle. The resulting bounded firing is compared
with the canonical result-sorted operational constructor.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.MixedPremiseSortedClassifier

open Mettapedia.GSLT.Examples.TypedMixedPremiseHistory
open Mettapedia.GSLT.Examples.TypedPartialSpinePremise (wrapped expected step)
open Mettapedia.GSLT.Examples.ScopedLamCongExecution (betaRule)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ResultSortedMixedPremises
open Mettapedia.OSLF.Binding.ScopedRuleConstructorFrame
open Mettapedia.OSLF.Binding.SelectedResultSortedMixedPremises

private def term : TypeExpr := .base "Term"

def recursiveLanguage : LanguageDef :=
  { mixedLanguage with «rewrites» := [betaRule, mixedRule] }

def firstHistory : RuleHistory :=
  .fire 1 [.root 0 0, .step 1 0 (.fire 0 [])]

def secondHistory : RuleHistory :=
  .fire 1 [.root 0 1, .step 1 0 (.fire 0 [])]

private def results : List (RuleHistory × Pattern) :=
  rewriteAt RelationEnv.empty recursiveLanguage 2 0 wrapped

private theorem two_results : results.length = 2 := by
  decide +kernel

def firstResult : RuleHistory × Pattern :=
  results[0]'(by simp [two_results])

def secondResult : RuleHistory × Pattern :=
  results[1]'(by simp [two_results])

def historyRuleIndex : RuleHistory → Nat
  | .fire index _ => index

def historyRootOrdinal : RuleHistory → Option Nat
  | .fire _ (.root _ ordinal :: _) => some ordinal
  | _ => none

theorem first_result_observation :
    firstResult.2 = expected ∧
      historyRuleIndex firstResult.1 = 1 ∧
      historyRootOrdinal firstResult.1 = some 0 := by
  decide +kernel

theorem second_result_observation :
    secondResult.2 = expected ∧
      historyRuleIndex secondResult.1 = 1 ∧
      historyRootOrdinal secondResult.1 = some 1 := by
  decide +kernel

theorem first_recursive_firing :
    (firstResult.1, expected) ∈
      rewriteAt RelationEnv.empty recursiveLanguage 2 0 wrapped := by
  have member : firstResult ∈ results := by
    unfold firstResult
    exact List.getElem_mem (by simp [two_results])
  rw [← first_result_observation.1]
  exact member

theorem second_recursive_firing :
    (secondResult.1, expected) ∈
      rewriteAt RelationEnv.empty recursiveLanguage 2 0 wrapped := by
  have member : secondResult ∈ results := by
    unfold secondResult
    exact List.getElem_mem (by simp [two_results])
  rw [← second_result_observation.1]
  exact member

theorem distinct_recursive_histories : firstResult.1 ≠ secondResult.1 := by
  intro same
  have observed := congrArg historyRootOrdinal same
  rw [first_result_observation.2.2, second_result_observation.2.2] at observed
  cases observed

/-- This firing uses the authored mixed rule at index one; index zero is the
beta rule supplying the recursive premise. -/
private theorem selected_firing_has_mixed_shape
    (history : RuleHistory)
    (selected : (history, expected) ∈
      rewriteAt RelationEnv.empty recursiveLanguage 2 0 wrapped)
    (observedIndex : historyRuleIndex history = 1) :
    ∃ raw : RuleSkeleton RuleHistory RelationEnv.empty recursiveLanguage
      0 wrapped expected,
      raw.rule = mixedRule ∧ raw.ruleIndex = 1 := by
  obtain ⟨raw, premiseHistory, historyEq, _⟩ :=
    runtime_has_shape_with_history RelationEnv.empty recursiveLanguage
      1 0 wrapped expected history selected
  have index : raw.ruleIndex = 1 := by
    have observed := congrArg historyRuleIndex historyEq
    have indexEqual : historyRuleIndex history = raw.ruleIndex := by
      simpa [historyRuleIndex] using observed
    exact indexEqual.symm.trans observedIndex
  have ruleEq : raw.rule = mixedRule := by
    have listed := raw.listed
    simp [recursiveLanguage, index] at listed
    exact listed
  exact ⟨raw, ruleEq, index⟩

theorem first_firing_has_mixed_shape :
    ∃ raw : RuleSkeleton RuleHistory RelationEnv.empty recursiveLanguage
      0 wrapped expected,
      raw.rule = mixedRule ∧ raw.ruleIndex = 1 :=
  selected_firing_has_mixed_shape firstResult.1 first_recursive_firing
    first_result_observation.2.1

theorem second_firing_has_mixed_shape :
    ∃ raw : RuleSkeleton RuleHistory RelationEnv.empty recursiveLanguage
      0 wrapped expected,
      raw.rule = mixedRule ∧ raw.ruleIndex = 1 :=
  selected_firing_has_mixed_shape secondResult.1 second_recursive_firing
    second_result_observation.2.1

private theorem source_typed :
    Mettapedia.GSLT.LanguageDef.WellSorted.HasType
      recursiveLanguage FreeTypeContext.empty [] wrapped term := by
  apply checkHasType_sound
  decide +kernel

private theorem target_typed :
    Mettapedia.GSLT.LanguageDef.WellSorted.HasType
      recursiveLanguage FreeTypeContext.empty [] expected term := by
  apply checkHasType_sound
  decide +kernel

/-- The actual recursive firing, not merely a hand-written rule schema,
provides a constructor in the canonical result-sorted presentation. -/
private theorem selected_firing_has_sorted_constructor
    (history : RuleHistory)
    (selected : (history, expected) ∈
      rewriteAt RelationEnv.empty recursiveLanguage 2 0 wrapped)
    (observedIndex : historyRuleIndex history = 1) :
    ∃ raw : RuleSkeleton RuleHistory RelationEnv.empty recursiveLanguage
        0 wrapped expected,
      ∃ sorted : RuleShape RelationEnv.empty recursiveLanguage
        FreeTypeContext.empty [] term wrapped expected,
        sorted.raw = raw ∧ raw.rule = mixedRule ∧ raw.ruleIndex = 1 := by
  obtain ⟨raw, ruleEq, index⟩ :=
    selected_firing_has_mixed_shape history selected observedIndex
  have unique : (raw.rule.typeContext.map Prod.fst).Nodup := by
    rw [ruleEq]
    decide
  have compiled : compileList? recursiveLanguage
      (freeFromRuleContext raw.rule.typeContext) [] raw.rule.premises =
      some [.relationQuery "eq" [closedIdentity, closedIdentity],
        .step step] := by
    rw [ruleEq]
    decide +kernel
  let sorted := RuleShape.ofCompiled FreeTypeContext.empty [] term raw
    unique [.relationQuery "eq" [closedIdentity, closedIdentity],
      .step step] compiled source_typed target_typed
  exact ⟨raw, sorted, rfl, ruleEq, index⟩

theorem first_recursive_firing_has_sorted_constructor :
    ∃ raw : RuleSkeleton RuleHistory RelationEnv.empty recursiveLanguage
        0 wrapped expected,
      ∃ sorted : RuleShape RelationEnv.empty recursiveLanguage
        FreeTypeContext.empty [] term wrapped expected,
        sorted.raw = raw ∧ raw.rule = mixedRule ∧ raw.ruleIndex = 1 :=
  selected_firing_has_sorted_constructor firstResult.1
    first_recursive_firing first_result_observation.2.1

theorem second_recursive_firing_has_sorted_constructor :
    ∃ raw : RuleSkeleton RuleHistory RelationEnv.empty recursiveLanguage
        0 wrapped expected,
      ∃ sorted : RuleShape RelationEnv.empty recursiveLanguage
        FreeTypeContext.empty [] term wrapped expected,
        sorted.raw = raw ∧ raw.rule = mixedRule ∧ raw.ruleIndex = 1 :=
  selected_firing_has_sorted_constructor secondResult.1
    second_recursive_firing second_result_observation.2.1

/-- Every admitted constructor of the authored mixed rule has exactly the
one recursive child declared by its scoped step. The root query contributes
selected event data, not an additional recursive position. -/
theorem sorted_mixed_constructor_has_scoped_child
    (sorted : RuleShape RelationEnv.empty recursiveLanguage
      FreeTypeContext.empty [] term wrapped expected)
    (ruleEq : sorted.raw.rule = mixedRule) :
    ∃ childSource childTarget,
      sorted.children =
        [⟨[term, term], term, childSource, childTarget⟩] := by
  let raw := sorted.raw
  have premiseEq : raw.rule.premises =
      [.relationQuery "eq" [closedIdentity, closedIdentity],
       .scopedStep step] := by
    rw [ruleEq]
    rfl
  have checked :
      Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise.check
        recursiveLanguage (freeFromRuleContext raw.rule.typeContext)
        [] step = true := by
    rw [ruleEq]
    decide +kernel
  obtain ⟨childSource, childTarget, childEq⟩ :=
    RuleSkeleton.relationQuery_then_scopedStep_result_child
      [] (freeFromRuleContext raw.rule.typeContext) raw premiseEq checked
  have unique : (raw.rule.typeContext.map Prod.fst).Nodup := by
    rw [ruleEq]
    decide
  have compiled : compileList? recursiveLanguage
      (freeFromRuleContext raw.rule.typeContext) [] raw.rule.premises =
      some [.relationQuery "eq" [closedIdentity, closedIdentity],
        .step step] := by
    rw [ruleEq]
    decide +kernel
  have canonicalEq :
      Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?
        [] raw = some sorted.children := by
    exact sorted.canonical
  rw [Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?_of_compiled
    [] raw unique _ compiled, childEq] at canonicalEq
  have childrenEq : sorted.children =
      [⟨[term, term], term, childSource, childTarget⟩] := by
    have same := Option.some.inj canonicalEq
    have bindersEq : step.binders = [term, term] := by rfl
    have resultEq : step.resultType = term := by rfl
    simpa only [bindersEq, resultEq, List.append_nil] using same.symm
  exact ⟨childSource, childTarget, childrenEq⟩

/-- A root query followed by a scoped step cannot be misread as a
nullary rule, even when the query has multiple selected rows. -/
theorem sorted_mixed_constructor_not_nullary
    (sorted : RuleShape RelationEnv.empty recursiveLanguage
      FreeTypeContext.empty [] term wrapped expected)
    (ruleEq : sorted.raw.rule = mixedRule) : sorted.children ≠ [] := by
  obtain ⟨childSource, childTarget, childrenEq⟩ :=
    sorted_mixed_constructor_has_scoped_child sorted ruleEq
  simp [childrenEq]

/-- Each selected recursive firing enters the sorted presentation with
the exact singleton child context and result sort. -/
private theorem selected_firing_has_scoped_child
    (history : RuleHistory)
    (selected : (history, expected) ∈
      rewriteAt RelationEnv.empty recursiveLanguage 2 0 wrapped)
    (observedIndex : historyRuleIndex history = 1) :
    ∃ sorted : RuleShape RelationEnv.empty recursiveLanguage
        FreeTypeContext.empty [] term wrapped expected,
      ∃ childSource childTarget,
        sorted.raw.rule = mixedRule ∧ sorted.raw.ruleIndex = 1 ∧
          sorted.children =
            [⟨[term, term], term, childSource, childTarget⟩] := by
  obtain ⟨raw, sorted, rawEq, ruleEq, index⟩ :=
    selected_firing_has_sorted_constructor history selected observedIndex
  have sortedRule : sorted.raw.rule = mixedRule := by
    simpa [rawEq] using ruleEq
  obtain ⟨childSource, childTarget, childrenEq⟩ :=
    sorted_mixed_constructor_has_scoped_child sorted sortedRule
  exact ⟨sorted, childSource, childTarget, sortedRule,
    by simpa [rawEq] using index, childrenEq⟩

theorem first_recursive_firing_has_scoped_child :
    ∃ sorted : RuleShape RelationEnv.empty recursiveLanguage
        FreeTypeContext.empty [] term wrapped expected,
      ∃ childSource childTarget,
        sorted.raw.rule = mixedRule ∧ sorted.raw.ruleIndex = 1 ∧
          sorted.children =
            [⟨[term, term], term, childSource, childTarget⟩] :=
  selected_firing_has_scoped_child firstResult.1 first_recursive_firing
    first_result_observation.2.1

theorem second_recursive_firing_has_scoped_child :
    ∃ sorted : RuleShape RelationEnv.empty recursiveLanguage
        FreeTypeContext.empty [] term wrapped expected,
      ∃ childSource childTarget,
        sorted.raw.rule = mixedRule ∧ sorted.raw.ruleIndex = 1 ∧
          sorted.children =
            [⟨[term, term], term, childSource, childTarget⟩] :=
  selected_firing_has_scoped_child secondResult.1 second_recursive_firing
    second_result_observation.2.1

/-- This child is not inferred from its endpoints. It is the exact
oracle-selected recursive occurrence inside the authored mixed-rule frame. -/
private theorem selected_firing_has_selected_scoped_child
    (history : RuleHistory)
    (selected : (history, expected) ∈
      rewriteAt RelationEnv.empty recursiveLanguage 2 0 wrapped)
    (observedIndex : historyRuleIndex history = 1) :
    ∃ raw : RuleSkeleton RuleHistory RelationEnv.empty recursiveLanguage
        0 wrapped expected,
      ∃ childSource childTarget evidence ordinal,
        raw.rule = mixedRule ∧ raw.ruleIndex = 1 ∧
          raw.children = [(2, childSource, childTarget)] ∧
          Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.resultSortedChildren?
            [] (freeFromRuleContext raw.rule.typeContext) raw =
              some [⟨[term, term], term, childSource, childTarget⟩] ∧
          ((evidence, childTarget), ordinal) ∈
            (rewriteAt RelationEnv.empty recursiveLanguage 1 2
              childSource).zipIdx := by
  obtain ⟨rule, index, listed, firing, ⟨frame⟩,
      historyEq, targetEq⟩ :=
    (mem_rewriteAt_succ_iff_frames RelationEnv.empty recursiveLanguage
      1 0 wrapped expected history).mp selected
  have indexEq : index = 1 := by
    have projected := congrArg historyRuleIndex historyEq
    have observed : historyRuleIndex history = index := by
      simpa [historyRuleIndex] using projected
    exact observed.symm.trans observedIndex
  have ruleEq : rule = mixedRule := by
    have membership := listed
    simp [recursiveLanguage, indexEq] at membership
    exact membership
  have premiseEq : rule.premises =
      [.relationQuery "eq" [closedIdentity, closedIdentity],
       .scopedStep step] := by
    rw [ruleEq]
    rfl
  have checked :
      Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise.check
        recursiveLanguage (freeFromRuleContext rule.typeContext)
        [] step = true := by
    rw [ruleEq]
    decide +kernel
  obtain ⟨childSource, childTarget, evidence, ordinal,
      childEq, sortedEq, selectedChild⟩ :=
    RuleConstructorFrame.relationQuery_then_scopedStep_selected_child
      [] (freeFromRuleContext rule.typeContext) listed frame
        premiseEq checked
  cases ruleEq
  cases indexEq
  cases firing with
  | mk captured completed premiseHistory target =>
      dsimp at targetEq
      subst target
      let raw := RuleConstructorFrame.toSkeleton 1 listed frame
      have bindersEq : step.binders = [term, term] := by rfl
      have resultEq : step.resultType = term := by rfl
      refine ⟨raw, childSource, childTarget, evidence, ordinal,
        rfl, rfl, ?_, ?_, ?_⟩
      · simpa only [raw, bindersEq, List.length_cons,
          List.length_nil, Nat.reduceAdd] using childEq
      · change
          Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.resultSortedChildren?
            [] (freeFromRuleContext mixedRule.typeContext)
              (RuleConstructorFrame.toSkeleton 1 listed frame) =
            some [⟨[term, term], term, childSource, childTarget⟩]
        simpa only [bindersEq, resultEq, List.append_nil]
          using sortedEq
      · simpa only [bindersEq, List.length_cons,
          List.length_nil, Nat.reduceAdd] using selectedChild

theorem first_recursive_firing_has_selected_scoped_child :
    ∃ raw : RuleSkeleton RuleHistory RelationEnv.empty recursiveLanguage
        0 wrapped expected,
      ∃ childSource childTarget evidence ordinal,
        raw.rule = mixedRule ∧ raw.ruleIndex = 1 ∧
          raw.children = [(2, childSource, childTarget)] ∧
          Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.resultSortedChildren?
            [] (freeFromRuleContext raw.rule.typeContext) raw =
              some [⟨[term, term], term, childSource, childTarget⟩] ∧
          ((evidence, childTarget), ordinal) ∈
            (rewriteAt RelationEnv.empty recursiveLanguage 1 2
              childSource).zipIdx :=
  selected_firing_has_selected_scoped_child firstResult.1
    first_recursive_firing first_result_observation.2.1

theorem second_recursive_firing_has_selected_scoped_child :
    ∃ raw : RuleSkeleton RuleHistory RelationEnv.empty recursiveLanguage
        0 wrapped expected,
      ∃ childSource childTarget evidence ordinal,
        raw.rule = mixedRule ∧ raw.ruleIndex = 1 ∧
          raw.children = [(2, childSource, childTarget)] ∧
          Mettapedia.OSLF.Binding.ResultSortedScopedPremises.RuleSkeleton.resultSortedChildren?
            [] (freeFromRuleContext raw.rule.typeContext) raw =
              some [⟨[term, term], term, childSource, childTarget⟩] ∧
          ((evidence, childTarget), ordinal) ∈
            (rewriteAt RelationEnv.empty recursiveLanguage 1 2
              childSource).zipIdx :=
  selected_firing_has_selected_scoped_child secondResult.1
    second_recursive_firing second_result_observation.2.1

#print axioms first_result_observation
#print axioms second_result_observation
#print axioms distinct_recursive_histories
#print axioms first_recursive_firing_has_sorted_constructor
#print axioms second_recursive_firing_has_sorted_constructor
#print axioms sorted_mixed_constructor_has_scoped_child
#print axioms sorted_mixed_constructor_not_nullary
#print axioms first_recursive_firing_has_scoped_child
#print axioms second_recursive_firing_has_scoped_child
#print axioms first_recursive_firing_has_selected_scoped_child
#print axioms second_recursive_firing_has_selected_scoped_child

end Mettapedia.GSLT.Examples.MixedPremiseSortedClassifier
