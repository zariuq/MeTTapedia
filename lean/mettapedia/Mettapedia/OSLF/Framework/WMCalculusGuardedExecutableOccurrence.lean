import Mettapedia.OSLF.Framework.PremiseAwareOccurrence
import Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport
import Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider
import Mettapedia.OSLF.Framework.WMCalculusContextClosure

/-!
# Executable occurrences of the checked WM outside-scope rule

The checked relation provider is consumed by the premise-aware contextual
engine. An accepted row produces an executable occurrence with the authored
rule name retained at finite fuel. The rule name is a local diagnostic; the
engine's numeric indices are positions in this particular authored language.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusGuardedExecutableOccurrence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.WeightedOccurrence
open Mettapedia.OSLF.Framework.PremiseAwareOccurrence
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- The accepted outside-scope premise contributes the target through its
specific authored rule already at one unit of contextual fuel. -/
theorem checked_forget_rule_result (relEnv : RelationEnv)
    (scope world query : Pattern)
    (guard : [("q", query), ("W", world), ("S", scope)] ∈
      applyPremisesWithEnv relEnv
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", query), ("W", world), ("S", scope)]) :
    pExtract world query ∈
      applyRuleUsing (engineBasePremises relEnv)
        (wmExtVertexLanguageDefGuarded combinedVertex)
        (rewriteAt (engineBasePremises relEnv)
          (wmExtVertexLanguageDefGuarded combinedVertex) 0)
        ruleForgetOutsideGuarded
        (pExtract (pForget scope world) query) := by
  let bindings : Bindings := [("q", query), ("W", world), ("S", scope)]
  have matched : bindings ∈
      matchPatternForRule (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded (pExtract (pForget scope world) query) := by
    rw [matchPatternForRule_eq_syntactic]
    simp [bindings, ruleForgetOutsideGuarded, pExtract, pForget,
      matchPattern, matchArgs, mergeBindings]
  have premises : bindings ∈
      premisesUsing (engineBasePremises relEnv)
        (wmExtVertexLanguageDefGuarded combinedVertex)
        (rewriteAt (engineBasePremises relEnv)
          (wmExtVertexLanguageDefGuarded combinedVertex) 0)
        ruleForgetOutsideGuarded.premises bindings := by
    simpa [bindings, premisesUsing, premiseStepUsing, engineBasePremises,
      applyPremisesWithEnv, ruleForgetOutsideGuarded] using guard
  have target :
      applyBindingsForRule (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded bindings = pExtract world query := by
    rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
    simp [bindings, ruleForgetOutsideGuarded, pExtract, applyBindings]
  simp only [applyRuleUsing, List.mem_flatMap, List.mem_map]
  exact ⟨bindings, matched, bindings, premises, target⟩

/-- A checked guard gives a concrete finite-fuel engine occurrence whose
rule identity cannot be lost to another rule with the same target. -/
theorem checked_forget_named_occurrence (relEnv : RelationEnv)
    (scope world query : Pattern)
    (guard : [("q", query), ("W", world), ("S", scope)] ∈
      applyPremisesWithEnv relEnv
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", query), ("W", world), ("S", scope)]) :
    ∃ occurrence ∈
      rewriteAtOccurrences (engineBasePremises relEnv)
        (wmExtVertexLanguageDefGuarded combinedVertex) 1
        (pExtract (pForget scope world) query),
      occurrence.target = pExtract world query ∧
      occurrence.ruleName = "WM_ForgetOutside_Guarded" := by
  have ruleMember : ruleForgetOutsideGuarded ∈
      (wmExtVertexLanguageDefGuarded combinedVertex).rewrites :=
    Mettapedia.OSLF.Framework.WMCalculusBNBridge.ruleForgetOutsideGuarded_mem_guarded
      combinedVertex (Or.inl rfl)
  obtain ⟨occurrence, member, target, ruleName⟩ :=
    rewriteAtOccurrences_named_of_rule_result
      (engineBasePremises relEnv)
      (wmExtVertexLanguageDefGuarded combinedVertex) 0
      ruleForgetOutsideGuarded
      (pExtract (pForget scope world) query) (pExtract world query)
      ruleMember (checked_forget_rule_result relEnv scope world query guard)
  exact ⟨occurrence, member, target,
    by simpa [ruleForgetOutsideGuarded] using ruleName⟩

/-- The concrete accepted counting-provider row executes the guarded rule
with its authored identity retained. -/
theorem counting_outside_named_occurrence :
    ∃ occurrence ∈
      rewriteAtOccurrences (engineBasePremises (relationEnv demoTable))
        (wmExtVertexLanguageDefGuarded combinedVertex) 1
        (pExtract (pForget scopeHandle worldHandle) outsideHandle),
      occurrence.target = pExtract worldHandle outsideHandle ∧
      occurrence.ruleName = "WM_ForgetOutside_Guarded" := by
  exact checked_forget_named_occurrence (relationEnv demoTable)
    scopeHandle worldHandle outsideHandle outside_premise_accepted

/-- The in-scope provider rejection removes this authored guard's executable
occurrence. This does not claim that unrelated rules cannot rewrite the same
source for other reasons. -/
theorem counting_inside_no_named_occurrence :
    ¬ ∃ occurrence ∈
      rewriteAtOccurrences (engineBasePremises (relationEnv demoTable))
        (wmExtVertexLanguageDefGuarded combinedVertex) 1
        (pExtract (pForget scopeHandle worldHandle) insideHandle),
      occurrence.ruleName = "WM_ForgetOutside_Guarded" := by
  decide +kernel

/-- An accepted guard reduces under the authored Combine-left congruence
rule at exactly two contextual layers: one for the guard and one for the
enclosing Combine. -/
theorem checked_forget_under_combine_left_at_two (relEnv : RelationEnv)
    (scope world query other : Pattern)
    (guard : [("q", query), ("W", world), ("S", scope)] ∈
      applyPremisesWithEnv relEnv
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", query), ("W", world), ("S", scope)]) :
    StepAt (engineBasePremises relEnv)
      (wmExtVertexLanguageDefGuardedWithCong combinedVertex)
      2
      (pCombine (pExtract (pForget scope world) query) other)
      (pCombine (pExtract world query) other) := by
  let initial : Bindings :=
    [("e2", other), ("e1", pExtract (pForget scope world) query)]
  let final : Bindings :=
    [("e1p", pExtract world query),
      ("e2", other), ("e1", pExtract (pForget scope world) query)]
  have innerAt : StepAt (engineBasePremises relEnv)
      (wmExtVertexLanguageDefGuarded combinedVertex) 1
      (pExtract (pForget scope world) query)
      (pExtract world query) := by
    apply mem_rewriteAt_iff_stepAt.mp
    simp only [rewriteAt, List.mem_flatMap]
    exact ⟨ruleForgetOutsideGuarded,
      Mettapedia.OSLF.Framework.WMCalculusBNBridge.ruleForgetOutsideGuarded_mem_guarded
        combinedVertex (Or.inl rfl),
      checked_forget_rule_result relEnv scope world query guard⟩
  have innerCongAt : StepAt (engineBasePremises relEnv)
      (wmExtVertexLanguageDefGuardedWithCong combinedVertex) 1
      (pExtract (pForget scope world) query)
      (pExtract world query) :=
    StepAt.mono_rules
      (guardedRules_subset_guardedCongRules_ext combinedVertex) innerAt
  refine StepAt.rule (rule := ruleCombineCongLeft)
    (initialBindings := initial) (finalBindings := final)
    ?_ ?_ ?_ ?_
  · simp [wmExtVertexLanguageDefGuardedWithCong, coreCongruenceRules]
  · rw [matchPatternForRule_eq_syntactic]
    simp [initial, ruleCombineCongLeft, pCombine,
      matchPattern, matchArgs, mergeBindings]
  · change PremisesAt (engineBasePremises relEnv)
      (wmExtVertexLanguageDefGuardedWithCong combinedVertex) 1
      initial [.congruence (.fvar "e1") (.fvar "e1p")] final
    have recursive : StepAt (engineBasePremises relEnv)
        (wmExtVertexLanguageDefGuardedWithCong combinedVertex) 1
        (applyBindings initial (.fvar "e1")) (pExtract world query) := by
      simpa [initial, applyBindings] using innerCongAt
    refine .cons (PremiseAt.congruence
      (premiseBindings := [("e1p", pExtract world query)])
      recursive ?_ ?_) (.nil final)
    · simp [matchPattern]
    · simp [initial, final, mergeBindings]
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
    simp [final, ruleCombineCongLeft, pCombine, applyBindings]

/-- The fixed-depth contextual result is a step of the least authored
premise-aware relation. -/
theorem checked_forget_under_combine_left (relEnv : RelationEnv)
    (scope world query other : Pattern)
    (guard : [("q", query), ("W", world), ("S", scope)] ∈
      applyPremisesWithEnv relEnv
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", query), ("W", world), ("S", scope)]) :
    langReducesUsing relEnv
      (wmExtVertexLanguageDefGuardedWithCong combinedVertex)
      (pCombine (pExtract (pForget scope world) query) other)
      (pCombine (pExtract world query) other) :=
  ⟨2, checked_forget_under_combine_left_at_two relEnv scope world query other guard⟩

/-- The bounded inner guard is an actual premise input to the authored
Combine-left rule applier, so this target is attributable to that outer
rule rather than only to unlabelled contextual closure. -/
theorem checked_forget_combine_rule_result (relEnv : RelationEnv)
    (scope world query other : Pattern)
    (guard : [("q", query), ("W", world), ("S", scope)] ∈
      applyPremisesWithEnv relEnv
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", query), ("W", world), ("S", scope)]) :
    pCombine (pExtract world query) other ∈
      applyRuleUsing (engineBasePremises relEnv)
        (wmExtVertexLanguageDefGuardedWithCong combinedVertex)
        (rewriteAt (engineBasePremises relEnv)
          (wmExtVertexLanguageDefGuardedWithCong combinedVertex) 1)
        ruleCombineCongLeft
        (pCombine (pExtract (pForget scope world) query) other) := by
  let initial : Bindings :=
    [("e2", other), ("e1", pExtract (pForget scope world) query)]
  let final : Bindings :=
    [("e1p", pExtract world query),
      ("e2", other), ("e1", pExtract (pForget scope world) query)]
  have innerAt : StepAt (engineBasePremises relEnv)
      (wmExtVertexLanguageDefGuarded combinedVertex) 1
      (pExtract (pForget scope world) query)
      (pExtract world query) := by
    apply mem_rewriteAt_iff_stepAt.mp
    simp only [rewriteAt, List.mem_flatMap]
    exact ⟨ruleForgetOutsideGuarded,
      Mettapedia.OSLF.Framework.WMCalculusBNBridge.ruleForgetOutsideGuarded_mem_guarded
        combinedVertex (Or.inl rfl),
      checked_forget_rule_result relEnv scope world query guard⟩
  have innerMember : pExtract world query ∈
      rewriteAt (engineBasePremises relEnv)
        (wmExtVertexLanguageDefGuardedWithCong combinedVertex) 1
        (pExtract (pForget scope world) query) := by
    apply mem_rewriteAt_iff_stepAt.mpr
    exact StepAt.mono_rules
      (guardedRules_subset_guardedCongRules_ext combinedVertex) innerAt
  have matched : initial ∈
      matchPatternForRule (wmExtVertexLanguageDefGuardedWithCong combinedVertex)
        ruleCombineCongLeft
        (pCombine (pExtract (pForget scope world) query) other) := by
    rw [matchPatternForRule_eq_syntactic]
    simp [initial, ruleCombineCongLeft, pCombine,
      matchPattern, matchArgs, mergeBindings]
  have premises : final ∈
      premisesUsing (engineBasePremises relEnv)
        (wmExtVertexLanguageDefGuardedWithCong combinedVertex)
        (rewriteAt (engineBasePremises relEnv)
          (wmExtVertexLanguageDefGuardedWithCong combinedVertex) 1)
        ruleCombineCongLeft.premises initial := by
    simp only [ruleCombineCongLeft, premisesUsing, List.mem_flatMap,
      List.mem_singleton]
    refine ⟨final, ?_, rfl⟩
    simp only [premiseStepUsing, List.mem_flatMap, List.mem_filterMap]
    refine ⟨pExtract world query, ?_,
      [("e1p", pExtract world query)], ?_, ?_⟩
    · simpa [initial, applyBindings] using innerMember
    · simp [matchPattern]
    · simp [initial, final, mergeBindings]
  have target :
      applyBindingsForRule (wmExtVertexLanguageDefGuardedWithCong combinedVertex)
        ruleCombineCongLeft final =
        pCombine (pExtract world query) other := by
    rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
    simp [final, ruleCombineCongLeft, pCombine, applyBindings]
  simp only [applyRuleUsing, List.mem_flatMap, List.mem_map]
  exact ⟨initial, matched, final, premises, target⟩

/-- The contextual guarded step is in the support of the same finite-fuel
premise-aware occurrence engine; the outer rule record is a Combine context
event and does not claim to retain the recursive guard proof. -/
theorem checked_forget_under_combine_left_occurs (relEnv : RelationEnv)
    (scope world query other : Pattern)
    (guard : [("q", query), ("W", world), ("S", scope)] ∈
      applyPremisesWithEnv relEnv
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", query), ("W", world), ("S", scope)]) :
    ∃ occurrence ∈
      rewriteAtOccurrences (engineBasePremises relEnv)
        (wmExtVertexLanguageDefGuardedWithCong combinedVertex) 2
        (pCombine (pExtract (pForget scope world) query) other),
      occurrence.target = pCombine (pExtract world query) other ∧
      occurrence.ruleName = "WM_CombineCongLeft" := by
  have ruleMember : ruleCombineCongLeft ∈
      (wmExtVertexLanguageDefGuardedWithCong combinedVertex).rewrites := by
    simp [wmExtVertexLanguageDefGuardedWithCong, coreCongruenceRules]
  obtain ⟨occurrence, member, target, ruleName⟩ :=
    rewriteAtOccurrences_named_of_rule_result
      (engineBasePremises relEnv)
      (wmExtVertexLanguageDefGuardedWithCong combinedVertex) 1
      ruleCombineCongLeft
      (pCombine (pExtract (pForget scope world) query) other)
      (pCombine (pExtract world query) other)
      ruleMember
      (checked_forget_combine_rule_result relEnv scope world query other guard)
  exact ⟨occurrence, member, target,
    by simpa [ruleCombineCongLeft] using ruleName⟩

#print axioms checked_forget_rule_result
#print axioms checked_forget_named_occurrence
#print axioms counting_outside_named_occurrence
#print axioms counting_inside_no_named_occurrence
#print axioms checked_forget_under_combine_left_at_two
#print axioms checked_forget_under_combine_left
#print axioms checked_forget_combine_rule_result
#print axioms checked_forget_under_combine_left_occurs

end Mettapedia.OSLF.Framework.WMCalculusGuardedExecutableOccurrence
