import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Monotonic contextual-depth bounds

Increasing the contextual-depth bound preserves every previously generated
reduct.  This concerns the finite derivation bound, not an evaluator search
strategy or a promise to execute effects from only one branch.
-/

namespace Mettapedia.OSLF.MeTTaIL.ContextualStep

open Syntax Match

theorem premiseStepUsing_mono_reduction
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {first second : Pattern → List Pattern}
    (inclusion : ∀ source, first source ⊆ second source)
    (bindings : Bindings) (premise : Premise) :
    premiseStepUsing base lang first bindings premise ⊆
      premiseStepUsing base lang second bindings premise := by
  intro output member
  cases premise with
  | congruence source target =>
    simp only [premiseStepUsing, List.mem_flatMap, List.mem_filterMap] at member ⊢
    obtain ⟨candidate, step, matched, matchMember, merged⟩ := member
    exact ⟨candidate, inclusion _ step, matched, matchMember, merged⟩
  | freshness _ => exact member
  | relationQuery _ _ => exact member
  | forAll _ _ _ => exact member

theorem premisesUsing_mono_reduction
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {first second : Pattern → List Pattern}
    (inclusion : ∀ source, first source ⊆ second source)
    (premises : List Premise) (bindings : Bindings) :
    premisesUsing base lang first premises bindings ⊆
      premisesUsing base lang second premises bindings := by
  induction premises generalizing bindings with
  | nil => intro output member; exact member
  | cons premise rest ih =>
    intro output member
    simp only [premisesUsing, List.mem_flatMap] at member ⊢
    obtain ⟨middle, head, tail⟩ := member
    exact ⟨middle, premiseStepUsing_mono_reduction inclusion _ _ head, ih _ tail⟩

theorem applyRuleUsing_mono_reduction
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {first second : Pattern → List Pattern}
    (inclusion : ∀ source, first source ⊆ second source)
    (rule : RewriteRule) (source : Pattern) :
    applyRuleUsing base lang first rule source ⊆
      applyRuleUsing base lang second rule source := by
  intro output member
  simp only [applyRuleUsing, List.mem_flatMap, List.mem_map] at member ⊢
  obtain ⟨initial, matched, final, premises, outputEq⟩ := member
  exact ⟨initial, matched, final,
    premisesUsing_mono_reduction inclusion _ _ premises, outputEq⟩

theorem rewriteAt_subset_succ (base : BasePremiseEvaluator)
    (lang : LanguageDef) (fuel : Nat) (source : Pattern) :
    rewriteAt base lang fuel source ⊆ rewriteAt base lang (fuel + 1) source := by
  induction fuel generalizing source with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
    intro output member
    simp only [rewriteAt, List.mem_flatMap] at member ⊢
    obtain ⟨rule, available, step⟩ := member
    exact ⟨rule, available, applyRuleUsing_mono_reduction ih _ _ step⟩

theorem rewriteAt_mono_fuel (base : BasePremiseEvaluator)
    (lang : LanguageDef) {first second : Nat} (le : first ≤ second)
    (source : Pattern) :
    rewriteAt base lang first source ⊆ rewriteAt base lang second source := by
  induction le with
  | refl => intro output member; exact member
  | @step fuel _ ih =>
    intro output member
    exact rewriteAt_subset_succ base lang fuel source (ih member)

theorem StepAt.mono_fuel {base : BasePremiseEvaluator} {lang : LanguageDef}
    {first second : Nat} {source target : Pattern}
    (step : StepAt base lang first source target) (le : first ≤ second) :
    StepAt base lang second source target := by
  apply mem_rewriteAt_iff_stepAt.mp
  exact rewriteAt_mono_fuel base lang le source (mem_rewriteAt_iff_stepAt.mpr step)

end Mettapedia.OSLF.MeTTaIL.ContextualStep
