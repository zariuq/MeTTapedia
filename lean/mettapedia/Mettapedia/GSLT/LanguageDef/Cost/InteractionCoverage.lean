import Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SynchronousDecoration

/-!
# Base-interaction coverage of the selected Cost cuts

The required lambda and rho instances each have exactly one base interaction.
Rho also declares a contextual rule with a reduction premise. Covering its
COMM cut therefore covers all base interactions, but does not implement
parallel closure. This distinction uses the existing `IsBaseRewrite` notion.
-/

namespace Mettapedia.GSLT.LanguageDef.Cost.InteractionCoverage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.LambdaInstance
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

set_option autoImplicit false

theorem lambda_all_rules (rule : RewriteRule) (member : rule ∈ lambdaCalc.rewrites) :
    rule = LambdaContinuedInteraction.lambdaIGSLT.presentation.interactionRewrite.1 := by
  exact List.mem_singleton.mp member

theorem rho_base_rules (rule : RewriteRule) (member : rule ∈ rhoCalc.rewrites)
    (base : IsBaseRewrite rule) :
    rule = rhoIGSLT.presentation.interactionRewrite.1 := by
  change rule ∈ [rhoCommRewrite, rhoParCongRewrite] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rfl
  · exact False.elim (not_isBaseRewrite_of_congruence (source := .fvar "S")
      (target := .fvar "T") (by simp [rhoParCongRewrite]) base)

theorem synchronous_base_rules (rule : RewriteRule)
    (member : rule ∈ Synchronous.rhoSyncCalc.rewrites) (base : IsBaseRewrite rule) :
    rule = Synchronous.rhoSyncIGSLT.presentation.interactionRewrite.1 := by
  change rule ∈ [Synchronous.rhoSyncCommRewrite, rhoParCongRewrite] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rfl
  · exact False.elim (not_isBaseRewrite_of_congruence (source := .fvar "S")
      (target := .fvar "T") (by simp [rhoParCongRewrite]) base)

/-- Parallel closure is authored reduction data in both rho instances. -/
theorem rho_parallel_rule_retained_in_source :
    rhoParCongRewrite ∈ rhoCalc.rewrites ∧
      rhoParCongRewrite ∈ Synchronous.rhoSyncCalc.rewrites ∧
      ¬ IsBaseRewrite rhoParCongRewrite := by
  exact ⟨List.mem_cons_of_mem _ (List.mem_singleton_self _),
    List.mem_cons_of_mem _ (List.mem_singleton_self _),
    not_isBaseRewrite_of_congruence (source := .fvar "S")
      (target := .fvar "T") (by simp [rhoParCongRewrite])⟩

/-- The claim that one selected cut covers every authored rho rule is false. -/
theorem rho_not_all_rules_selected :
    ¬ (∀ rule ∈ rhoCalc.rewrites,
      rule = rhoIGSLT.presentation.interactionRewrite.1) := by
  intro covers
  have same := covers rhoParCongRewrite rho_parallel_rule_retained_in_source.1
  have premises := congrArg RewriteRule.premises same
  contradiction

theorem synchronous_not_all_rules_selected :
    ¬ (∀ rule ∈ Synchronous.rhoSyncCalc.rewrites,
      rule = Synchronous.rhoSyncIGSLT.presentation.interactionRewrite.1) := by
  intro covers
  have same := covers rhoParCongRewrite rho_parallel_rule_retained_in_source.2.1
  have premises := congrArg RewriteRule.premises same
  contradiction

#print axioms rho_base_rules
#print axioms synchronous_base_rules
#print axioms rho_not_all_rules_selected

end Mettapedia.GSLT.LanguageDef.Cost.InteractionCoverage
