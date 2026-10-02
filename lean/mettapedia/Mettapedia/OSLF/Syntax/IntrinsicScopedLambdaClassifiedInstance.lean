import Mettapedia.OSLF.Syntax.IntrinsicLambdaFourRulePresentation
import Mettapedia.OSLF.Syntax.IntrinsicScopedAuthoredClassifiedReduction
import Mettapedia.OSLF.Syntax.IntrinsicScopedEmptyEquationTreeComparison

/-!
# All four authored lambda rules in the general classification

The original five-entry telescope is retained at every rule and every node.
The actual empty equation quotient and the inverse binding-clone map give
an exact comparison with the unrestricted four-rule contextual relation,
including abstraction premises under their bound variable.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLambdaClassifiedInstance

open LambdaContextualRung (sig Srt appT lamT)
open AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open IntrinsicScopedSharedLocalPolynomialComparison (localRules toLocalInstance toLocalPosition)
open IntrinsicScopedSharedLocalTreeComparison (toLocalTree toSharedTree)
open IntrinsicScopedAuthoredClassifiedInstance (algebra)
open IntrinsicScopedAuthoredClassifiedReduction (ExtendedReduction)

abbrev eqs : List (EqAxiom sig IntrinsicLambdaFourRulePresentation.metas) := []
abbrev rules := localRules IntrinsicLambdaFourRulePresentation.rules

/-- The existing four-rule presentation's genuine canonical operational model. -/
abbrev model := IntrinsicScopedAuthoredClassifiedInstance.model rules eqs
abbrev classified := IntrinsicScopedAuthoredClassifiedInstance.classified rules eqs
abbrev interpretation := IntrinsicScopedAuthoredClassifiedInstance.interpretation rules eqs
abbrev restrictionIso := IntrinsicScopedAuthoredClassifiedInstance.restrictionIso rules eqs
abbrev recoveredModelIso := IntrinsicScopedAuthoredClassifiedInstance.recoveredModelIso rules eqs

/-- No rule row or complete shared telescope has been discarded. -/
theorem rule_inventory : rules =
    [⟨IntrinsicLambdaFourRulePresentation.metas, IntrinsicLambdaFourRulePresentation.beta⟩,
     ⟨IntrinsicLambdaFourRulePresentation.metas, IntrinsicLambdaFourRulePresentation.appCongL⟩,
     ⟨IntrinsicLambdaFourRulePresentation.metas, IntrinsicLambdaFourRulePresentation.appCongR⟩,
     ⟨IntrinsicLambdaFourRulePresentation.metas, IntrinsicLambdaFourRulePresentation.lamCong⟩] := rfl

/-- The original ordered premise profiles include LamCong's bound term variable. -/
theorem ordered_premise_binders :
    rules.map (fun declaration => declaration.2.premises.map (fun premise => premise.binders)) =
      [[], [[]], [[]], [[Srt.term]]] := rfl

/-- The unpruned adapter preserves the actual LamCong child context. -/
theorem lamCong_child_context (Γ : Ctx sig)
    (valuation : SemanticContextualMetavariables.Valuation
      (M := IntrinsicLambdaFourRulePresentation.metas) (BindingCloneAlgebra.terms sig) Γ) :
    (IntrinsicScopedLocalPolynomial.childJudgment rules (BindingCloneAlgebra.terms sig)
      (toLocalInstance IntrinsicLambdaFourRulePresentation.rules
        (IntrinsicLambdaFourRulePresentation.lamCongOccurrence Γ valuation))
      (toLocalPosition IntrinsicLambdaFourRulePresentation.rules
        (IntrinsicLambdaFourRulePresentation.lamCongOccurrence Γ valuation)
        ⟨0, by simp [IntrinsicLambdaFourRulePresentation.lamCongOccurrence,
          IntrinsicLambdaFourRulePresentation.rules,
          IntrinsicLambdaFourRulePresentation.lamCong]⟩)).1 = Srt.term :: Γ :=
  (congrArg Sigma.fst (IntrinsicScopedSharedLocalPolynomialComparison.toLocal_child
    IntrinsicLambdaFourRulePresentation.rules _ _)).trans
      (IntrinsicLambdaFourRulePresentation.lamCongChildContext Γ valuation)

/-- Every open contextual step, and only such a step, has an actual
classified-model event between these original program classes. -/
theorem step_iff_tree {Γ : Ctx sig} (source target : Term sig Γ Srt.term) :
    LambdaContextualRung.Step Γ source target ↔
      Nonempty (IntrinsicScopedLocalPolynomial.Tree rules (algebra eqs)
        (mapJudgment (BindingEquationQuotientModel.projection eqs)
          (⟨Γ, Srt.term, source, target⟩ : Judgment (BindingCloneAlgebra.terms sig)))) := by
  apply IntrinsicLambdaFourRulePresentation.sourceStep_iff_reduces.trans
  apply Iff.trans ?_ (IntrinsicScopedEmptyEquationTreeComparison.raw_iff_quotient
    IntrinsicLambdaFourRulePresentation.metas rules _)
  constructor
  · rintro ⟨tree⟩
    exact ⟨toLocalTree IntrinsicLambdaFourRulePresentation.rules _ _ tree⟩
  · rintro ⟨tree⟩
    exact ⟨toSharedTree IntrinsicLambdaFourRulePresentation.rules _ _ tree⟩

/-- The one genuine cocontinuous classification covers exactly the full
four-rule relation at every original ordinary context. -/
theorem extension_iff_step {Γ : Ctx sig} (source target : Term sig Γ Srt.term) :
    ExtendedReduction rules eqs source target ↔
      LambdaContextualRung.Step Γ source target :=
  (IntrinsicScopedAuthoredClassifiedReduction.extension_iff_tree rules eqs source target).trans
    (step_iff_tree source target).symm

theorem beta_classified {Γ : Ctx sig} (body : Term sig (Srt.term :: Γ) Srt.term)
    (argument : Term sig Γ Srt.term) :
    ExtendedReduction rules eqs (appT (lamT body) argument) (inst body argument) :=
  (extension_iff_step _ _).mpr (.beta body argument)

theorem appCongL_classified {Γ : Ctx sig} {source target : Term sig Γ Srt.term}
    (argument : Term sig Γ Srt.term)
    (child : ExtendedReduction rules eqs source target) :
    ExtendedReduction rules eqs (appT source argument) (appT target argument) :=
  (extension_iff_step _ _).mpr (.appCongL argument ((extension_iff_step _ _).mp child))

theorem appCongR_classified {Γ : Ctx sig} {source target : Term sig Γ Srt.term}
    (function : Term sig Γ Srt.term)
    (child : ExtendedReduction rules eqs source target) :
    ExtendedReduction rules eqs (appT function source) (appT function target) :=
  (extension_iff_step _ _).mpr (.appCongR function ((extension_iff_step _ _).mp child))

theorem lamCong_classified {Γ : Ctx sig}
    {source target : Term sig (Srt.term :: Γ) Srt.term}
    (child : ExtendedReduction rules eqs source target) :
    ExtendedReduction rules eqs (lamT source) (lamT target) :=
  (extension_iff_step _ _).mpr (.lamCong ((extension_iff_step _ _).mp child))

/-- A variable still has no event in the genuine interpreted generic reduction. -/
theorem variable_has_no_extended_firing {Γ : Ctx sig} (v : Var Γ Srt.term)
    (target : Term sig Γ Srt.term) :
    ¬ ExtendedReduction rules eqs (.var v) target := by
  intro firing
  exact IntrinsicLambdaFourRulePresentation.variable_has_no_intrinsic_firing v
    (IntrinsicLambdaFourRulePresentation.sourceStep_iff_reduces.mp
      ((extension_iff_step _ _).mp firing))

end Mettapedia.OSLF.Binding.IntrinsicScopedLambdaClassifiedInstance
