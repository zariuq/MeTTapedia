import Mettapedia.OSLF.Syntax.SecondOrderEquationModelNaturality
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionModels

/-!
# Free conditional-rule evidence over authored equation contexts

The authored equation models vary contravariantly with second-order
contexts. The existing free rule-tree construction can be lifted along every
binding-clone map, including its action on substituted firing evidence. Its
functor laws therefore yield one context-indexed operational model carrying
the actual authored operations, equations and conditional rule constructors.

This is an operational presheaf. A universal property for the additional
finite-limit and chosen function-object structure is a separate theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

variable {S : Signature} {M : List (MetaArity S)}

/-- The free substitution-operational model depends functorially on its
binding-equation base. The map is the proved fold of individual rule trees,
and its uniqueness controls the functor laws. -/
noncomputable def freeSubstitutionOperationalFunctor
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (equations : List (EqAxiom S M)) :
    FreeBindingEquationModel.Model equations ⥤
      SubstitutionOperationalModel rules equations where
  obj base := SubstitutionOperationalModel.free rules base
  map {base target} interpretation :=
    SubstitutionOperationalModel.lift rules base
      (SubstitutionOperationalModel.free rules target) interpretation
  map_id base := by
    exact (SubstitutionOperationalModel.lift_unique rules
      (𝟙 (SubstitutionOperationalModel.free rules base))).symm
  map_comp {base middle target} first second := by
    let composite : SubstitutionOperationalModel.Hom
        (SubstitutionOperationalModel.free rules base)
        (SubstitutionOperationalModel.free rules target) :=
      SubstitutionOperationalModel.Hom.comp
        (SubstitutionOperationalModel.lift rules base
          (SubstitutionOperationalModel.free rules middle) first)
        (SubstitutionOperationalModel.lift rules middle
          (SubstitutionOperationalModel.free rules target) second)
    exact (SubstitutionOperationalModel.lift_unique rules composite).symm

/-- Forget the individual firing evidence and retain the actual authored
binding-equation model and the base part of each model map. -/
def forgetSubstitutionOperationalBase
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (equations : List (EqAxiom S M)) :
    SubstitutionOperationalModel rules equations ⥤
      FreeBindingEquationModel.Model equations where
  obj model := model.base
  map interpretation := interpretation.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Free conditional-rule evidence is left adjoint to forgetting it. The
left naturality law follows from uniqueness of the recursive fold, while
right naturality reads the base component of an operational map. -/
noncomputable def freeSubstitutionOperationalAdjunction
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (equations : List (EqAxiom S M)) :
    freeSubstitutionOperationalFunctor rules equations ⊣
      forgetSubstitutionOperationalBase rules equations :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun base target =>
      SubstitutionOperationalModel.freeHomEquiv rules base target
    homEquiv_naturality_left_symm := by
      intro earlier later target baseMap interpretation
      let composite : SubstitutionOperationalModel.Hom
          (SubstitutionOperationalModel.free rules earlier) target :=
        SubstitutionOperationalModel.Hom.comp
          (SubstitutionOperationalModel.lift rules earlier
            (SubstitutionOperationalModel.free rules later) baseMap)
          (SubstitutionOperationalModel.lift rules later target interpretation)
      exact (SubstitutionOperationalModel.lift_unique rules composite).symm
    homEquiv_naturality_right := by
      intro base first second interpretation change
      rfl }

/-- The authored language determines a coherent operational model at every
metavariable context. An arrow acts on the full equation-class binding clone
and transports each free firing tree, including binder-local premises. -/
noncomputable def authoredOperationalPresheaf (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M)) :
    (Object S)ᵒᵖ ⥤ SubstitutionOperationalModel rules equations :=
  authoredEquationModelPresheaf S equations ⋙
    freeSubstitutionOperationalFunctor rules equations

/-- The same operational model descends to authored equation-class context
maps. Its maps retain individual firing trees and their substitution action,
even when different raw assignments denote the same equation-class arrow. -/
noncomputable def authoredQuotientOperationalPresheaf (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M)) :
    (EquationContexts (authoredEquationPresentation S equations))ᵒᵖ ⥤
      SubstitutionOperationalModel rules equations :=
  authoredEquationQuotientModelPresheaf S equations ⋙
    freeSubstitutionOperationalFunctor rules equations

/-- Restricting the equation-class operational model along the quotient
functor recovers the original raw-context model. This records that descent
changes only the identity of context arrows, not firing-tree semantics. -/
theorem authoredOperationalPresheaf_descends (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M)) :
    (authoredEquationPresentation S equations).quotientFunctor.op ⋙
      authoredQuotientOperationalPresheaf S equations rules =
        authoredOperationalPresheaf S equations rules := by
  rfl

/-- At one authored equation context, interpreting the free rule trees in any
lawful substitution-operational target is equivalent to interpreting their
binding-equation base. Both sides are spaces of actual model maps. -/
noncomputable def authoredOperationalInterpretationEquivAt (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (context : EquationContexts (authoredEquationPresentation S equations))
    (target : SubstitutionOperationalModel rules equations) :
    ((authoredQuotientOperationalPresheaf S equations rules).obj
        (Opposite.op context) ⟶ target) ≃
      ((authoredEquationQuotientModelPresheaf S equations).obj
        (Opposite.op context) ⟶ target.base) :=
  SubstitutionOperationalModel.freeHomEquiv rules
    (authoredEquationModelAt S equations context.as) target

/-- The relative universal interpretation is natural in the authored
equation context. A change of contextual metavariables can be made before or
after extending a base interpretation to all firing trees. -/
theorem authoredOperationalInterpretation_context_natural (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    {source targetContext : EquationContexts
      (authoredEquationPresentation S equations)}
    (assignment : source ⟶ targetContext)
    (target : SubstitutionOperationalModel rules equations)
    (baseMap : (authoredEquationQuotientModelPresheaf S equations).obj
      (Opposite.op source) ⟶ target.base) :
    (authoredOperationalInterpretationEquivAt S equations rules
      targetContext target).symm
        ((authoredEquationQuotientModelPresheaf S equations).map
          assignment.op ≫ baseMap) =
      (authoredQuotientOperationalPresheaf S equations rules).map
          assignment.op ≫
        (authoredOperationalInterpretationEquivAt S equations rules
          source target).symm baseMap := by
  let composed :=
    (authoredQuotientOperationalPresheaf S equations rules).map
        assignment.op ≫
      (authoredOperationalInterpretationEquivAt S equations rules
        source target).symm baseMap
  exact (SubstitutionOperationalModel.lift_unique rules composed).symm

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.freeSubstitutionOperationalFunctor
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.freeSubstitutionOperationalAdjunction
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredOperationalPresheaf
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredQuotientOperationalPresheaf
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredOperationalPresheaf_descends
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredOperationalInterpretation_context_natural
