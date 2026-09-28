import Mettapedia.OSLF.Syntax.AuthoredPositionedRulePolynomial
import Mettapedia.OSLF.Syntax.BinderLocalPremise

/-!
# Interpreting a binder-local step premise in a binding clone

The premise's local binders extend the ambient context of the conclusion.
Its ordinary rule variables and the ambient portion of each metavariable
value are lifted separately through that extension. This yields the exact
child judgment needed by a conditional-rule polynomial. At the free term
model it agrees with contextual syntactic instantiation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.BinderLocalPremise
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial

universe u v

variable {S : Signature} {M : List (MetaArity S)}

private def variableEnvironment (A : BindingCloneAlgebra.Algebra.{u} S)
    (Γ : Ctx S) : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier Γ Γ :=
  fun _ var => A.substitution.injectVar var

/-- The child judgment requested by one intrinsically scoped authored
premise. The local binders are prepended to the ambient context, and both
endpoint sorts are the premise's declared sort. -/
def interpretPremise (A : BindingCloneAlgebra.Algebra.{u} S)
    {Ξ Γ : Ctx S} (body : Valuation (M := M) A Γ)
    (close : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier Ξ Γ)
    (premise : LocalStepPremise (withMetas S M) Ξ) : Judgment A :=
  ⟨premise.binders ++ Γ, premise.sort,
    interpretSchema A body
      (weakenEnvironment A premise.binders
        (variableEnvironment A Γ))
      (A.substitution.liftEnvironment close premise.binders) premise.source,
    interpretSchema A body
      (weakenEnvironment A premise.binders
        (variableEnvironment A Γ))
      (A.substitution.liftEnvironment close premise.binders) premise.target⟩

/-- A model interpretation preserves the exact child judgment, including
the declared binder extension, sort, and both endpoints. -/
theorem interpretPremise_map
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    {Ξ Γ : Ctx S} (body : Valuation (M := M) A Γ)
    (close : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier Ξ Γ)
    (premise : LocalStepPremise (withMetas S M) Ξ) :
    interpretPremise B (mapValuation h body)
        (fun sort var => h.raw.map (close sort var)) premise =
      mapJudgment h (interpretPremise A body close premise) := by
  have ambientEq :
      (fun sort var => h.raw.map
        (weakenEnvironment A premise.binders
          (variableEnvironment A Γ) sort var)) =
      weakenEnvironment B premise.binders
        (variableEnvironment B Γ) := by
    rw [weakenEnvironment_map]
    congr 1
    funext sort var
    exact h.raw.map_variable var
  have ordinaryEq := liftEnvironment_map h close premise.binders
  have sourceEq := interpretSchema_map h body
    (weakenEnvironment A premise.binders
      (variableEnvironment A Γ))
    (A.substitution.liftEnvironment close premise.binders)
    premise.source
  have targetEq := interpretSchema_map h body
    (weakenEnvironment A premise.binders
      (variableEnvironment A Γ))
    (A.substitution.liftEnvironment close premise.binders)
    premise.target
  rw [ambientEq, ordinaryEq] at sourceEq targetEq
  simp only [interpretPremise, mapJudgment]
  rw [sourceEq, targetEq]

/-- In the free term model this child is exactly the syntactic contextual
premise instance under its locally opened binders. -/
theorem interpretPremise_terms
    {Ξ Γ : Ctx S}
    (body : Valuation (M := M) (BindingCloneAlgebra.terms S) Γ)
    (close : BindingSubstitutionAlgebra.Environment S
      (BindingCloneAlgebra.terms S).substitution.Carrier Ξ Γ)
    (premise : LocalStepPremise (withMetas S M) Ξ) :
    interpretPremise (BindingCloneAlgebra.terms S) body close premise =
      (⟨premise.binders ++ Γ, premise.sort,
        ContextualAssignment.instantiate
          (body : ContextualAssignment S M Γ)
          (ContextualAssignment.weakenSub (S := S) premise.binders
            (fun _ var => Term.var var))
          (liftSub (close : Sub S Ξ Γ) premise.binders) premise.source,
        ContextualAssignment.instantiate
          (body : ContextualAssignment S M Γ)
          (ContextualAssignment.weakenSub (S := S) premise.binders
            (fun _ var => Term.var var))
          (liftSub (close : Sub S Ξ Γ) premise.binders) premise.target⟩ :
        Judgment (BindingCloneAlgebra.terms S)) := by
  have ambientEq :
      weakenEnvironment (BindingCloneAlgebra.terms S) premise.binders
          (variableEnvironment (BindingCloneAlgebra.terms S) Γ) =
        ContextualAssignment.weakenSub (S := S) premise.binders
          (fun _ var => Term.var var : Sub S Γ Γ) := by
    exact weakenEnvironment_terms (S := S) premise.binders
      (fun _ var => Term.var var : Sub S Γ Γ)
  have ordinaryEq :
      (BindingCloneAlgebra.terms S).substitution.liftEnvironment
          close premise.binders =
        liftSub (close : Sub S Ξ Γ) premise.binders :=
    BindingSubstitutionAlgebra.terms_liftEnvironment_eq_liftSub
      (close : Sub S Ξ Γ) premise.binders
  have sourceEq :=
    (congrArg₂
      (fun ambient ordinary =>
        interpretSchema (BindingCloneAlgebra.terms S) body
          ambient ordinary premise.source)
      ambientEq ordinaryEq).trans
      (interpretSchema_terms (body : ContextualAssignment S M Γ)
        (ContextualAssignment.weakenSub (S := S) premise.binders
          (fun _ var => Term.var var : Sub S Γ Γ))
        (liftSub (close : Sub S Ξ Γ) premise.binders) premise.source)
  have targetEq :=
    (congrArg₂
      (fun ambient ordinary =>
        interpretSchema (BindingCloneAlgebra.terms S) body
          ambient ordinary premise.target)
      ambientEq ordinaryEq).trans
      (interpretSchema_terms (body : ContextualAssignment S M Γ)
        (ContextualAssignment.weakenSub (S := S) premise.binders
          (fun _ var => Term.var var : Sub S Γ Γ))
        (liftSub (close : Sub S Ξ Γ) premise.binders) premise.target)
  exact congrArg
    (fun endpoints : Term S (premise.binders ++ Γ) premise.sort ×
        Term S (premise.binders ++ Γ) premise.sort =>
      (⟨premise.binders ++ Γ, premise.sort, endpoints⟩ :
        Judgment (BindingCloneAlgebra.terms S)))
    (congrArg₂ Prod.mk sourceEq targetEq)

#print axioms interpretPremise_map
#print axioms interpretPremise_terms

end Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation
