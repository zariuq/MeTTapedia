import Mettapedia.OSLF.Syntax.BindingContextExtensionComparison
import Mettapedia.OSLF.Syntax.SemanticScopedPremiseInterpretation

/-!
# Authored scoped premises as contextual function objects

Both endpoints of a binder-local conditional premise are interpreted in the
presheaf exponential for its exact binder list. The representation is
natural in ambient substitution and in binding-clone model maps. This is the
closed-structure comparison for the authored rule syntax; an operational
premise remains a request for firing evidence, not an equation of terms.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalClosedInterpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.BinderLocalPremise
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.MultiBinderPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

universe u

variable {S : Signature} {M : List (MetaArity S)}

/-- The two individually retained program endpoints of an authored scoped
premise, represented as functions of all its locally bound variables. -/
def premiseFunctions (A : BindingCloneAlgebra.Algebra.{u} S)
    {Ξ Γ : Ctx S} (valuation : Valuation (M := M) A Γ)
    (close : Environment S A.substitution.Carrier Ξ Γ)
    (premise : LocalStepPremise (withMetas S M) Ξ) :
    ((binders A premise.binders).functorHom (programs A premise.sort)).obj
        (Opposite.op (ContextObject.ofList A.substitution.toClone Γ)) ×
      ((binders A premise.binders).functorHom (programs A premise.sort)).obj
        (Opposite.op (ContextObject.ofList A.substitution.toClone Γ)) :=
  let judgment := interpretPremise A valuation close premise
  ((scopedBodyEquiv A (ContextObject.ofList A.substitution.toClone Γ)
      premise.binders premise.sort).symm judgment.2.2.1,
    (scopedBodyEquiv A (ContextObject.ofList A.substitution.toClone Γ)
      premise.binders premise.sort).symm judgment.2.2.2)

/-- The function representation exposes exactly the semantic source and
target requested by the original authored premise. -/
theorem premiseFunctions_body (A : BindingCloneAlgebra.Algebra.{u} S)
    {Ξ Γ : Ctx S} (valuation : Valuation (M := M) A Γ)
    (close : Environment S A.substitution.Carrier Ξ Γ)
    (premise : LocalStepPremise (withMetas S M) Ξ) :
    let comparison := scopedBodyEquiv A
      (ContextObject.ofList A.substitution.toClone Γ)
      premise.binders premise.sort
    comparison (premiseFunctions A valuation close premise).1 =
        (interpretPremise A valuation close premise).2.2.1 ∧
      comparison (premiseFunctions A valuation close premise).2 =
        (interpretPremise A valuation close premise).2.2.2 := by
  constructor <;> exact Equiv.apply_symm_apply _ _

/-- Interpreting a rule premise in another binding clone agrees with the
induced map of its actual presheaf function objects, for both endpoints. -/
theorem premiseFunctions_map
    {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B)
    {Ξ Γ : Ctx S} (valuation : Valuation (M := M) A Γ)
    (close : Environment S A.substitution.Carrier Ξ Γ)
    (premise : LocalStepPremise (withMetas S M) Ξ) :
    premiseFunctions B (mapValuation h valuation)
        (fun sort var => h.raw.map (close sort var)) premise =
      ((mapScopedFunctions h premise.binders premise.sort).app
          (Opposite.op (ContextObject.ofList A.substitution.toClone Γ))
          (premiseFunctions A valuation close premise).1,
        (mapScopedFunctions h premise.binders premise.sort).app
          (Opposite.op (ContextObject.ofList A.substitution.toClone Γ))
          (premiseFunctions A valuation close premise).2) := by
  apply Prod.ext
  · apply (scopedBodyEquiv B (ContextObject.ofList B.substitution.toClone Γ)
      premise.binders premise.sort).injective
    change scopedBodyEquiv B (ContextObject.ofList B.substitution.toClone Γ)
        premise.binders premise.sort
        (premiseFunctions B (mapValuation h valuation)
          (fun sort var => h.raw.map (close sort var)) premise).1 =
      scopedBodyEquiv B (ContextObject.ofList B.substitution.toClone Γ)
        premise.binders premise.sort
        ((mapScopedFunctions h premise.binders premise.sort).app
          (Opposite.op (ContextObject.ofList A.substitution.toClone Γ))
          (premiseFunctions A valuation close premise).1)
    have leftB := (premiseFunctions_body B
      (mapValuation h valuation)
      (fun sort var => h.raw.map (close sort var)) premise).1
    have leftA := (premiseFunctions_body A valuation close premise).1
    have mappedLeft :
        (interpretPremise B (mapValuation h valuation)
          (fun sort var => h.raw.map (close sort var)) premise).2.2.1 =
        h.raw.map (interpretPremise A valuation close premise).2.2.1 := by
      have mapped := interpretPremise_map h valuation close premise
      simp only [interpretPremise, AuthoredPositionedRulePolynomial.mapJudgment,
        Sigma.mk.inj_iff, heq_iff_eq, true_and] at mapped
      exact congrArg Prod.fst mapped
    have functionBody := mapScopedFunctions_body h premise.binders
      premise.sort (ContextObject.ofList A.substitution.toClone Γ)
      (premiseFunctions A valuation close premise).1
    exact leftB.trans (mappedLeft.trans
      ((congrArg h.raw.map leftA.symm).trans functionBody.symm))
  · apply (scopedBodyEquiv B (ContextObject.ofList B.substitution.toClone Γ)
      premise.binders premise.sort).injective
    change scopedBodyEquiv B (ContextObject.ofList B.substitution.toClone Γ)
        premise.binders premise.sort
        (premiseFunctions B (mapValuation h valuation)
          (fun sort var => h.raw.map (close sort var)) premise).2 =
      scopedBodyEquiv B (ContextObject.ofList B.substitution.toClone Γ)
        premise.binders premise.sort
        ((mapScopedFunctions h premise.binders premise.sort).app
          (Opposite.op (ContextObject.ofList A.substitution.toClone Γ))
          (premiseFunctions A valuation close premise).2)
    have rightB := (premiseFunctions_body B
      (mapValuation h valuation)
      (fun sort var => h.raw.map (close sort var)) premise).2
    have rightA := (premiseFunctions_body A valuation close premise).2
    have mappedRight :
        (interpretPremise B (mapValuation h valuation)
          (fun sort var => h.raw.map (close sort var)) premise).2.2.2 =
        h.raw.map (interpretPremise A valuation close premise).2.2.2 := by
      have mapped := interpretPremise_map h valuation close premise
      simp only [interpretPremise, AuthoredPositionedRulePolynomial.mapJudgment,
        Sigma.mk.inj_iff, heq_iff_eq, true_and] at mapped
      exact congrArg Prod.snd mapped
    have functionBody := mapScopedFunctions_body h premise.binders
      premise.sort (ContextObject.ofList A.substitution.toClone Γ)
      (premiseFunctions A valuation close premise).2
    exact rightB.trans (mappedRight.trans
      ((congrArg h.raw.map rightA.symm).trans functionBody.symm))

/-- Substituting an ambient environment into an authored binder-local
premise is exactly reindexing both of its contextual function endpoints.
The event requested by the premise remains an operational obligation. -/
theorem premiseFunctions_substitute
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {Ξ Γ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ)
    (valuation : Valuation (M := M) A Γ)
    (close : Environment S A.substitution.Carrier Ξ Γ)
    (premise : LocalStepPremise (withMetas S M) Ξ) :
    premiseFunctions A (substValuation A σ valuation)
        (fun sort var => A.substitution.substitute σ (close sort var))
        premise =
      let reindex := ((binders A premise.binders).functorHom
        (programs A premise.sort)).map
          (Quiver.Hom.op (environmentArrow A σ))
      (reindex (premiseFunctions A valuation close premise).1,
        reindex (premiseFunctions A valuation close premise).2) := by
  apply Prod.ext
  · apply (scopedBodyEquiv A
      (ContextObject.ofList A.substitution.toClone Δ)
      premise.binders premise.sort).injective
    have newBody := (premiseFunctions_body A
      (substValuation A σ valuation)
      (fun sort var => A.substitution.substitute σ (close sort var))
      premise).1
    have oldBody := (premiseFunctions_body A valuation close premise).1
    have sourceSub := substitute_interpretSchema_premise A σ
      valuation close premise.binders premise.source
    have reindexed := scopedBodyEquiv_reindex A
      premise.binders premise.sort
      (Quiver.Hom.op (environmentArrow A σ))
      (premiseFunctions A valuation close premise).1
    exact newBody.trans
      (sourceSub.symm.trans
        ((congrArg (A.substitution.substitute
          (A.substitution.liftEnvironment σ premise.binders))
          oldBody.symm).trans
        ((scopedBodies_substitute A premise.binders σ premise.sort _).symm.trans
          reindexed.symm)))
  · apply (scopedBodyEquiv A
      (ContextObject.ofList A.substitution.toClone Δ)
      premise.binders premise.sort).injective
    have newBody := (premiseFunctions_body A
      (substValuation A σ valuation)
      (fun sort var => A.substitution.substitute σ (close sort var))
      premise).2
    have oldBody := (premiseFunctions_body A valuation close premise).2
    have targetSub := substitute_interpretSchema_premise A σ
      valuation close premise.binders premise.target
    have reindexed := scopedBodyEquiv_reindex A
      premise.binders premise.sort
      (Quiver.Hom.op (environmentArrow A σ))
      (premiseFunctions A valuation close premise).2
    exact newBody.trans
      (targetSub.symm.trans
        ((congrArg (A.substitution.substitute
          (A.substitution.liftEnvironment σ premise.binders))
          oldBody.symm).trans
        ((scopedBodies_substitute A premise.binders σ premise.sort _).symm.trans
          reindexed.symm)))

#print axioms premiseFunctions_map
#print axioms premiseFunctions_substitute

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalClosedInterpretation
