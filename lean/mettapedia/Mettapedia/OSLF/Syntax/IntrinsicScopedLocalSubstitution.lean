import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalPolynomial

/-!
# Substitution of rule-local occurrences

Substitution acts only on the selected rule's valuation. The semantic,
identity, composition, and base-change laws are transported from the existing
singleton-rule action. No global telescope is introduced by this transport.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
  (substJudgment substValuation)

universe u v

variable {S : Signature} (R : List (LocalRule S))

/-- Substitute the selected valuation beneath each metavariable's dependencies. -/
def Instance.subst {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : Instance R A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ) :
    Instance R A where
  index := occurrence.index
  ambient := Δ
  valuation := substValuation A σ occurrence.valuation
  close := fun t v => A.substitution.substitute σ (occurrence.close t v)

@[simp] theorem toSingleton_subst {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : Instance R A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ) :
    (Instance.subst R occurrence σ).toSingleton R =
      IntrinsicScopedConditionalSubstitution.Instance.subst
        [(R.get occurrence.index).2] (occurrence.toSingleton R) σ := rfl

theorem conclusionJudgment_subst {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : Instance R A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ) :
    conclusionJudgment R A (Instance.subst R occurrence σ) =
      substJudgment (conclusionJudgment R A occurrence) σ :=
  IntrinsicScopedConditionalSubstitution.conclusionJudgment_subst
    [(R.get occurrence.index).2] (occurrence.toSingleton R) σ

theorem childJudgment_subst {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : Instance R A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ)
    (position : Fin (R.get occurrence.index).2.premises.length) :
    childJudgment R A (Instance.subst R occurrence σ) position =
      substJudgment (childJudgment R A occurrence position)
        (A.substitution.liftEnvironment σ
          ((R.get occurrence.index).2.premises.get position).binders) :=
  IntrinsicScopedConditionalSubstitution.childJudgment_subst
    [(R.get occurrence.index).2] (occurrence.toSingleton R) σ position

theorem Instance.subst_identity {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : Instance R A) :
    Instance.subst R occurrence (fun _ v => A.substitution.injectVar v) =
      occurrence := by
  have same := congrArg (Instance.ofSingleton R occurrence.index)
    (IntrinsicScopedConditionalSubstitution.Instance.subst_identity
      [(R.get occurrence.index).2] (occurrence.toSingleton R))
  exact same

theorem Instance.subst_comp {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : Instance R A) {Δ Θ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ)
    (τ : Environment S A.substitution.Carrier Δ Θ) :
    Instance.subst R (Instance.subst R occurrence σ) τ =
      Instance.subst R occurrence
        (fun t v => A.substitution.substitute τ (σ t v)) := by
  exact congrArg (Instance.ofSingleton R occurrence.index)
    (IntrinsicScopedConditionalSubstitution.Instance.subst_comp
      [(R.get occurrence.index).2] (occurrence.toSingleton R) σ τ)

/-- Base interpretation commutes with substitution of a local occurrence. -/
theorem mapInstance_subst {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) (occurrence : Instance R A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ) :
    mapInstance R h (Instance.subst R occurrence σ) =
      Instance.subst R (mapInstance R h occurrence)
        (fun t v => h.raw.map (σ t v)) := by
  exact congrArg (Instance.ofSingleton R occurrence.index)
    (IntrinsicScopedConditionalSubstitution.mapInstance_subst
      [(R.get occurrence.index).2] h (occurrence.toSingleton R) σ)

#print axioms conclusionJudgment_subst
#print axioms childJudgment_subst
#print axioms Instance.subst_comp
#print axioms mapInstance_subst

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
