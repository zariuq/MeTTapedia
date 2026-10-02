import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedUnitNaturality
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedModelIsomorphisms

/-!
# Models and structure-preserving functors are equivalent

The classifying functor and recovery of a model are inverse up to natural
isomorphism. The unit preserves both substitution and the authored rule
actions; its inverse inherits these laws from the forward map. Both
naturality squares hold for all model maps and natural transformations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

namespace CategoricalModel

variable (model : CategoricalModel R equations (D := D))

/-- Recovering a model from its classifying functor gives an isomorphic model. -/
noncomputable def unitIso : model ≅ model.structured.model := by
  letI : IsIso model.unitHom.program := model.programUnitIso.isIso_hom
  letI : ∀ Γ s, IsIso (model.unitHom.events.event Γ s) :=
    fun Γ s => (model.eventIso Γ s).isIso_hom
  exact model.unitHom.isoOfComponents

@[simp] theorem unitIso_hom : model.unitIso.hom = model.unitHom := rfl

/-- Recovery preserves distinct generalized events at the same judgment. -/
theorem unit_event_injective (Z : D) (j : AuthoredPositionedRulePolynomial.Judgment
    (model.programModel.stage Z)) : Function.Injective (model.eventUnit.stage Z j) := by
  intro first second same
  apply Subtype.ext
  exact (cancel_mono (model.eventIso j.1 j.2.1).hom).mp (congrArg Subtype.val same)

/-- The complete model unit is natural, including its operational actions. -/
theorem unitHom_naturality {M N : CategoricalModel R equations (D := D)} (f : M ⟶ N) :
    f ≫ N.unitHom = M.unitHom ≫ (modelFunctor.map (classifyFunctor.map f)) := by
  apply Hom.ext'
  · exact programUnit_naturality f
  · intro Γ s
    exact eventUnit_naturality f Γ s

end CategoricalModel

/-- The recovered model is naturally isomorphic to the original model. -/
noncomputable def unitNatIso :
    𝟭 (CategoricalModel R equations (D := D)) ≅ classifyFunctor ⋙ modelFunctor :=
  NatIso.ofComponents CategoricalModel.unitIso (fun {M N} f => by
    change f ≫ N.unitIso.hom = M.unitIso.hom ≫ modelFunctor.map (classifyFunctor.map f)
    rw [CategoricalModel.unitIso_hom, CategoricalModel.unitIso_hom]
    exact CategoricalModel.unitHom_naturality f)

/-- **The universal classifying equivalence**, on all maps. -/
noncomputable def classificationEquivalence :
    CategoricalModel R equations (D := D) ≌ StructuredFunctor R equations (D := D) :=
  _root_.CategoryTheory.Equivalence.mk classifyFunctor modelFunctor unitNatIso counitNatIso

@[simp] theorem classificationEquivalence_functor :
    (classificationEquivalence (R := R) (equations := equations) (D := D)).functor =
      classifyFunctor :=
  rfl

@[simp] theorem classificationEquivalence_inverse :
    (classificationEquivalence (R := R) (equations := equations) (D := D)).inverse =
      modelFunctor :=
  rfl

/-- Classifying natural transformations retain every distinction between
maps of the independently defined models. -/
theorem classifyingMap_injective {M N : CategoricalModel R equations (D := D)} :
    Function.Injective (CategoricalModel.classifyingMap (M := M) (N := N)) := by
  intro first second same
  let e := classificationEquivalence (R := R) (equations := equations) (D := D)
  exact e.functor.map_injective same

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

end
