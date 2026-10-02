import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafEventPowers
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafNaturalEvidence
import Mathlib.CategoryTheory.HomCongr

/-!
# Generalized retained events as natural evidence

Contextual event sections are equivalent to arrows from the full context
product into the original retained-event presheaf. This comparison preserves
source and target, rather than forgetting the event witness.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafEventFunctions

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open IntrinsicScopedConditionalPresheaf (Base)
open IntrinsicScopedJudgmentAction (JudgmentAction)
open IntrinsicScopedOperationalPresheafEvents
open IntrinsicScopedOperationalPresheafEventPowers
open IntrinsicScopedOperationalPresheafPrograms (target model contextIso)
open MultiBinderPresheaf (binders)

universe u
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S}

/-- Context-function universal property transported along the actual context representation. -/
def contextFunctionEquiv (Γ : Ctx S) (F Z : IntrinsicScopedOperationalPresheafPrograms.target A) :
    (Z ⟶ (binders A Γ).functorHom F) ≃
      (CategoricalBindingModel.contextOf (IntrinsicScopedConditionalPresheaf.programs A) Γ ⊗ Z ⟶ F) :=
  (FunctorToTypes.functorHomEquiv (binders A Γ) Z F).trans {
    toFun := fun f => (contextIso A Γ).hom ▷ Z ≫ f
    invFun := fun f => (contextIso A Γ).inv ▷ Z ≫ f
    left_inv := fun f => by
      dsimp only
      rw [← Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
    right_inv := fun f => by
      dsimp only
      rw [← Category.assoc, ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight, Category.id_comp] }

/-- Every generalized contextual event is its genuine natural retained-evidence arrow. -/
def eventFunctionEquiv (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt) (Z : IntrinsicScopedOperationalPresheafPrograms.target A) :
    (Z ⟶ events Y Γ s) ≃ ((model A).ctx Γ ⊗ Z ⟶ sortEvents Y s) :=
  ((Iso.refl Z).homCongr (eventPowerIso Y Γ s)).trans (contextFunctionEquiv Γ (sortEvents Y s) Z)

/-- The function comparison computes at every clone stage and ordinary assignment. -/
theorem eventFunctionEquiv_apply (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt)
    (Z : IntrinsicScopedOperationalPresheafPrograms.target A) (event : Z ⟶ events Y Γ s) (X : Base A)
    (input : ((model A).ctx Γ).obj X) (z : Z.obj X) :
    (eventFunctionEquiv Y Γ s Z event).app X (input, z) =
      (((eventPowerIso Y Γ s).hom.app X (event.app X z)).app X (𝟙 X))
        ((contextIso A Γ).hom.app X input) := rfl

/-- Reading retained evidence then its source is actual categorical uncurrying. -/
theorem eventFunctionEquiv_source (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt)
    (Z : IntrinsicScopedOperationalPresheafPrograms.target A) (event : Z ⟶ events Y Γ s) :
    eventFunctionEquiv Y Γ s Z event ≫ source Y s =
      (model A).uncurry (event ≫ sourcePower Y Γ s) := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  rintro ⟨input, z⟩
  rfl

/-- Reading retained evidence then its target is the same actual uncurrying. -/
theorem eventFunctionEquiv_target (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt)
    (Z : IntrinsicScopedOperationalPresheafPrograms.target A) (event : Z ⟶ events Y Γ s) :
    eventFunctionEquiv Y Γ s Z event ≫ IntrinsicScopedOperationalPresheafEventPowers.target Y s =
      (model A).uncurry (event ≫ targetPower Y Γ s) := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  rintro ⟨input, z⟩
  rfl

/-- Generalized event values and natural retained evidence have identical endpoint fibers. -/
def stageEventEquiv (Y : JudgmentAction.{u,u} A)
    (Z : IntrinsicScopedOperationalPresheafPrograms.target A)
    (judgment : AuthoredPositionedRulePolynomial.Judgment ((model A).stage Z)) :
    (objects Y).StageEvent Z judgment ≃
      IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A) (sortEvents Y)
        (source Y) (IntrinsicScopedOperationalPresheafEventPowers.target Y) Z judgment where
  toFun event := ⟨eventFunctionEquiv Y judgment.1 judgment.2.1 Z event.1,
    (eventFunctionEquiv_source Y _ _ _ event.1).trans
      ((congrArg (model A).uncurry event.2.1).trans ((model A).uncurry_curry _)),
    (eventFunctionEquiv_target Y _ _ _ event.1).trans
      ((congrArg (model A).uncurry event.2.2).trans ((model A).uncurry_curry _))⟩
  invFun value :=
    ⟨(eventFunctionEquiv Y judgment.1 judgment.2.1 Z).symm value.1, by
      constructor
      · apply (model A).hom_ext_power
        exact (eventFunctionEquiv_source Y _ _ _ _).symm.trans
          ((congrArg (· ≫ source Y judgment.2.1)
            ((eventFunctionEquiv Y _ _ _).apply_symm_apply value.1)).trans
              (value.2.1.trans ((model A).uncurry_curry _).symm))
      · apply (model A).hom_ext_power
        exact (eventFunctionEquiv_target Y _ _ _ _).symm.trans
          ((congrArg (· ≫ IntrinsicScopedOperationalPresheafEventPowers.target Y judgment.2.1)
            ((eventFunctionEquiv Y _ _ _).apply_symm_apply value.1)).trans
              (value.2.2.trans ((model A).uncurry_curry _).symm))⟩
  left_inv event := Subtype.ext ((eventFunctionEquiv Y _ _ _).symm_apply_apply event.1)
  right_inv value := Subtype.ext ((eventFunctionEquiv Y _ _ _).apply_symm_apply value.1)

/-- Generalized stage changes precompose the complete retained-evidence arrow. -/
theorem eventFunctionEquiv_restage (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt)
    {Z Z' : IntrinsicScopedOperationalPresheafPrograms.target A} (h : Z' ⟶ Z)
    (event : Z ⟶ events Y Γ s) :
    eventFunctionEquiv Y Γ s Z' (h ≫ event) =
      ((model A).ctx Γ ◁ h) ≫ eventFunctionEquiv Y Γ s Z event := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  rintro ⟨input, z⟩
  rfl

/-- The entire endpoint-fiber comparison is natural at every generalized stage. -/
theorem stageEventEquiv_restage (Y : JudgmentAction.{u,u} A)
    {Z Z' : IntrinsicScopedOperationalPresheafPrograms.target A} (h : Z' ⟶ Z)
    {judgment : AuthoredPositionedRulePolynomial.Judgment ((model A).stage Z)}
    (event : (objects Y).StageEvent Z judgment) :
    stageEventEquiv Y Z'
        (AuthoredPositionedRulePolynomial.mapJudgment ((model A).stageRestage h) judgment)
        ((objects Y).restage h event) =
      IntrinsicScopedOperationalPresheafNaturalEvidence.restage h (stageEventEquiv Y Z judgment event) :=
  Subtype.ext (eventFunctionEquiv_restage Y _ _ h event.1)

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafEventFunctions
