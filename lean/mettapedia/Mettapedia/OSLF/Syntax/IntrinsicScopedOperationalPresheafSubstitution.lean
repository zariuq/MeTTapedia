import Mettapedia.OSLF.Syntax.CategoricalBindingStage

/-!
# Context arrows for generalized operational substitution

A semantic environment induces an actual arrow between the generic context
products. These arrows compose by the binding clone's substitution and
commute with changes of stage. They act on retained evidence by precomposition.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafSubstitution

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open CategoricalBindingModel

universe u v
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} (M : Model S D)

/-- The underlying natural-family substitution used by the actual stage clone. -/
def substituteElem {Z : D} {Γ Δ : Ctx S} {s : S.Srt}
    (σ : BindingSubstitutionAlgebra.Environment S (M.ElemOver Z) Γ Δ)
    (value : M.ElemOver Z Γ s) : M.ElemOver Z Δ s :=
  (M.kripkeSubstitution Z (N' := [])).substitute σ value

/-- The genuine arrow interpreting a contextual substitution at a generic stage. -/
def substitutionArrow {Z : D} {Γ Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (M.ElemOver Z) Γ Δ) :
    M.ctx Δ ⊗ Z ⟶ M.ctx Γ ⊗ Z :=
  lift (M.tupleEnv (Model.envValue σ _ (snd _ _) (M.genericEnv Δ Z))) (snd _ _)

@[simp] theorem substitutionArrow_snd {Z : D} {Γ Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (M.ElemOver Z) Γ Δ) :
    substitutionArrow M σ ≫ snd _ _ = snd _ _ := lift_snd _ _

/-- Each coordinate is the actual generic value of the substituted variable. -/
theorem substitutionArrow_coordinate {Z : D} {Γ Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (M.ElemOver Z) Γ Δ)
    {s : S.Srt} (var : Var Γ s) :
    substitutionArrow M σ ≫ fst _ _ ≫ projectVar M.sort var =
      M.elemValue (σ s var) := by
  rw [substitutionArrow, lift_fst_assoc, M.tupleEnv_projectVar]
  rfl

/-- Substitution of a natural program family is precomposition at its generic context. -/
theorem substitutionArrow_value {Z : D} {Γ Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (M.ElemOver Z) Γ Δ)
    {s : S.Srt} (value : (M.ElemOver Z) Γ s) :
    M.elemValue (substituteElem M σ value) =
      substitutionArrow M σ ≫ M.elemValue value :=
  M.value_eq_generic value _ (snd _ _) (Model.envValue σ _ (snd _ _) (M.genericEnv Δ Z))

/-- Identity environments induce identity arrows on the entire context and stage. -/
theorem substitutionArrow_identity (Z : D) (Γ : Ctx S) :
    substitutionArrow M (fun _ var => (M.stage Z).substitution.injectVar var :
      BindingSubstitutionAlgebra.Environment S (M.ElemOver Z) Γ Γ) =
        𝟙 (M.ctx Γ ⊗ Z) := by
  change lift (M.tupleEnv (M.genericEnv Γ Z)) (snd _ _) = _
  rw [Model.genericEnv, M.tupleEnv_restage, M.tupleEnv_projections, Category.comp_id]
  exact lift_fst_snd

/-- Composition of actual semantic environments induces composition of their context arrows. -/
theorem substitutionArrow_comp {Z : D} {Γ Δ Θ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (M.ElemOver Z) Γ Δ)
    (τ : BindingSubstitutionAlgebra.Environment S (M.ElemOver Z) Δ Θ) :
    substitutionArrow M (fun s var => substituteElem M τ (σ s var)) =
      substitutionArrow M τ ≫ substitutionArrow M σ := by
  apply hom_ext
  · rw [substitutionArrow, lift_fst]
    symm
    apply M.tupleEnv_unique
    intro s var
    simp only [Category.assoc, substitutionArrow_coordinate]
    exact (substitutionArrow_value M τ (σ s var)).symm
  · simp only [Category.assoc, substitutionArrow_snd]

/-- The generic value of a restaged program family is precomposition by the stage map. -/
theorem elemValue_restage {Z Z' : D} (h : Z' ⟶ Z) {Γ : Ctx S} {s : S.Srt}
    (value : M.ElemOver Z Γ s) :
    M.elemValue (M.restageElem h value) = (M.ctx Γ ◁ h) ≫ M.elemValue value := by
  have sameEnv : M.restage (M.ctx Γ ◁ h) (M.genericEnv Γ Z) =
      M.genericEnv Γ Z' := by
    funext sort var
    change (M.ctx Γ ◁ h) ≫ fst _ _ ≫ projectVar M.sort var =
      fst _ _ ≫ projectVar M.sort var
    rw [whiskerLeft_fst_assoc]
  have natural := value.natural (M.ctx Γ ◁ h) (snd _ _) (M.genericEnv Γ Z)
  change value.value _ (snd _ _ ≫ h) (M.genericEnv Γ Z') = _
  simpa only [Model.elemValue, whiskerLeft_snd, sameEnv] using natural

/-- Changing stage commutes with the whole contextual substitution arrow. -/
theorem substitutionArrow_restage {Z Z' : D} (h : Z' ⟶ Z) {Γ Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (M.ElemOver Z) Γ Δ) :
    substitutionArrow M (fun s var => M.restageElem h (σ s var)) ≫
        (M.ctx Γ ◁ h) =
      (M.ctx Δ ◁ h) ≫ substitutionArrow M σ := by
  apply hom_ext
  · rw [Category.assoc, whiskerLeft_fst, substitutionArrow, lift_fst]
    symm
    apply M.tupleEnv_unique
    intro s var
    simp only [Category.assoc, substitutionArrow_coordinate]
    have sameEnv : M.restage (M.ctx Δ ◁ h) (M.genericEnv Δ Z) =
        M.genericEnv Δ Z' := by
      funext sort var
      change (M.ctx Δ ◁ h) ≫ fst _ _ ≫ projectVar M.sort var =
        fst _ _ ≫ projectVar M.sort var
      rw [whiskerLeft_fst_assoc]
    have natural := (σ s var : M.ElemOver Z Δ s).natural
      (M.ctx Δ ◁ h) (snd _ _) (M.genericEnv Δ Z)
    change (M.ctx Δ ◁ h) ≫ M.elemValue (σ s var) =
      (σ s var).value _ (snd _ _ ≫ h) (M.genericEnv Δ Z')
    simpa only [Model.elemValue, whiskerLeft_snd, sameEnv] using natural.symm
  · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, substitutionArrow_snd]
    rw [Category.assoc, substitutionArrow_snd, whiskerLeft_snd]

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafSubstitution
