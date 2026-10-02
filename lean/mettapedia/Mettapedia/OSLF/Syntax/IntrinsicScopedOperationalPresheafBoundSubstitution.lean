import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRuleSubstitutionPoints

/-!
# Actual contextual substitution beneath ordered premise binders

The generic binder context arrow and the genuine substitution arrow commute.
Both sides retain the original ordered binder projections and substitute the
ambient context through the same evaluated environment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafBoundSubstitution

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open CategoricalBindingModel BindingSubstitutionAlgebra
open IntrinsicScopedOperationalPresheafSubstitution
open IntrinsicScopedOperationalPresheafBoundContexts
open IntrinsicScopedOperationalPresheafRuleSubstitutionPoints

universe u v
variable {S : Signature} {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable (M : Model S D)

/-- The actual bound context arrow reads its full ordered extended environment. -/
theorem boundContextArrow_environment (bs Γ : Ctx S) (Z : D) :
    M.restage (boundContextArrow M bs Γ Z) (M.genericEnv (bs ++ Γ) Z) =
      M.extendEnv bs (M.genericEnv Γ Z) := by
  funext s var
  change boundContextArrow M bs Γ Z ≫ fst _ _ ≫ projectVar M.sort var = _
  rw [boundContextArrow, lift_fst_assoc, M.tupleEnv_projectVar]

/-- Its ordinary context component is the actual tuple of all binder and old
ordinary values, in the declared order. -/
theorem boundContextArrow_fst (bs Γ : Ctx S) (Z : D) :
    boundContextArrow M bs Γ Z ≫ fst _ _ =
      M.tupleEnv (M.extendEnv bs (M.genericEnv Γ Z)) := lift_fst _ _

/-- Genuine contextual substitution commutes with the actual ordered binder
context arrow, for every categorical binding model and semantic environment. -/
theorem boundContextArrow_substitution (bs : Ctx S) {Z : D} {Γ Δ : Ctx S}
    (σ : Environment S (M.stage Z).substitution.Carrier Γ Δ) :
    boundContextArrow M bs Δ Z ≫
        substitutionArrow M ((M.stage Z).substitution.liftEnvironment σ bs) =
      (M.ctx bs ◁ substitutionArrow M σ) ≫ boundContextArrow M bs Γ Z := by
  change Environment S (M.ElemOver Z) Γ Δ at σ
  let lifted : Environment S (M.ElemOver Z) (bs ++ Γ) (bs ++ Δ) :=
    (M.stage Z).substitution.liftEnvironment σ bs
  change boundContextArrow M bs Δ Z ≫ substitutionArrow M lifted =
    (M.ctx bs ◁ substitutionArrow M σ) ≫ boundContextArrow M bs Γ Z
  apply hom_ext
  · have natural := Model.envValue_restage lifted (boundContextArrow M bs Δ Z)
      (snd _ _) (M.genericEnv (bs ++ Δ) Z)
    rw [boundContextArrow_snd, boundContextArrow_environment] at natural
    have leftEnv := natural.symm.trans
      (envValue_stageLift M σ (snd _ _) (M.genericEnv Δ Z) bs)
    have rightEnv := (M.extendEnv_restage (substitutionArrow M σ) bs
      (M.genericEnv Γ Z)).symm.trans
        (congrArg (M.extendEnv bs) (substitutionArrow_environment M σ))
    have subFst : substitutionArrow M lifted ≫ fst _ _ =
        M.tupleEnv (M.envValue lifted _ (snd _ _) (M.genericEnv (bs ++ Δ) Z)) :=
      lift_fst _ _
    calc
      (boundContextArrow M bs Δ Z ≫ substitutionArrow M lifted) ≫ fst _ _ =
          boundContextArrow M bs Δ Z ≫
            M.tupleEnv (M.envValue lifted _ (snd _ _) (M.genericEnv (bs ++ Δ) Z)) := by
        rw [Category.assoc, subFst]
      _ = M.tupleEnv (M.restage (boundContextArrow M bs Δ Z)
          (M.envValue lifted _ (snd _ _) (M.genericEnv (bs ++ Δ) Z))) :=
        (M.tupleEnv_restage _ _).symm
      _ = M.tupleEnv (M.extendEnv bs (M.envValue σ _ (snd _ _) (M.genericEnv Δ Z))) :=
        congrArg M.tupleEnv leftEnv
      _ = M.tupleEnv (M.restage (M.ctx bs ◁ substitutionArrow M σ)
          (M.extendEnv bs (M.genericEnv Γ Z))) := (congrArg M.tupleEnv rightEnv).symm
      _ = (M.ctx bs ◁ substitutionArrow M σ) ≫
          M.tupleEnv (M.extendEnv bs (M.genericEnv Γ Z)) := M.tupleEnv_restage _ _
      _ = ((M.ctx bs ◁ substitutionArrow M σ) ≫ boundContextArrow M bs Γ Z) ≫ fst _ _ := by
        rw [Category.assoc, boundContextArrow_fst]
  · simp only [Category.assoc, substitutionArrow_snd, boundContextArrow_snd,
      whiskerLeft_snd_assoc]

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafBoundSubstitution
