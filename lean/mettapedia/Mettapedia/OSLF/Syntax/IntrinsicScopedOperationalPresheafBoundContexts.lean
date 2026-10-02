import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafSubstitution
import Mettapedia.OSLF.Syntax.CategoricalContextualEquationSoundness

/-!
# Ordered binder-local contexts of generalized operational premises

An ordered binder list extends the ordinary environment in front of the
ambient context and leaves the generalized stage parameter at the end. The
actual tuple of this environment supplies the arrow evaluating a bound premise.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafBoundContexts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open CategoricalBindingModel

universe u v
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} (M : Model S D)

/-- The full ordered binder and ordinary context together with the same stage parameter. -/
def boundContextArrow (bs Γ : Ctx S) (Z : D) :
    M.ctx bs ⊗ (M.ctx Γ ⊗ Z) ⟶ M.ctx (bs ++ Γ) ⊗ Z :=
  lift (M.tupleEnv (M.extendEnv bs (M.genericEnv Γ Z))) (snd _ _ ≫ snd _ _)

@[simp] theorem boundContextArrow_snd (bs Γ : Ctx S) (Z : D) :
    boundContextArrow M bs Γ Z ≫ snd _ _ = snd _ _ ≫ snd _ _ := lift_snd _ _

/-- Reading a natural bound-premise value uses the actual extended ordinary environment. -/
theorem boundContextArrow_value (bs Γ : Ctx S) {Z : D} {s : S.Srt}
    (value : M.ElemOver Z (bs ++ Γ) s) :
    boundContextArrow M bs Γ Z ≫ M.elemValue value =
      value.value (M.ctx bs ⊗ (M.ctx Γ ⊗ Z)) (snd _ _ ≫ snd _ _)
        (M.extendEnv bs (M.genericEnv Γ Z)) :=
  (M.value_eq_generic value _ (snd _ _ ≫ snd _ _)
    (M.extendEnv bs (M.genericEnv Γ Z))).symm

/-- Every old ordinary variable stays behind the binder prefix. -/
theorem boundContextArrow_old (bs Γ : Ctx S) (Z : D) {s : S.Srt} (var : Var Γ s) :
    boundContextArrow M bs Γ Z ≫ fst _ _ ≫ projectVar M.sort (weakenVar bs var) =
      snd _ _ ≫ fst _ _ ≫ projectVar M.sort var := by
  rw [boundContextArrow, lift_fst_assoc, M.tupleEnv_projectVar, M.extendEnv_old]
  rfl

/-- The generic ordinary context commutes with every map of generalized stages. -/
theorem genericEnv_restage (Γ : Ctx S) {Z Z' : D} (h : Z' ⟶ Z) :
    M.restage (M.ctx Γ ◁ h) (M.genericEnv Γ Z) = M.genericEnv Γ Z' := by
  funext sort var
  change (M.ctx Γ ◁ h) ≫ fst _ _ ≫ projectVar M.sort var = fst _ _ ≫ projectVar M.sort var
  rw [whiskerLeft_fst_assoc]

/-- Binder-local context arrows commute with arbitrary changes of the stage parameter. -/
theorem boundContextArrow_restage (bs Γ : Ctx S) {Z Z' : D} (h : Z' ⟶ Z) :
    (M.ctx bs ◁ (M.ctx Γ ◁ h)) ≫ boundContextArrow M bs Γ Z =
      boundContextArrow M bs Γ Z' ≫ (M.ctx (bs ++ Γ) ◁ h) := by
  apply hom_ext
  · rw [Category.assoc, boundContextArrow, lift_fst]
    rw [Category.assoc, whiskerLeft_fst, boundContextArrow, lift_fst]
    exact (M.tupleEnv_restage (M.ctx bs ◁ (M.ctx Γ ◁ h))
      (M.extendEnv bs (M.genericEnv Γ Z))).symm.trans
        (congrArg M.tupleEnv ((M.extendEnv_restage (M.ctx Γ ◁ h) bs
          (M.genericEnv Γ Z)).symm.trans
            (congrArg (M.extendEnv bs) (genericEnv_restage M Γ h))))
  · rw [Category.assoc, boundContextArrow_snd, whiskerLeft_snd_assoc]
    rw [whiskerLeft_snd]
    rw [Category.assoc, whiskerLeft_snd]
    simpa only [Category.assoc] using
      (congrArg (· ≫ h) (boundContextArrow_snd M bs Γ Z')).symm

/-- Weakening the captured ambient identity under a premise binder list reads
precisely the old ordinary context through the product projection. -/
theorem weakenedAmbient_value (bs Γ : Ctx S) (Z : D) :
    Model.envValue
        (SemanticContextualMetavariables.weakenEnvironment (M.stage Z) bs
          (fun _ var => (M.stage Z).substitution.injectVar var :
            BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier Γ Γ))
        (M.ctx bs ⊗ (M.ctx Γ ⊗ Z)) (snd _ _ ≫ snd _ _)
        (M.extendEnv bs (M.genericEnv Γ Z)) =
      M.restage (snd _ _) (M.genericEnv Γ Z) := by
  funext sort var
  change M.extendEnv bs (M.genericEnv Γ Z) sort (weakenVar bs var) =
    snd _ _ ≫ M.genericEnv Γ Z sort var
  exact M.extendEnv_old bs (M.genericEnv Γ Z) var

/-- Captured metavariable bodies under any ordered premise binders retain
their values and are restaged through the same ambient projection. -/
theorem captureBody_underBinders (bs Γ : Ctx S) {Z : D} {dependencies : Ctx S} {s : S.Srt}
    (body : M.ElemOver Z (dependencies ++ Γ) s) :
    M.captureBody body (snd _ _ ≫ snd _ _)
        (Model.envValue
          (SemanticContextualMetavariables.weakenEnvironment (M.stage Z) bs
            (fun _ var => (M.stage Z).substitution.injectVar var :
              BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier Γ Γ))
          (M.ctx bs ⊗ (M.ctx Γ ⊗ Z)) (snd _ _ ≫ snd _ _)
          (M.extendEnv bs (M.genericEnv Γ Z))) =
      M.restageElem (snd _ _) (M.captureBody body (snd _ _) (M.genericEnv Γ Z)) := by
  rw [weakenedAmbient_value]
  exact M.captureBody_restage body (snd _ _) (M.genericEnv Γ Z) (snd _ _)

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafBoundContexts
