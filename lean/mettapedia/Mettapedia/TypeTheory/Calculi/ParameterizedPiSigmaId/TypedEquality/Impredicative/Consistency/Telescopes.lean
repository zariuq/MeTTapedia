import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Formation

/-!
# Closed constants from their full applications

A declared constant `f : Π Θ. C` is a valid term of its declared type when
its full application to the variables of `Θ` is a valid term of `C` in `Θ`.
The partial equivalence of a dependent function type relates two functions
when their applications to related arguments are related, at every world, so
the validity of a function follows from the validity of its application to a
fresh variable, one binder at a time.

The valid parts of the declared type give the validity of the telescope and
of each partial product. A full application that computes, in the model, to a
valid term is valid.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization
open TelescopeAbstraction (closeType applyClosed liftClosed_zero)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-! ## Telescopes -/

theorem rename_applyClosed {n m k : Nat} (ρ : Ren m k) :
    ∀ (Θ : Ctx Head n) (σ : Sub Head n m) (F : Tm Head m),
      Presentation.rename ρ (applyClosed Θ σ F) =
        applyClosed Θ (fun i => Presentation.rename ρ (σ i)) (Presentation.rename ρ F)
  | .nil, _, _ => rfl
  | .snoc Θ _, σ, F => by
      simp only [applyClosed, Presentation.rename]
      rw [rename_applyClosed ρ Θ]

/-- The full application in an extended telescope applies the weakened full
application of the telescope before it to the fresh variable. -/
theorem applyClosed_snoc_ids {n : Nat} (Θ : Ctx Head n) (A : Tm Head n) (f : Tm Head 0) :
    applyClosed (.snoc Θ A) ids (liftClosed f) =
      .app (Presentation.rename wk (applyClosed Θ ids (liftClosed f))) (.var 0) := by
  rw [rename_applyClosed, rename_liftClosed]
  rfl

/-- A valid closed type with valid parts, written as a product over a
telescope, has a valid telescope and a valid codomain with valid parts. -/
theorem ValidTy.close_parts : ∀ {n : Nat} (Θ : Ctx Head n) {C : Tm Head n},
    ValidTy M .nil (closeType Θ C) → Structured M .nil (closeType Θ C) →
      ValidCtxS M Θ ∧ ValidTy M Θ C ∧ Structured M Θ C
  | _, .nil, _, valid, parts => ⟨trivial, valid, parts⟩
  | _, .snoc Θ A, C, valid, parts => by
      obtain ⟨ctx, _, partsPi⟩ := ValidTy.close_parts Θ (C := .pi A C) valid parts
      obtain ⟨⟨validA, partsA⟩, validC, partsC⟩ := partsPi
      exact ⟨⟨ctx, validA, partsA⟩, validC, partsC⟩

section Laws

variable (laws : M.Laws)
include laws

/-- A term is a valid term of a dependent function type when its application
to a fresh variable is a valid term of the codomain. -/
theorem ValidTm.of_app_var {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    {B : Tm Head (n + 1)} (validPi : ValidTy M Γ (.pi A B))
    (validApp : ValidTm M (.snoc Γ A) (.app (Presentation.rename wk t) (.var 0)) B) :
    ValidTm M Γ t (.pi A B) := by
  refine ⟨validPi, fun {_ ξ σ σ'} e {R} den => ?_⟩
  obtain ⟨_, rel⟩ := validApp
  obtain ⟨L, interp⟩ := den
  obtain ⟨P, rfl, domInterp, codInterp, _⟩ := InterpAt.pi_inv laws interp
  intro _ ξ' ρ w a b ha hab
  have domDen : Den M ξ' (Presentation.subst (fun i => Presentation.rename ρ (σ i)) A)
      (P.dom w) := by
    have interpA := domInterp w
    rw [rename_subst] at interpA
    exact ⟨L, interpA⟩
  have codDen : Den M ξ' (Presentation.subst (consSub a fun i => Presentation.rename ρ (σ i)) B)
      (P.cod w ha) := by
    have interpB := codInterp w ha
    rw [inst0_rename_subst_liftSub] at interpB
    exact ⟨L, interpB⟩
  have related := rel (EqSubst.cons (EqSubst.rename laws e w) domDen hab) codDen
  simp only [Presentation.subst, subst_consSub_rename_wk, consSub_zero] at related
  rw [rename_subst, rename_subst]
  exact related

/-- A constant, or any closed term, is a valid term of its closed type when its
full application to the variables of the telescope is valid. -/
theorem ValidTm.close : ∀ {n : Nat} (Θ : Ctx Head n) {C : Tm Head n} {f : Tm Head 0},
    ValidTy M .nil (closeType Θ C) → Structured M .nil (closeType Θ C) →
      ValidTm M Θ (applyClosed Θ ids (liftClosed f)) C → ValidTm M .nil f (closeType Θ C)
  | _, .nil, _, f, _, _, valid => by
      rw [show applyClosed (.nil : Ctx Head 0) ids (liftClosed f) = liftClosed f from rfl,
        liftClosed_zero] at valid
      exact valid
  | _, .snoc Θ A, C, f, validType, partsType, valid => by
      obtain ⟨_, validPi, _⟩ := ValidTy.close_parts Θ (C := .pi A C) validType partsType
      refine ValidTm.close Θ (C := .pi A C) validType partsType
        (ValidTm.of_app_var laws validPi ?_)
      rw [← applyClosed_snoc_ids]
      exact valid

end Laws

/-- A term is valid when, under every substitution, it computes in the model to
an instance of a valid term. -/
theorem ValidTm.of_red {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (red : ∀ {m : Nat} (σ : Sub Head n m),
      WhRed M.rules M.roles (Presentation.subst σ t) (Presentation.subst σ u))
    (valid : ValidTm M Γ u A) : ValidTm M Γ t A := by
  obtain ⟨validA, rel⟩ := valid
  refine ⟨validA, fun {_ ξ σ σ'} e {R} den => ?_⟩
  exact Den.expandLeft den (red σ) (Den.expandRight den (red σ') (rel e den))

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
