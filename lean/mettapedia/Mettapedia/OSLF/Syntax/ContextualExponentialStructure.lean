import Mettapedia.GSLT.Core.ContextualLadder
import Mathlib.Logic.Equiv.Basic

/-!
# Function objects in a simply typed contextual theory

An exponential at the multi-ary level represents a term with one additional
typed input by a term of function type. The representing equivalence must be
natural in all the other inputs. This interface applies to any simply typed
contextual theory, independently of a particular lambda syntax or target
category. Cartesian products and a free universal property are separate
structures.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualExponentialStructure

open Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

/-- Lift a substitution under a fresh binder using only contextual pairing. -/
def lift {S : Scwf.{u, v, w, w'}} {Γ Δ : S.Ctx}
    (σ : S.Sub Γ Δ) (A : S.Ty) :
    S.Sub (S.ext Γ A) (S.ext Δ A) :=
  S.pair (S.compS σ (S.wk A)) A (S.vz A)

theorem lift_id (S : Scwf.{u, v, w, w'}) (Γ : S.Ctx) (A : S.Ty) :
    lift (S.idS Γ) A = S.idS (S.ext Γ A) := by
  unfold lift
  rw [S.id_comp]
  calc
    S.pair (S.wk A) A (S.vz A) =
        S.pair (S.compS (S.wk A) (S.idS (S.ext Γ A))) A
          (S.tmSub (S.vz A) (S.idS (S.ext Γ A))) := by
            rw [S.comp_id, S.tmSub_id]
    _ = S.idS (S.ext Γ A) := S.pair_eta A (S.idS (S.ext Γ A))

/-- Pairing is stable under precomposition. -/
theorem pair_comp (S : Scwf.{u, v, w, w'}) {Γ Δ Θ : S.Ctx}
    (σ : S.Sub Δ Θ) (A : S.Ty) (t : S.Tm Δ A)
    (τ : S.Sub Γ Δ) :
    S.compS (S.pair σ A t) τ =
      S.pair (S.compS σ τ) A (S.tmSub t τ) := by
  calc
    S.compS (S.pair σ A t) τ =
        S.pair (S.compS (S.wk A) (S.compS (S.pair σ A t) τ)) A
          (S.tmSub (S.vz A) (S.compS (S.pair σ A t) τ)) :=
      (S.pair_eta A _).symm
    _ = S.pair (S.compS σ τ) A (S.tmSub t τ) := by
      rw [← S.comp_assoc, S.wk_pair, S.tmSub_comp, S.vz_pair]

/-- Contextual lifting respects composition, as required for a natural
representing equivalence. -/
theorem lift_comp (S : Scwf.{u, v, w, w'}) {Γ Δ Θ : S.Ctx}
    (σ : S.Sub Δ Θ) (τ : S.Sub Γ Δ) (A : S.Ty) :
    lift (S.compS σ τ) A = S.compS (lift σ A) (lift τ A) := by
  unfold lift
  rw [pair_comp]
  congr 1
  · simp only [S.comp_assoc, S.wk_pair]
  · exact (S.vz_pair _ _ _).symm

/-- A chosen contextual function structure is the multi-ary exponential
hom-set equivalence, natural under substitution of every ambient variable.
It does not assert products of types, finite limits, or an initial model. -/
structure ContextualExponential (S : Scwf.{u, v, w, w'}) where
  arrow : S.Ty → S.Ty → S.Ty
  curry : ∀ {Γ : S.Ctx} {A B : S.Ty},
    S.Tm (S.ext Γ A) B ≃ S.Tm Γ (arrow A B)
  curry_natural : ∀ {Γ Δ : S.Ctx} {A B : S.Ty}
      (σ : S.Sub Γ Δ) (body : S.Tm (S.ext Δ A) B),
    curry (S.tmSub body (lift σ A)) = S.tmSub (curry body) σ

namespace ContextualExponential

variable {S : Scwf.{u, v, w, w'}} (E : ContextualExponential S)

/-- Uncurrying is also natural. This follows from the inverse equations and
the one naturality law in the interface. -/
theorem uncurry_natural {Γ Δ : S.Ctx} {A B : S.Ty}
    (σ : S.Sub Γ Δ) (f : S.Tm Δ (E.arrow A B)) :
    (E.curry (Γ := Γ) (A := A) (B := B)).symm (S.tmSub f σ) =
      S.tmSub ((E.curry (Γ := Δ) (A := A) (B := B)).symm f)
        (lift σ A) := by
  apply (E.curry (Γ := Γ) (A := A) (B := B)).injective
  have h₁ := (E.curry (Γ := Γ) (A := A) (B := B)).apply_symm_apply
    (S.tmSub f σ)
  have h₂ := E.curry_natural σ
    ((E.curry (Γ := Δ) (A := A) (B := B)).symm f)
  have h₃ := (E.curry (Γ := Δ) (A := A) (B := B)).apply_symm_apply f
  exact h₁.trans (h₂.trans (congrArg (fun t => S.tmSub t σ) h₃)).symm

end ContextualExponential

#print axioms ContextualExponential.uncurry_natural
#print axioms lift_id
#print axioms lift_comp

end Mettapedia.OSLF.Binding.ContextualExponentialStructure
