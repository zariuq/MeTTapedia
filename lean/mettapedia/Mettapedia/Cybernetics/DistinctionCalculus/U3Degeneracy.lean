import Mathlib.CategoryTheory.Monad.Basic

/-!
# Degeneracy of the displayed U3 re-reification signature

`dclosure_v3`, Proposition "Degeneracy of the displayed U3 signature":
the three copy-style equations reproduced from the Geometry and Economics
reflection monad force `Δ_X = η_{MX}`. Any exact-unit consumer then makes
the displayed corrector the identity.

The result is exactly those three equations, checked against Mathlib monads.
It does not apply to a different Frobenius law, and it does not construct
GE's operational reflection monad.
-/

set_option autoImplicit false

universe u v

namespace Mettapedia.Cybernetics.DistinctionCalculus.U3Degeneracy

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The three displayed U3 equations on a monad `T`, in components. -/
structure DisplayedU3 (T : CategoryTheory.Monad C) where
  /-- `Δ : T ⇒ T²`. -/
  δ : T.toFunctor ⟶ T.toFunctor ⋙ T.toFunctor
  /-- `μ Δ = 1_T`. -/
  mu_delta : ∀ X : C, δ.app X ≫ T.μ.app X = 𝟙 (T.obj X)
  /-- `Δ μ = Tμ Δ_T`. -/
  delta_mu :
    ∀ X : C,
      T.μ.app X ≫ δ.app X = δ.app (T.obj X) ≫ T.map (T.μ.app X)
  /-- `Δ η = Tη η`. -/
  delta_eta :
    ∀ X : C, T.η.app X ≫ δ.app X = T.η.app X ≫ T.map (T.η.app X)

variable {T : CategoryTheory.Monad C}

/-- Under U3, the displayed copy is the monad unit at `T X`. -/
theorem displayed_copy_is_unit (σ : DisplayedU3 T) (X : C) :
    σ.δ.app X = T.η.app (T.obj X) := by
  rw [← Category.id_comp (σ.δ.app X)]
  erw [← T.left_unit X]
  rw [Category.assoc, σ.delta_mu X, ← Category.assoc, σ.delta_eta (T.obj X),
    Category.assoc, ← T.map_comp, T.left_unit X]
  simp [Functor.id_obj, T.map_id]

/-- The displayed corrector `R(γ) = β ∘ Tγ ∘ Δ`. -/
def corrector (σ : DisplayedU3 T) {X : C} (β γ : T.obj X ⟶ X) :
    T.obj X ⟶ X :=
  σ.δ.app X ≫ T.map γ ≫ β

/-- Exact unit plus U3 makes every corrector the identity on the consumer. -/
theorem corrector_trivial (σ : DisplayedU3 T) {X : C}
    (β : T.obj X ⟶ X) (exactUnit : T.η.app X ≫ β = 𝟙 X)
    (γ : T.obj X ⟶ X) : corrector σ β γ = γ := by
  unfold corrector
  rw [displayed_copy_is_unit σ X, ← Category.assoc, ← T.η.naturality γ,
    Category.assoc, exactUnit]
  simp [Functor.id_map]

/-- Componentwise `η_{T X} : T X ⟶ T² X`. This is not the unit `η : 1 ⇒ T`. -/
def canonicalDelta (T : CategoryTheory.Monad C) :
    T.toFunctor ⟶ T.toFunctor ⋙ T.toFunctor where
  app X := T.η.app (T.obj X)
  naturality _ _ f := T.η.naturality (T.map f)

/-- Canonical insertion `η_{T(-)}` satisfies the displayed U3 equations. -/
def canonicalInsertion (T : CategoryTheory.Monad C) : DisplayedU3 T where
  δ := canonicalDelta T
  mu_delta X := T.left_unit X
  delta_mu X := T.η.naturality (T.μ.app X)
  delta_eta X := T.η.naturality (T.η.app X)

@[simp] theorem canonicalInsertion_delta (T : CategoryTheory.Monad C) (X : C) :
    (canonicalInsertion T).δ.app X = T.η.app (T.obj X) :=
  rfl

end Mettapedia.Cybernetics.DistinctionCalculus.U3Degeneracy
