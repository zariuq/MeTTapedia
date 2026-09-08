import Mathlib.CategoryTheory.Yoneda

/-!
# Natural reducts of global points require injective point transport

For a functor `F : C ⥤ D`, a chosen point `point : d ⟶ F.obj c` transports
each arrow `σ : c ⟶ X` to `point ≫ F.map σ`. A natural transformation in the
reverse direction, from `D(d, F(-))` to `C(c, -)`, must recover `σ` whenever
its component at `c` takes `point` to the identity.

The identity condition follows when the endomorphisms of `c` form a
subsingleton, in particular when `c` is terminal. Consequently a collision
between transported global points rules out every such natural reduct.
No satisfaction relation or choice of formulas is needed for this obstruction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.GlobalPointReduct

open CategoryTheory
open Opposite

universe v u w

variable {C : Type u} [Category.{v} C]
variable {D : Type w} [Category.{v} D]
variable {F : C ⥤ D} {c : C} {d : D}

/-- Naturality determines the reduct on every transported point from its
value at the chosen point. -/
theorem app_postcompose
    (reduct : F ⋙ coyoneda.obj (op d) ⟶ coyoneda.obj (op c))
    (point : d ⟶ F.obj c) {X : C} (σ : c ⟶ X) :
    reduct.app X (point ≫ F.map σ) = reduct.app c point ≫ σ := by
  exact reduct.naturality_apply σ point

/-- A natural reduct taking the chosen point to the identity is a left
inverse to point transport at every object. -/
theorem leftInverse_of_app_eq_id
    (reduct : F ⋙ coyoneda.obj (op d) ⟶ coyoneda.obj (op c))
    (point : d ⟶ F.obj c)
    (identity : reduct.app c point = 𝟙 c) (X : C) :
    Function.LeftInverse (reduct.app X)
      (fun σ : c ⟶ X => point ≫ F.map σ) := by
  intro σ
  rw [app_postcompose reduct point σ, identity, Category.id_comp]

/-- If the base object has only one endomorphism, every natural reduct is
automatically a left inverse to point transport. -/
theorem leftInverse [Subsingleton (c ⟶ c)]
    (reduct : F ⋙ coyoneda.obj (op d) ⟶ coyoneda.obj (op c))
    (point : d ⟶ F.obj c) (X : C) :
    Function.LeftInverse (reduct.app X)
      (fun σ : c ⟶ X => point ≫ F.map σ) :=
  leftInverse_of_app_eq_id reduct point (Subsingleton.elim _ _) X

/-- A natural global-point reduct requires point transport to be injective. -/
theorem pointTransport_injective [Subsingleton (c ⟶ c)]
    (reduct : F ⋙ coyoneda.obj (op d) ⟶ coyoneda.obj (op c))
    (point : d ⟶ F.obj c) (X : C) :
    Function.Injective (fun σ : c ⟶ X => point ≫ F.map σ) :=
  (leftInverse reduct point X).injective

/-- A pair of distinct global points with the same transport rules out
every natural reduct for this functor and chosen point. -/
theorem no_reduct_of_collision [Subsingleton (c ⟶ c)]
    (point : d ⟶ F.obj c) {X : C} (left right : c ⟶ X)
    (different : left ≠ right)
    (collision : point ≫ F.map left = point ≫ F.map right) :
    ¬ Nonempty (F ⋙ coyoneda.obj (op d) ⟶ coyoneda.obj (op c)) := by
  rintro ⟨reduct⟩
  exact different (pointTransport_injective reduct point X collision)

#print axioms app_postcompose
#print axioms leftInverse_of_app_eq_id
#print axioms leftInverse
#print axioms pointTransport_injective
#print axioms no_reduct_of_collision

end Mettapedia.TypeTheory.GlobalPointReduct
