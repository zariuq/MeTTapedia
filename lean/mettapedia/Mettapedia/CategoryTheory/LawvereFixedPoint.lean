import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mettapedia.Logic.Diagonal.Lawvere

/-!
# Lawvere's fixed-point theorem in a cartesian closed category

Lawvere, *Diagonal arguments and cartesian closed categories* (1969).  In a
category with chosen finite products, a morphism `φ : A ⊗ A ⟶ Y` is *weakly
point-surjective* when every morphism `g : A ⟶ Y` is represented at points by a
point `a` of `A`: `lift x a ≫ φ = x ≫ g` for every point `x`.  Then every
endomorphism of `Y` has a fixed point (`lawvere`), and a fixed-point-free
endomorphism rules out every weakly point-surjective map into `Y`
(`not_weaklyPointSurjective`).

With exponentials (`MonoidalClosed`, which Mathlib now uses in place of the
deprecated `CartesianClosed`), a morphism `e : A ⟶ (A ⟹ Y)` is
*point-surjective* when every point of `A ⟹ Y` factors through it.  Its
uncurried form is then weakly point-surjective
(`weaklyPointSurjective_uncurry`), so the fixed-point theorem holds in the
closed form (`lawvere_closed`, `not_pointSurjective_of_fixedPointFree`).

Controls in the category of types:

* negative: Boolean negation has no fixed point, so no morphism
  `A ⊗ A ⟶ Bool` is weakly point-surjective, and no `A ⟶ (A ⟹ Bool)` is
  point-surjective (`bool_not_weaklyPointSurjective`,
  `bool_not_pointSurjective`): the categorical form of Cantor and Tarski;
* positive: onto the terminal object the unique morphism is weakly
  point-surjective (`unit_weaklyPointSurjective`), where every endomorphism
  has its fixed point;
* the type-level theorem is the instance in the category of types: a
  surjective `run : A → A → Y` gives a weakly point-surjective morphism
  (`weaklyPointSurjective_of_surjective`), and the categorical theorem returns
  the fixed point of `Mettapedia.Logic.Diagonal.lawvere`
  (`lawvere_types`).
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Mettapedia.CategoryTheory.LawvereFixedPoint

universe v u

section Products

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- **Weak point-surjectivity** (Lawvere 1969).  The left factor is the
argument and the right factor the code: every `g : A ⟶ Y` has a code point `a`
with `lift x a ≫ φ = x ≫ g` at every argument point `x`. -/
def WeaklyPointSurjective {A Y : C} (φ : A ⊗ A ⟶ Y) : Prop :=
  ∀ g : A ⟶ Y, ∃ a : 𝟙_ C ⟶ A, ∀ x : 𝟙_ C ⟶ A, lift x a ≫ φ = x ≫ g

/-- A fixed point of an endomorphism is a point it fixes. -/
def HasFixedPoint {Y : C} (t : Y ⟶ Y) : Prop :=
  ∃ y : 𝟙_ C ⟶ Y, y ≫ t = y

/-- **Lawvere's fixed-point theorem.**  A weakly point-surjective morphism into
`Y` forces every endomorphism of `Y` to have a fixed point: the diagonal
composite `lift (𝟙 A) (𝟙 A) ≫ φ ≫ t` is represented by a point `a`, and
`lift a a ≫ φ` is fixed. -/
theorem lawvere {A Y : C} {φ : A ⊗ A ⟶ Y} (surjective : WeaklyPointSurjective φ)
    (t : Y ⟶ Y) : HasFixedPoint t := by
  obtain ⟨a, represents⟩ := surjective (lift (𝟙 A) (𝟙 A) ≫ φ ≫ t)
  refine ⟨lift a a ≫ φ, ?_⟩
  calc (lift a a ≫ φ) ≫ t = a ≫ lift (𝟙 A) (𝟙 A) ≫ φ ≫ t := by
        simp only [Category.assoc, comp_lift_assoc, Category.comp_id]
    _ = lift a a ≫ φ := (represents a).symm

/-- **Contrapositive.**  A fixed-point-free endomorphism of `Y` rules out every
weakly point-surjective morphism into `Y`. -/
theorem not_weaklyPointSurjective {A Y : C} {t : Y ⟶ Y}
    (free : ∀ y : 𝟙_ C ⟶ Y, y ≫ t ≠ y) (φ : A ⊗ A ⟶ Y) : ¬ WeaklyPointSurjective φ := by
  intro surjective
  obtain ⟨y, fixed⟩ := lawvere surjective t
  exact free y fixed

end Products

section Closed

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- **Point-surjectivity** of a morphism into an exponential: every point of
`A ⟹ Y` factors through it. -/
def PointSurjective {A Y : C} [Closed A] (e : A ⟶ (ihom A).obj Y) : Prop :=
  ∀ h : 𝟙_ C ⟶ (ihom A).obj Y, ∃ a : 𝟙_ C ⟶ A, a ≫ e = h

/-- A point-surjective morphism into an exponential has a weakly
point-surjective uncurried form: the code of `g` is a point whose composite
with `e` is the name of `g`. -/
theorem weaklyPointSurjective_uncurry {A Y : C} [Closed A] {e : A ⟶ (ihom A).obj Y}
    (surjective : PointSurjective e) : WeaklyPointSurjective (uncurry e) := by
  intro g
  obtain ⟨a, factors⟩ := surjective (curry ((ρ_ A).hom ≫ g))
  refine ⟨a, fun x => ?_⟩
  have named : A ◁ a ≫ uncurry e = (ρ_ A).hom ≫ g := by
    rw [← uncurry_natural_left, factors, uncurry_curry]
  calc lift x a ≫ uncurry e = lift x (𝟙 (𝟙_ C)) ≫ A ◁ a ≫ uncurry e := by
        rw [lift_whiskerLeft_assoc, Category.id_comp]
    _ = lift x (𝟙 (𝟙_ C)) ≫ (ρ_ A).hom ≫ g := by rw [named]
    _ = x ≫ g := by rw [lift_rightUnitor_hom_assoc]

/-- **Lawvere's fixed-point theorem, closed form.** -/
theorem lawvere_closed {A Y : C} [Closed A] {e : A ⟶ (ihom A).obj Y}
    (surjective : PointSurjective e) (t : Y ⟶ Y) : HasFixedPoint t :=
  lawvere (weaklyPointSurjective_uncurry surjective) t

/-- **Contrapositive, closed form.** -/
theorem not_pointSurjective_of_fixedPointFree {A Y : C} [Closed A] {t : Y ⟶ Y}
    (free : ∀ y : 𝟙_ C ⟶ Y, y ≫ t ≠ y) (e : A ⟶ (ihom A).obj Y) : ¬ PointSurjective e :=
  fun surjective => not_weaklyPointSurjective free _ (weaklyPointSurjective_uncurry surjective)

end Closed

/-! ## Controls in the category of types -/

section Types

/-- Boolean negation as an endomorphism in the category of types. -/
def boolNot : (Bool : Type) ⟶ Bool := TypeCat.ofHom fun b => !b

/-- Boolean negation fixes no point. -/
theorem boolNot_fixedPointFree : ∀ y : 𝟙_ Type ⟶ (Bool : Type), y ≫ boolNot ≠ y := by
  intro y fixed
  have atUnit := congrArg (fun morphism : 𝟙_ Type ⟶ (Bool : Type) => morphism PUnit.unit) fixed
  exact Mettapedia.Logic.Diagonal.bool_not_fixedPointFree (y PUnit.unit) atUnit

/-- **Negative control (Cantor and Tarski, categorically).**  No morphism
`A ⊗ A ⟶ Bool` is weakly point-surjective. -/
theorem bool_not_weaklyPointSurjective {A : Type} (φ : A ⊗ A ⟶ (Bool : Type)) :
    ¬ WeaklyPointSurjective φ :=
  not_weaklyPointSurjective boolNot_fixedPointFree φ

/-- No morphism `A ⟶ (A ⟹ Bool)` is point-surjective. -/
theorem bool_not_pointSurjective {A : Type} (e : A ⟶ (ihom A).obj (Bool : Type)) :
    ¬ PointSurjective e :=
  not_pointSurjective_of_fixedPointFree boolNot_fixedPointFree e

/-- **Positive control.**  Onto the terminal object the unique morphism is
weakly point-surjective. -/
theorem unit_weaklyPointSurjective :
    WeaklyPointSurjective (toUnit (𝟙_ Type ⊗ 𝟙_ Type : Type)) := by
  intro g
  exact ⟨𝟙 _, fun x => toUnit_unique _ _⟩

/-- A surjective code map of types is weakly point-surjective as a morphism of
the category of types. -/
theorem weaklyPointSurjective_of_surjective {A Y : Type} {run : A → A → Y}
    (surjective : Function.Surjective run) :
    WeaklyPointSurjective (TypeCat.ofHom fun pair : A ⊗ A => run pair.2 pair.1) := by
  intro g
  obtain ⟨code, runs⟩ := surjective fun argument => g argument
  refine ⟨TypeCat.ofHom fun _ => code, fun x => ?_⟩
  ext point
  change run code (x point) = g (x point)
  rw [runs]

/-- **The type-level theorem as an instance.**  The categorical theorem,
applied in the category of types, yields a fixed point of any function on the
values of a surjective code map. -/
theorem lawvere_types {A Y : Type} {run : A → A → Y} (surjective : Function.Surjective run)
    (f : Y → Y) : ∃ value, f value = value := by
  obtain ⟨y, fixed⟩ := lawvere (weaklyPointSurjective_of_surjective surjective)
    (TypeCat.ofHom f)
  exact ⟨y PUnit.unit, congrArg (fun morphism : 𝟙_ Type ⟶ Y => morphism PUnit.unit) fixed⟩

end Types

end Mettapedia.CategoryTheory.LawvereFixedPoint
