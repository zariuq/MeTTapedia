import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Data.Set.Image

/-!
# Predicate base change and its observation boundary

An actual pullback earns existential predicate base change. A commuting
square alone does not. Conversely, predicate base change records existence
and can hold while a square retains several origins for the same pair.
It therefore does not recover the full pullback universal property.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.PredicateBaseChangeControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

theorem existential_baseChange {P A B Z : Type u}
    (top : P ⟶ B) (left : P ⟶ A) (right : B ⟶ Z) (bottom : A ⟶ Z)
    (square : IsPullback top left right bottom) (predicate : Set B) :
    bottom ⁻¹' (right '' predicate) = left '' (top ⁻¹' predicate) := by
  ext value
  constructor
  · rintro ⟨argument, holds, same⟩
    obtain ⟨origin, top_origin, left_origin⟩ :=
      Types.exists_of_isPullback square argument value same
    refine ⟨origin, ?_, left_origin⟩
    change top origin ∈ predicate
    rw [top_origin]
    exact holds
  · rintro ⟨origin, holds, rfl⟩
    exact ⟨top origin, holds, congrArg (fun arrow : P ⟶ Z => arrow origin) square.w⟩

def missingCorner : PEmpty ⟶ PUnit := TypeCat.ofHom PEmpty.elim

theorem missingCorner_commutes :
    missingCorner ≫ 𝟙 PUnit = missingCorner ≫ 𝟙 PUnit := rfl

theorem missingCorner_not_pullback :
    ¬ IsPullback missingCorner missingCorner (𝟙 PUnit) (𝟙 PUnit) := by
  intro square
  obtain ⟨origin, _, _⟩ := Types.exists_of_isPullback square PUnit.unit PUnit.unit rfl
  exact origin.elim

theorem commutativity_does_not_supply_baseChange :
    (𝟙 PUnit) ⁻¹' ((𝟙 PUnit) '' (Set.univ : Set PUnit)) ≠
      missingCorner '' (missingCorner ⁻¹' (Set.univ : Set PUnit)) := by
  intro same
  have holds : (PUnit.unit : PUnit) ∈
      (𝟙 PUnit) ⁻¹' ((𝟙 PUnit) '' (Set.univ : Set PUnit)) :=
    ⟨PUnit.unit, Set.mem_univ _, rfl⟩
  rw [same] at holds
  obtain ⟨origin, _, _⟩ := holds
  exact origin.elim

def duplicateCorner : Bool ⟶ PUnit := TypeCat.ofHom fun _ => PUnit.unit

theorem duplicateCorner_baseChange (predicate : Set PUnit) :
    (𝟙 PUnit) ⁻¹' ((𝟙 PUnit) '' predicate) =
      duplicateCorner '' (duplicateCorner ⁻¹' predicate) := by
  ext value
  cases value
  constructor
  · rintro ⟨argument, holds, _⟩
    cases argument
    exact ⟨false, holds, rfl⟩
  · rintro ⟨origin, holds, _⟩
    exact ⟨PUnit.unit, holds, rfl⟩

theorem duplicateCorner_not_pullback :
    ¬ IsPullback duplicateCorner duplicateCorner (𝟙 PUnit) (𝟙 PUnit) := by
  intro square
  have same : false = true := Types.ext_of_isPullback square rfl rfl
  contradiction

end Mettapedia.CategoryTheory.PredicateBaseChangeControls
