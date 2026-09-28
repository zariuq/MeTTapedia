import Mettapedia.GSLT.Topos.ConstructivePresheafFunctions

/-!
# Predicates on internal functions

A function preserves predicates when it does so at every future restriction.
Currying preserves this condition exactly when the uncurried operation maps
the product predicate into the result predicate. The statement is a
biconditional on standard natural transformations and subfunctors.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf

open CategoryTheory
open scoped ConstructivePresheaf

universe u
variable {C : Type u} [Category.{u} C]
variable {F G H : C ⥤ Type u}

def productPredicate (first : Subfunctor F) (second : Subfunctor G) :
    Subfunctor (FunctorToTypes.prod F G) where
  obj X := {pair | pair.1 ∈ first.obj X ∧ pair.2 ∈ second.obj X}
  map restriction _ held := ⟨first.map restriction held.1, second.map restriction held.2⟩

def functionPredicate (source : Subfunctor F) (target : Subfunctor G) :
    Subfunctor (functions F G) where
  obj X := {value | ∀ (Y : C) (restriction : X ⟶ Y) (argument : F.obj Y),
    argument ∈ source.obj Y → value.app Y restriction argument ∈ target.obj Y}
  map {X Y} restriction := by
    intro value held Z further argument member
    exact held Z (restriction ≫ further) argument member

theorem functionPredicate_elimination (source : Subfunctor F) (target : Subfunctor G)
    (X : C) (value : (functions F G).obj X) (held : value ∈ (functionPredicate source target).obj X)
    (argument : F.obj X) (member : argument ∈ source.obj X) :
    value.app X (𝟙 X) argument ∈ target.obj X := held X (𝟙 X) argument member

/-- A parameter preserves the function predicate precisely when the uncurried
operation preserves the product of argument and parameter predicates. -/
theorem curry_preserves_predicates_iff
    (operation : NatTrans (FunctorToTypes.prod F H) G)
    (source : Subfunctor F) (target : Subfunctor G) (parameters : Subfunctor H) :
    parameters ≤ preimage (curryFunction operation) (functionPredicate source target) ↔
      productPredicate source parameters ≤ preimage operation target := by
  constructor
  · intro held X pair member
    have result := held X member.2 X (𝟙 X) pair.1 member.1
    change operation.app X (pair.1, H.map (𝟙 X) pair.2) ∈ target.obj X at result
    rw [H.map_id_apply] at result
    exact result
  · intro held X parameter member Y restriction argument inSource
    exact held Y ⟨inSource, parameters.map restriction member⟩

theorem uncurry_preserves_predicates_iff
    (operation : NatTrans H (functions F G))
    (source : Subfunctor F) (target : Subfunctor G) (parameters : Subfunctor H) :
    parameters ≤ preimage operation (functionPredicate source target) ↔
      productPredicate source parameters ≤ preimage (uncurryFunction operation) target := by
  have equivalence := curry_preserves_predicates_iff
    (uncurryFunction operation) source target parameters
  rw [curry_uncurryFunction] at equivalence
  exact equivalence

theorem evaluation_preserves_predicates (source : Subfunctor F) (target : Subfunctor G) :
    productPredicate source (functionPredicate source target) ≤ preimage (evaluate F G) target := by
  intro X pair member
  exact member.2 X (𝟙 X) pair.1 member.1

end Mettapedia.GSLT.Topos.ConstructivePresheaf
