import Mettapedia.GSLT.Topos.ConstructivePresheafFunctionPredicates

/-!
# Function predicates with argument-dependent results

The result condition is a subfunctor of argument/result pairs. A function
must satisfy it at every future restriction. This is a predicate on the
ordinary internal function object, not a construction of dependent product
objects in every slice category.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf

open CategoryTheory
open scoped ConstructivePresheaf

universe u
variable {C : Type u} [Category.{u} C]
variable {F G H : C ⥤ Type u}

def dependentFunctionPredicate (source : Subfunctor F)
    (results : Subfunctor (FunctorToTypes.prod F G)) : Subfunctor (functions F G) where
  obj X := {value | ∀ (Y : C) (restriction : X ⟶ Y) (argument : F.obj Y),
    argument ∈ source.obj Y → (argument, value.app Y restriction argument) ∈ results.obj Y}
  map {X Y} restriction := by
    intro value held Z further argument member
    exact held Z (restriction ≫ further) argument member

/-- Retain the argument alongside the result of a natural operation. -/
def operationWithArgument (operation : NatTrans (FunctorToTypes.prod F H) G) :
    NatTrans (FunctorToTypes.prod F H) (FunctorToTypes.prod F G) where
  app X := TypeCat.ofHom (fun pair => (pair.1, operation.app X pair))
  naturality X Y restriction := by
    apply ConcreteCategory.hom_ext
    intro pair
    apply Prod.ext
    · rfl
    · exact congrArg (fun h : (FunctorToTypes.prod F H).obj X ⟶ G.obj Y => h pair)
        (operation.naturality restriction)

theorem curry_preserves_dependent_predicates_iff
    (operation : NatTrans (FunctorToTypes.prod F H) G)
    (source : Subfunctor F) (results : Subfunctor (FunctorToTypes.prod F G))
    (parameters : Subfunctor H) :
    parameters ≤ preimage (curryFunction operation) (dependentFunctionPredicate source results) ↔
      productPredicate source parameters ≤ preimage (operationWithArgument operation) results := by
  constructor
  · intro held X pair member
    have result := held X member.2 X (𝟙 X) pair.1 member.1
    change (pair.1, operation.app X (pair.1, H.map (𝟙 X) pair.2)) ∈ results.obj X at result
    rw [H.map_id_apply] at result
    exact result
  · intro held X parameter member Y restriction argument inSource
    exact held Y (x := (argument, H.map restriction parameter))
      ⟨inSource, parameters.map restriction member⟩

theorem dependent_function_elimination (source : Subfunctor F)
    (results : Subfunctor (FunctorToTypes.prod F G)) (X : C)
    (value : (functions F G).obj X)
    (held : value ∈ (dependentFunctionPredicate source results).obj X)
    (argument : F.obj X) (member : argument ∈ source.obj X) :
    (argument, value.app X (𝟙 X) argument) ∈ results.obj X :=
  held X (𝟙 X) argument member

end Mettapedia.GSLT.Topos.ConstructivePresheaf
