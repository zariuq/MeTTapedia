import Mettapedia.GSLT.Topos.ConstructivePresheafDependentFunctions

/-!
# Dependent result families of typed arguments

A relation on argument/result pairs determines a result family over the actual
supported argument objects. A predicate-preserving operation curries into a
dependent section. These objects retain values and typing support, not separate
histories of proofs of that support.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q H : C ⥤ Type u}

def resultFamily (arguments : Subfunctor P)
    (results : Subfunctor (FunctorToTypes.prod P Q)) : arguments.toFunctor.Elements ⥤ Type u where
  obj X := {result : Q.obj X.1 // (X.2.val, result) ∈ results.obj X.1}
  map {X Y} step := TypeCat.ofHom (fun result =>
    ⟨Q.map step.val result.val, by
      have held := results.map step.val result.property
      change (P.map step.val X.2.val, Q.map step.val result.val) ∈ results.obj Y.1 at held
      have argument_same := congrArg Subtype.val step.property
      change P.map step.val X.2.val = Y.2.val at argument_same
      rw [argument_same] at held
      exact held⟩)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro result
    apply Subtype.ext
    exact Q.map_id_apply X.1 result.val
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro result
    apply Subtype.ext
    exact Q.map_comp_apply first.val second.val result.val

def supportedOperation (operation : NatTrans (FunctorToTypes.prod P H) Q)
    (arguments : Subfunctor P) (parameters : Subfunctor H)
    (results : Subfunctor (FunctorToTypes.prod P Q))
    (preserves : ∀ X argument parameter, argument ∈ arguments.obj X →
      parameter ∈ parameters.obj X → (argument, operation.app X (argument,parameter)) ∈ results.obj X) :
    NatTrans (overElements arguments.toFunctor parameters.toFunctor) (resultFamily arguments results) where
  app X := TypeCat.ofHom (fun parameter =>
    ⟨operation.app X.1 (X.2.val,parameter.val),
      preserves X.1 X.2.val parameter.val X.2.property parameter.property⟩)
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    intro parameter
    apply Subtype.ext
    have natural := congrArg (fun f => f (X.2.val,parameter.val)) (operation.naturality step.val)
    change operation.app Y.1 (P.map step.val X.2.val, H.map step.val parameter.val) =
      Q.map step.val (operation.app X.1 (X.2.val,parameter.val)) at natural
    have argument_same := congrArg Subtype.val step.property
    change P.map step.val X.2.val = Y.2.val at argument_same
    rw [argument_same] at natural
    exact natural

def supportedDependentFunction (operation : NatTrans (FunctorToTypes.prod P H) Q)
    (arguments : Subfunctor P) (parameters : Subfunctor H)
    (results : Subfunctor (FunctorToTypes.prod P Q))
    (preserves : ∀ X argument parameter, argument ∈ arguments.obj X →
      parameter ∈ parameters.obj X → (argument, operation.app X (argument,parameter)) ∈ results.obj X) :
    NatTrans parameters.toFunctor (dependentFunctions arguments.toFunctor (resultFamily arguments results)) :=
  curry (supportedOperation operation arguments parameters results preserves)

theorem supportedDependentFunction_apply
    (operation : NatTrans (FunctorToTypes.prod P H) Q)
    (arguments : Subfunctor P) (parameters : Subfunctor H)
    (results : Subfunctor (FunctorToTypes.prod P Q))
    (preserves : ∀ X argument parameter, argument ∈ arguments.obj X →
      parameter ∈ parameters.obj X → (argument, operation.app X (argument,parameter)) ∈ results.obj X)
    {X Y : C} (step : X ⟶ Y) (parameter : parameters.obj X) (argument : arguments.obj Y) :
    ((supportedDependentFunction operation arguments parameters results preserves).app X parameter
      |>.app Y step argument).val = operation.app Y (argument.val, H.map step parameter.val) := rfl

#print axioms resultFamily
#print axioms supportedOperation
#print axioms supportedDependentFunction

end Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
