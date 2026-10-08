import Mettapedia.CategoryTheory.RelativeClosedConjunctiveAdjunction
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# The conjunctive construction monad and its complete fold readings

The monad is induced by the actual free-forgetful adjunction. Its underlying
theory contains the added vocabulary; multiplication is the independently
interpreted counit, which folds the second added truth and conjunction into
the first operations while retaining every old object and arrow.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctive.Construction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core
open RelativeClosedSyntax GeneratedCategory
open ConjunctiveClosedTheory HomEquivalence FreeForgetful

universe k

private instance identity_closed {C : Type k} [Category.{k} C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] : MonoidalClosedFunctor (𝟭 C) :=
  cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts _ Adjunction.id

def monad : Monad (BicategoryIsoClasses LambdaTheory.{k,k}) := FreeForgetful.adjunction.toMonad

theorem underlying_object (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    monad.obj source = ClosedTheoryIsoClasses.of (freeObject source.original).closed := rfl

theorem underlying_map {source target : BicategoryIsoClasses LambdaTheory.{k,k}} (mapping : source ⟶ target) :
    monad.map mapping = ConjunctiveClosedTheory.forget.map (freeMap mapping) := rfl

theorem unit_component (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    monad.η.app source = FreeForgetful.unit source := FreeForgetful.unit_app source

def multiplicationMap (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    LambdaTheoryMap (freeObject (freeObject source.original).closed).closed (freeObject source.original).closed :=
  (counitMap (freeObject source.original)).underlying

theorem multiplication_component (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    monad.μ.app source = ClosedTheoryIsoClasses.classOf (multiplicationMap source) := rfl

theorem folds_proposition (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    (multiplicationMap source).functor.obj
        (NativePredicates.operations (C := (freeObject source.original).closed.Obj)).proposition =
      (NativePredicates.operations (C := source.original.Obj)).proposition :=
  ModelReadout.proposition_read (𝟭 (freeObject source.original).closed.Obj)
    (freeObject source.original).operations (freeObject source.original).laws

theorem folds_truth (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    HEq ((multiplicationMap source).functor.map
      (NativePredicates.operations (C := (freeObject source.original).closed.Obj)).truth)
      (NativePredicates.operations (C := source.original.Obj)).truth :=
  ModelReadout.truth_heq (𝟭 (freeObject source.original).closed.Obj)
    (freeObject source.original).operations (freeObject source.original).laws

theorem folds_conjunction (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    HEq ((multiplicationMap source).functor.map
      (NativePredicates.operations (C := (freeObject source.original).closed.Obj)).conjunction)
      (NativePredicates.operations (C := source.original.Obj)).conjunction :=
  ModelReadout.conjunction_heq (𝟭 (freeObject source.original).closed.Obj)
    (freeObject source.original).operations (freeObject source.original).laws

theorem retains_old_object (source : BicategoryIsoClasses LambdaTheory.{k,k})
    (object : (freeObject source.original).closed.Obj) :
    (multiplicationMap source).functor.obj
      (baseObject (nativeSignature (C := (freeObject source.original).closed.Obj)) object) = object :=
  RelativeClosedSyntax.Interpretation.functor_base_object
    (ModelReadout.model (𝟭 (freeObject source.original).closed.Obj)
      (freeObject source.original).operations (freeObject source.original).laws).meanings
    (ModelReadout.model (𝟭 (freeObject source.original).closed.Obj)
      (freeObject source.original).operations (freeObject source.original).laws).realization object

theorem retains_old_diagram (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    baseFunctor (nativeSignature (C := (freeObject source.original).closed.Obj)) ⋙
        (multiplicationMap source).functor = 𝟭 (freeObject source.original).closed.Obj :=
  RelativeClosedSyntax.Interpretation.functor_base
    (ModelReadout.model (𝟭 (freeObject source.original).closed.Obj)
      (freeObject source.original).operations (freeObject source.original).laws).meanings
    (ModelReadout.model (𝟭 (freeObject source.original).closed.Obj)
      (freeObject source.original).operations (freeObject source.original).laws).realization

theorem retains_old_arrow (source : BicategoryIsoClasses LambdaTheory.{k,k})
    {before after : (freeObject source.original).closed.Obj} (arrow : before ⟶ after) :
    (multiplicationMap source).functor.map
        (baseArrow (signature := nativeSignature (C := (freeObject source.original).closed.Obj)) arrow) = arrow :=
  RelativeClosedSyntax.Interpretation.functor_base_arrow
    (ModelReadout.model (𝟭 (freeObject source.original).closed.Obj)
      (freeObject source.original).operations (freeObject source.original).laws).meanings
    (ModelReadout.model (𝟭 (freeObject source.original).closed.Obj)
      (freeObject source.original).operations (freeObject source.original).laws).realization arrow

theorem right_unit (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    monad.map (monad.η.app source) ≫ monad.μ.app source = 𝟙 (monad.obj source) := monad.right_unit source

theorem left_unit (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    monad.η.app (monad.obj source) ≫ monad.μ.app source = 𝟙 (monad.obj source) := monad.left_unit source

theorem associativity (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    monad.map (monad.μ.app source) ≫ monad.μ.app source =
      monad.μ.app (monad.obj source) ≫ monad.μ.app source := monad.assoc source

end Mettapedia.CategoryTheory.RelativeClosedConjunctive.Construction
