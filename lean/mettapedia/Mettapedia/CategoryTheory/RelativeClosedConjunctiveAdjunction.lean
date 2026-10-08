import Mettapedia.CategoryTheory.RelativeClosedConjunctiveHomEquivalence
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The free-forgetful adjunction for the conjunctive stratum

The free object is the actual generated finite-limit closed category with
its independently declared truth and conjunction. Its map action is obtained
by extension into the next generated theory. Complete base/declaration
comparison proves its identity and composition laws. The independently
constructed restriction/extension correspondence is natural in both
arguments and earns the actual adjunction, unit, counit and triangle laws.

The category retains all theory objects and identifies only weak maps through
compatible natural isomorphisms. This is one logical stratum, not a claim
about modal or structural generators.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctive.FreeForgetful

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core
open ConjunctiveClosedTheory HomEquivalence

universe k

def unit (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    source ⟶ ConjunctiveClosedTheory.forget.obj (freeObject source.original) :=
  ClosedTheoryIsoClasses.classOf (unitMap source.original)

def freeMap {source target : BicategoryIsoClasses LambdaTheory.{k,k}}
    (mapping : source ⟶ target) : freeObject source.original ⟶ freeObject target.original :=
  extend source.original (freeObject target.original) (mapping ≫ unit target)

theorem freeMap_restriction {source target : BicategoryIsoClasses LambdaTheory.{k,k}}
    (mapping : source ⟶ target) :
    restrict source.original (freeObject target.original) (freeMap mapping) = mapping ≫ unit target :=
  restrict_extend source.original (freeObject target.original) (mapping ≫ unit target)

theorem freeMap_identity (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    freeMap (𝟙 source) = 𝟙 (freeObject source.original) := by
  apply restrict_injective source.original (freeObject source.original)
  rw [freeMap_restriction, restrict_as_base_composition,
    ConjunctiveClosedTheory.forget.map_id]
  change 𝟙 source ≫ unit source = unit source ≫ 𝟙 _
  rw [Category.comp_id, Category.id_comp]

theorem freeMap_compose {source middle target : BicategoryIsoClasses LambdaTheory.{k,k}}
    (before : source ⟶ middle) (after : middle ⟶ target) :
    freeMap (before ≫ after) = freeMap before ≫ freeMap after := by
  apply restrict_injective source.original (freeObject target.original)
  rw [freeMap_restriction, restrict_postcompose, freeMap_restriction, Category.assoc]
  have complete := freeMap_restriction after
  rw [restrict_as_base_composition] at complete
  change unit middle ≫ ConjunctiveClosedTheory.forget.map (freeMap after) = after ≫ unit target at complete
  exact (congrArg (fun value => before ≫ value) complete.symm).trans
    (Category.assoc before (unit middle) (ConjunctiveClosedTheory.forget.map (freeMap after))).symm

def free : BicategoryIsoClasses LambdaTheory.{k,k} ⥤ ConjunctiveClosedTheory.{k} where
  obj source := freeObject source.original
  map mapping := freeMap mapping
  map_id := freeMap_identity
  map_comp := freeMap_compose

def homEquiv (source : BicategoryIsoClasses LambdaTheory.{k,k}) (target : ConjunctiveClosedTheory.{k}) :
    (free.obj source ⟶ target) ≃ (source ⟶ ConjunctiveClosedTheory.forget.obj target) :=
  HomEquivalence.homEquiv source.original target

theorem homEquiv_natural_left_symm
    {source before : BicategoryIsoClasses LambdaTheory.{k,k}} {target : ConjunctiveClosedTheory.{k}}
    (mapping : before ⟶ source) (value : source ⟶ ConjunctiveClosedTheory.forget.obj target) :
    (homEquiv before target).symm (mapping ≫ value) =
      free.map mapping ≫ (homEquiv source target).symm value := by
  apply restrict_injective before.original target
  change restrict before.original target (extend before.original target (mapping ≫ value)) =
    restrict before.original target (freeMap mapping ≫ extend source.original target value)
  rw [restrict_extend, restrict_postcompose, freeMap_restriction, Category.assoc]
  have complete := restrict_extend source.original target value
  rw [restrict_as_base_composition] at complete
  exact congrArg (fun result => mapping ≫ result) complete.symm

theorem homEquiv_natural_right
    {source : BicategoryIsoClasses LambdaTheory.{k,k}} {before target : ConjunctiveClosedTheory.{k}}
    (mapping : free.obj source ⟶ before) (after : before ⟶ target) :
    homEquiv source target (mapping ≫ after) =
      homEquiv source before mapping ≫ ConjunctiveClosedTheory.forget.map after :=
  restrict_postcompose source.original before mapping after

def adjunction : free.{k} ⊣ ConjunctiveClosedTheory.forget :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := homEquiv_natural_left_symm
    homEquiv_naturality_right := homEquiv_natural_right }

theorem unit_app (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    adjunction.unit.app source = unit source := by
  change restrict source.original (freeObject source.original) (𝟙 (freeObject source.original)) = unit source
  rw [restrict_as_base_composition, ConjunctiveClosedTheory.forget.map_id]
  change unit source ≫ 𝟙 _ = unit source
  exact Category.comp_id _

def counitMap (target : ConjunctiveClosedTheory.{k}) : Map (freeObject target.closed) target :=
  extension target.closed target (LambdaTheoryMap.id target.closed)

theorem counit_app (target : ConjunctiveClosedTheory.{k}) :
    adjunction.counit.app target = ConjunctiveClosedTheory.classOf (counitMap target) := rfl

theorem left_triangle (source : BicategoryIsoClasses LambdaTheory.{k,k}) :
    free.map (adjunction.unit.app source) ≫ adjunction.counit.app (free.obj source) = 𝟙 (free.obj source) :=
  adjunction.left_triangle_components source

theorem right_triangle (target : ConjunctiveClosedTheory.{k}) :
    adjunction.unit.app (ConjunctiveClosedTheory.forget.obj target) ≫
      ConjunctiveClosedTheory.forget.map (adjunction.counit.app target) =
        𝟙 (ConjunctiveClosedTheory.forget.obj target) :=
  adjunction.right_triangle_components target

end Mettapedia.CategoryTheory.RelativeClosedConjunctive.FreeForgetful
