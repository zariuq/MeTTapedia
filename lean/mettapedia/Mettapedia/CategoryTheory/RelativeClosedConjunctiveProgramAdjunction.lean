import Mettapedia.CategoryTheory.RelativeClosedConjunctiveProgramHomEquivalence
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Actual free-forgetful adjunction for conjunctive program theories

Restriction and independently constructed extension preserve the complete
program and reduction readings. The derived hom correspondence is natural
in both arguments and earns a genuine Mathlib adjunction. Weak categorical
choices are compared by whole compatible natural isomorphisms; raw theory
objects remain intact.

This is the conjunctive stratum over actual program theories. Modal,
structural and stronger propositional layers require additional generators
and their independently admitted relations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctiveProgram.FreeForgetful

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core
open ConjunctiveProgramTheory HomEquivalence

universe k

def unit (source : ProgramReductionTheoryIsoClasses.{k}) :
    source ⟶ ConjunctiveProgramTheory.forget.obj (freeObject source.original) :=
  ProgramReductionTheoryIsoClasses.classOf (unitMap source.original)

def freeMap {source target : ProgramReductionTheoryIsoClasses.{k}}
    (mapping : source ⟶ target) : freeObject source.original ⟶ freeObject target.original :=
  extend source.original (freeObject target.original) (mapping ≫ unit target)

theorem freeMap_restriction {source target : ProgramReductionTheoryIsoClasses.{k}}
    (mapping : source ⟶ target) :
    restrict source.original (freeObject target.original) (freeMap mapping) = mapping ≫ unit target :=
  restrict_extend source.original (freeObject target.original) (mapping ≫ unit target)

theorem freeMap_identity (source : ProgramReductionTheoryIsoClasses.{k}) :
    freeMap (𝟙 source) = 𝟙 (freeObject source.original) := by
  apply restrict_injective source.original (freeObject source.original)
  rw [freeMap_restriction, restrict_as_base_composition,
    ConjunctiveProgramTheory.forget.map_id]
  change 𝟙 source ≫ unit source = unit source ≫ 𝟙 _
  rw [Category.comp_id, Category.id_comp]

theorem freeMap_compose {source middle target : ProgramReductionTheoryIsoClasses.{k}}
    (before : source ⟶ middle) (after : middle ⟶ target) :
    freeMap (before ≫ after) = freeMap before ≫ freeMap after := by
  apply restrict_injective source.original (freeObject target.original)
  rw [freeMap_restriction, restrict_postcompose, freeMap_restriction, Category.assoc]
  have complete := freeMap_restriction after
  rw [restrict_as_base_composition] at complete
  change unit middle ≫ ConjunctiveProgramTheory.forget.map (freeMap after) = after ≫ unit target at complete
  exact (congrArg (fun value => before ≫ value) complete.symm).trans
    (Category.assoc before (unit middle) (ConjunctiveProgramTheory.forget.map (freeMap after))).symm

def free : ProgramReductionTheoryIsoClasses.{k} ⥤ ConjunctiveProgramTheory.{k} where
  obj source := freeObject source.original
  map mapping := freeMap mapping
  map_id := freeMap_identity
  map_comp := freeMap_compose

def homEquiv (source : ProgramReductionTheoryIsoClasses.{k}) (target : ConjunctiveProgramTheory.{k}) :
    (free.obj source ⟶ target) ≃ (source ⟶ ConjunctiveProgramTheory.forget.obj target) :=
  HomEquivalence.homEquiv source.original target

theorem homEquiv_natural_left_symm
    {source before : ProgramReductionTheoryIsoClasses.{k}} {target : ConjunctiveProgramTheory.{k}}
    (mapping : before ⟶ source) (value : source ⟶ ConjunctiveProgramTheory.forget.obj target) :
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
    {source : ProgramReductionTheoryIsoClasses.{k}} {before target : ConjunctiveProgramTheory.{k}}
    (mapping : free.obj source ⟶ before) (after : before ⟶ target) :
    homEquiv source target (mapping ≫ after) =
      homEquiv source before mapping ≫ ConjunctiveProgramTheory.forget.map after :=
  restrict_postcompose source.original before mapping after

def adjunction : free.{k} ⊣ ConjunctiveProgramTheory.forget :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := homEquiv_natural_left_symm
    homEquiv_naturality_right := homEquiv_natural_right }

theorem unit_app (source : ProgramReductionTheoryIsoClasses.{k}) :
    adjunction.unit.app source = unit source := by
  change restrict source.original (freeObject source.original) (𝟙 (freeObject source.original)) = unit source
  rw [restrict_as_base_composition, ConjunctiveProgramTheory.forget.map_id]
  change unit source ≫ 𝟙 _ = unit source
  exact Category.comp_id _

def counitMap (target : ConjunctiveProgramTheory.{k}) : Map (freeObject target.programTheory) target :=
  extension target.programTheory target (ProgramReductionTheory.Map.identity target.programTheory)

theorem counit_app (target : ConjunctiveProgramTheory.{k}) :
    adjunction.counit.app target = ConjunctiveProgramTheory.classOf (counitMap target) := rfl

theorem left_triangle (source : ProgramReductionTheoryIsoClasses.{k}) :
    free.map (adjunction.unit.app source) ≫ adjunction.counit.app (free.obj source) = 𝟙 (free.obj source) :=
  adjunction.left_triangle_components source

theorem right_triangle (target : ConjunctiveProgramTheory.{k}) :
    adjunction.unit.app (ConjunctiveProgramTheory.forget.obj target) ≫
      ConjunctiveProgramTheory.forget.map (adjunction.counit.app target) =
        𝟙 (ConjunctiveProgramTheory.forget.obj target) :=
  adjunction.right_triangle_components target

end Mettapedia.CategoryTheory.RelativeClosedConjunctiveProgram.FreeForgetful

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctiveProgram.Construction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core
open RelativeClosedSyntax GeneratedCategory
open ConjunctiveProgramTheory HomEquivalence FreeForgetful

universe k

private instance identity_closed {C : Type k} [Category.{k} C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] : MonoidalClosedFunctor (𝟭 C) :=
  cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts _ Adjunction.id

def monad : Monad ProgramReductionTheoryIsoClasses.{k} := FreeForgetful.adjunction.toMonad

theorem underlying_object (source : ProgramReductionTheoryIsoClasses.{k}) :
    monad.obj source = ProgramReductionTheoryIsoClasses.of (freeObject source.original).programTheory := rfl

theorem underlying_map {source target : ProgramReductionTheoryIsoClasses.{k}} (mapping : source ⟶ target) :
    monad.map mapping = ConjunctiveProgramTheory.forget.map (freeMap mapping) := rfl

theorem unit_component (source : ProgramReductionTheoryIsoClasses.{k}) :
    monad.η.app source = FreeForgetful.unit source := FreeForgetful.unit_app source

def multiplicationMap (source : ProgramReductionTheoryIsoClasses.{k}) :
    ProgramReductionTheory.Map
      (freeObject (freeObject source.original).programTheory).programTheory
      (freeObject source.original).programTheory :=
  (counitMap (freeObject source.original)).underlying

theorem multiplication_component (source : ProgramReductionTheoryIsoClasses.{k}) :
    monad.μ.app source = ProgramReductionTheoryIsoClasses.classOf (multiplicationMap source) := rfl

def multiplication_base_comparison (source : ProgramReductionTheoryIsoClasses.{k}) :
    ProgramReductionTheoryIsoClasses.MapIso
      (ProgramReductionTheory.Map.compose (unitMap (freeObject source.original).programTheory)
        (multiplicationMap source))
      (ProgramReductionTheory.Map.identity (freeObject source.original).programTheory) :=
  ModelReadout.extension_base (freeObject source.original).programTheory (freeObject source.original)
    (ProgramReductionTheory.Map.identity (freeObject source.original).programTheory)

theorem retains_complete_event (source : ProgramReductionTheoryIsoClasses.{k}) :
    (multiplication_base_comparison source).comparison.hom.app (freeObject source.original).programTheory.Event ≫
        𝟙 (freeObject source.original).programTheory.Event =
      (multiplicationMap source).closed.functor.map
          (unitMap (freeObject source.original).programTheory).reduction ≫
        (multiplicationMap source).reduction :=
  (multiplication_base_comparison source).reduction_square

theorem folds_proposition (source : ProgramReductionTheoryIsoClasses.{k}) :
    (multiplicationMap source).closed.functor.obj
        (freeObject (freeObject source.original).programTheory).operations.proposition =
      (freeObject source.original).operations.proposition :=
  RelativeClosedConjunctive.ModelReadout.proposition_read (𝟭 (freeObject source.original).closed.Obj)
    (freeObject source.original).operations (freeObject source.original).laws

theorem folds_truth (source : ProgramReductionTheoryIsoClasses.{k}) :
    HEq ((multiplicationMap source).closed.functor.map
      (freeObject (freeObject source.original).programTheory).operations.truth)
      (freeObject source.original).operations.truth :=
  RelativeClosedConjunctive.ModelReadout.truth_heq (𝟭 (freeObject source.original).closed.Obj)
    (freeObject source.original).operations (freeObject source.original).laws

theorem folds_conjunction (source : ProgramReductionTheoryIsoClasses.{k}) :
    HEq ((multiplicationMap source).closed.functor.map
      (freeObject (freeObject source.original).programTheory).operations.conjunction)
      (freeObject source.original).operations.conjunction :=
  RelativeClosedConjunctive.ModelReadout.conjunction_heq (𝟭 (freeObject source.original).closed.Obj)
    (freeObject source.original).operations (freeObject source.original).laws

theorem retains_old_object (source : ProgramReductionTheoryIsoClasses.{k})
    (object : (freeObject source.original).closed.Obj) :
    (multiplicationMap source).closed.functor.obj
      (baseObject (RelativeClosedConjunctive.nativeSignature (C := (freeObject source.original).closed.Obj)) object) = object :=
  RelativeClosedSyntax.Interpretation.functor_base_object
    (RelativeClosedConjunctive.ModelReadout.model (𝟭 (freeObject source.original).closed.Obj)
      (freeObject source.original).operations (freeObject source.original).laws).meanings
    (RelativeClosedConjunctive.ModelReadout.model (𝟭 (freeObject source.original).closed.Obj)
      (freeObject source.original).operations (freeObject source.original).laws).realization object

theorem retains_old_arrow (source : ProgramReductionTheoryIsoClasses.{k})
    {before after : (freeObject source.original).closed.Obj} (arrow : before ⟶ after) :
    (multiplicationMap source).closed.functor.map
      (baseArrow (signature := RelativeClosedConjunctive.nativeSignature
        (C := (freeObject source.original).closed.Obj)) arrow) = arrow :=
  RelativeClosedSyntax.Interpretation.functor_base_arrow
    (RelativeClosedConjunctive.ModelReadout.model (𝟭 (freeObject source.original).closed.Obj)
      (freeObject source.original).operations (freeObject source.original).laws).meanings
    (RelativeClosedConjunctive.ModelReadout.model (𝟭 (freeObject source.original).closed.Obj)
      (freeObject source.original).operations (freeObject source.original).laws).realization arrow

theorem right_unit (source : ProgramReductionTheoryIsoClasses.{k}) :
    monad.map (monad.η.app source) ≫ monad.μ.app source = 𝟙 (monad.obj source) := monad.right_unit source

theorem left_unit (source : ProgramReductionTheoryIsoClasses.{k}) :
    monad.η.app (monad.obj source) ≫ monad.μ.app source = 𝟙 (monad.obj source) := monad.left_unit source

theorem associativity (source : ProgramReductionTheoryIsoClasses.{k}) :
    monad.map (monad.μ.app source) ≫ monad.μ.app source =
      monad.μ.app (monad.obj source) ≫ monad.μ.app source := monad.assoc source

end Mettapedia.CategoryTheory.RelativeClosedConjunctiveProgram.Construction
