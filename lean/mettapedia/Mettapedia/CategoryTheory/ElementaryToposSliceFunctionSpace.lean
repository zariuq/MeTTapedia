import Mettapedia.CategoryTheory.ElementaryToposPartialMapAction

/-!
# Fibrewise function objects from partial maps

The ambient parameter contains a base point and a partial function on the
whole source object. A single exponential equalizer says that mapping its
value to the base gives exactly the partial map with the specified source
fibre as domain. It therefore enforces both domain totality and the base
equation. Evaluation is recovered through the partial-map classifier.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposSliceFunctionSpace

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open ElementaryToposPartialMaps ElementaryToposStableEpimorphisms

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [HasPullbacks C] [HasEqualizers C]
variable (classifier : Subobject.Classifier C)
variable {X Y B : C} (f : X ⟶ B) (g : Y ⟶ B)

abbrev functionParameter (_source : X ⟶ B) (_target : Y ⟶ B) : C :=
  B ⊗ (ihom X).obj (partialObject classifier Y)

abbrev parameterBase : functionParameter classifier f g ⟶ B := fst _ _

def parameterApply : X ⊗ functionParameter classifier f g ⟶ partialObject classifier Y :=
  X ◁ snd _ _ ≫ (ihom.ev X).app (partialObject classifier Y)

def fibrePartial : X ⊗ B ⟶ partialObject classifier B :=
  classifyPartial classifier (graph f) f

def valueCondition : functionParameter classifier f g ⟶ (ihom X).obj (partialObject classifier B) :=
  curry (parameterApply classifier f g ≫ mapPartial classifier g)

def domainCondition : functionParameter classifier f g ⟶ (ihom X).obj (partialObject classifier B) :=
  curry (X ◁ parameterBase classifier f g ≫ fibrePartial classifier f)

abbrev functionSpace : C := equalizer (valueCondition classifier f g) (domainCondition classifier f g)

abbrev functionInclusion : functionSpace classifier f g ⟶ functionParameter classifier f g :=
  equalizer.ι _ _

abbrev functionBase : functionSpace classifier f g ⟶ B :=
  functionInclusion classifier f g ≫ parameterBase classifier f g

def functionApply : X ⊗ functionSpace classifier f g ⟶ partialObject classifier Y :=
  X ◁ functionInclusion classifier f g ≫ parameterApply classifier f g

theorem function_condition : functionApply classifier f g ≫ mapPartial classifier g =
    X ◁ functionBase classifier f g ≫ fibrePartial classifier f := by
  have equation := congrArg uncurry
    (equalizer.condition (valueCondition classifier f g) (domainCondition classifier f g))
  simpa only [uncurry_natural_left, valueCondition, domainCondition, uncurry_curry,
    functionApply, functionBase, functionInclusion, functionSpace,
    MonoidalCategory.whiskerLeft_comp, Category.assoc] using equation

abbrev functionFibre : C := pullback f (functionBase classifier f g)

abbrev fibreInclusion : functionFibre classifier f g ⟶ X ⊗ functionSpace classifier f g :=
  lift (pullback.fst _ _) (pullback.snd _ _)

instance fibreInclusion_mono : Mono (fibreInclusion classifier f g) :=
  (graph_pullback (IsPullback.of_hasPullback f (functionBase classifier f g)).flip).mono_snd_of_mono

abbrev fibreBaseValue : functionFibre classifier f g ⟶ B := pullback.fst _ _ ≫ f

theorem fibre_classification :
    classifyPartial classifier (fibreInclusion classifier f g) (fibreBaseValue classifier f g) =
      functionApply classifier f g ≫ mapPartial classifier g := by
  rw [function_condition]
  exact classifyPartial_substitution classifier (graph f) f
    (X ◁ functionBase classifier f g) (pullback.fst _ _) (fibreInclusion classifier f g)
    (graph_pullback (IsPullback.of_hasPullback f (functionBase classifier f g)).flip).flip

def baseWitness : functionFibre classifier f g ⟶ definedObject classifier B :=
  partialWitness classifier (fibreInclusion classifier f g) (fibreBaseValue classifier f g)

theorem baseWitness_condition : (fibreInclusion classifier f g ≫ functionApply classifier f g) ≫
    mapPartial classifier g = baseWitness classifier f g ≫ domain classifier B := by
  rw [Category.assoc, ← fibre_classification, ← partialWitness_domain]
  rfl

def valueWitness : functionFibre classifier f g ⟶ definedObject classifier Y :=
  (mapDefined_isPullback classifier g).lift
    (fibreInclusion classifier f g ≫ functionApply classifier f g)
    (baseWitness classifier f g) (baseWitness_condition classifier f g)

@[reassoc (attr := simp)] theorem valueWitness_domain :
    valueWitness classifier f g ≫ domain classifier Y =
      fibreInclusion classifier f g ≫ functionApply classifier f g :=
  (mapDefined_isPullback classifier g).lift_fst _ _ _

@[reassoc (attr := simp)] theorem valueWitness_map :
    valueWitness classifier f g ≫ mapDefined classifier g = baseWitness classifier f g :=
  (mapDefined_isPullback classifier g).lift_snd _ _ _

def evaluation : functionFibre classifier f g ⟶ Y :=
  valueWitness classifier f g ≫ value classifier Y

@[reassoc (attr := simp)] theorem evaluation_base :
    evaluation classifier f g ≫ g = fibreBaseValue classifier f g := by
  rw [evaluation, Category.assoc, ← mapDefined_value, ← Category.assoc,
    valueWitness_map]
  exact partialWitness_value classifier _ _

theorem evaluation_domain_isPullback :
    IsPullback (fibreInclusion classifier f g) (valueWitness classifier f g)
      (functionApply classifier f g) (domain classifier Y) := by
  have entire := classifyPartial_isPullback classifier (fibreInclusion classifier f g)
    (fibreBaseValue classifier f g)
  rw [fibre_classification] at entire
  change IsPullback (fibreInclusion classifier f g) (baseWitness classifier f g)
    (functionApply classifier f g ≫ mapPartial classifier g) (domain classifier B) at entire
  have entire' : IsPullback (fibreInclusion classifier f g)
      (valueWitness classifier f g ≫ mapDefined classifier g)
      (functionApply classifier f g ≫ mapPartial classifier g) (domain classifier B) := by
    simpa only [valueWitness_map] using entire
  exact entire'.of_bot (valueWitness_domain classifier f g).symm (mapDefined_isPullback classifier g)

theorem evaluation_classification :
    classifyPartial classifier (fibreInclusion classifier f g) (evaluation classifier f g) =
      functionApply classifier f g :=
  (classifyPartial_unique classifier (fibreInclusion classifier f g) (evaluation classifier f g)
    (functionApply classifier f g) (valueWitness classifier f g)
    (evaluation_domain_isPullback classifier f g) rfl).symm

end Mettapedia.CategoryTheory.ElementaryToposSliceFunctionSpace
