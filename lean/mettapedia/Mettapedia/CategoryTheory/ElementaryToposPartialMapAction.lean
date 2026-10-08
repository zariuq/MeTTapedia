import Mettapedia.CategoryTheory.ElementaryToposPartialMapClassifier

/-!
# Substitution and value maps for partial-map classification

Substitution changes the actual domain by pullback. Mapping the returned
value leaves that domain intact. Both laws follow from the complete
classifier universal property and give the genuine partial-map functor.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposPartialMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [HasPullbacks C] [HasEqualizers C]
variable (classifier : Subobject.Classifier C)

def mapPartial {first second : C} (arrow : first ⟶ second) :
    partialObject classifier first ⟶ partialObject classifier second :=
  classifyPartial classifier (domain classifier first) (value classifier first ≫ arrow)

def mapDefined {first second : C} (arrow : first ⟶ second) :
    definedObject classifier first ⟶ definedObject classifier second :=
  partialWitness classifier (domain classifier first) (value classifier first ≫ arrow)

@[reassoc (attr := simp)] theorem mapDefined_domain {first second : C} (arrow : first ⟶ second) :
    mapDefined classifier arrow ≫ domain classifier second = domain classifier first ≫ mapPartial classifier arrow :=
  partialWitness_domain classifier _ _

@[reassoc (attr := simp)] theorem mapDefined_value {first second : C} (arrow : first ⟶ second) :
    mapDefined classifier arrow ≫ value classifier second = value classifier first ≫ arrow :=
  partialWitness_value classifier _ _

theorem mapDefined_isPullback {first second : C} (arrow : first ⟶ second) :
    IsPullback (domain classifier first) (mapDefined classifier arrow)
      (mapPartial classifier arrow) (domain classifier second) :=
  classifyPartial_isPullback classifier _ _

theorem classifyPartial_substitution {object parameter selected next selectedNext : C}
    (inclusion : selected ⟶ parameter) [Mono inclusion] (suppliedValue : selected ⟶ object)
    (arrow : next ⟶ parameter) (selectedMap : selectedNext ⟶ selected)
    (nextInclusion : selectedNext ⟶ next) [Mono nextInclusion]
    (square : IsPullback nextInclusion selectedMap arrow inclusion) :
    classifyPartial classifier nextInclusion (selectedMap ≫ suppliedValue) =
      arrow ≫ classifyPartial classifier inclusion suppliedValue := by
  have entire := square.paste_vert (classifyPartial_isPullback classifier inclusion suppliedValue)
  have readout : (selectedMap ≫ partialWitness classifier inclusion suppliedValue) ≫
      value classifier object = selectedMap ≫ suppliedValue := by
    rw [Category.assoc, partialWitness_value]
  exact (classifyPartial_unique classifier nextInclusion (selectedMap ≫ suppliedValue)
    (arrow ≫ classifyPartial classifier inclusion suppliedValue)
    (selectedMap ≫ partialWitness classifier inclusion suppliedValue) entire readout).symm

theorem classifyPartial_postcomposition {first second parameter selected : C}
    (inclusion : selected ⟶ parameter) [Mono inclusion] (suppliedValue : selected ⟶ first)
    (arrow : first ⟶ second) :
    classifyPartial classifier inclusion (suppliedValue ≫ arrow) =
      classifyPartial classifier inclusion suppliedValue ≫ mapPartial classifier arrow := by
  have entire := (classifyPartial_isPullback classifier inclusion suppliedValue).paste_vert
    (mapDefined_isPullback classifier arrow)
  have readout : (partialWitness classifier inclusion suppliedValue ≫ mapDefined classifier arrow) ≫
      value classifier second = suppliedValue ≫ arrow := by
    rw [Category.assoc, mapDefined_value, ← Category.assoc, partialWitness_value]
  exact (classifyPartial_unique classifier inclusion (suppliedValue ≫ arrow)
    (classifyPartial classifier inclusion suppliedValue ≫ mapPartial classifier arrow)
    (partialWitness classifier inclusion suppliedValue ≫ mapDefined classifier arrow) entire readout).symm

@[simp] theorem mapPartial_id (object : C) : mapPartial classifier (𝟙 object) = 𝟙 _ := by
  have same := classifyPartial_unique classifier (domain classifier object)
    (value classifier object ≫ 𝟙 object) (𝟙 _) (𝟙 _)
    (IsPullback.of_id_snd (f := domain classifier object)) (by simp)
  exact same.symm

@[simp] theorem mapPartial_comp {first middle last : C}
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    mapPartial classifier (earlier ≫ later) = mapPartial classifier earlier ≫ mapPartial classifier later := by
  simpa only [mapPartial, Category.assoc] using
    classifyPartial_postcomposition classifier (domain classifier first)
      (value classifier first ≫ earlier) later

def partialFunctor : C ⥤ C where
  obj := partialObject classifier
  map := mapPartial classifier
  map_id := mapPartial_id classifier
  map_comp := mapPartial_comp classifier

end Mettapedia.CategoryTheory.ElementaryToposPartialMaps
