import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# The category of isomorphism classes of bicategorical maps

Objects are retained. Only parallel one-cells are identified, by an actual
invertible two-cell. Whiskering makes this relation compatible with
composition, and the supplied associators and unitors earn the ordinary
category laws. Every pseudofunctor descends to an actual ordinary functor.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory

universe u v w u' v' w'

structure BicategoryIsoClasses (B : Type u) where
  original : B

namespace BicategoryIsoClasses

variable {B : Type u} [Bicategory.{w,v} B]

def mapSetoid (source target : B) : Setoid (source ⟶ target) where
  r first second := Nonempty (first ≅ second)
  iseqv :=
    ⟨fun first => ⟨Iso.refl first⟩,
      fun ⟨comparison⟩ => ⟨comparison.symm⟩,
      fun ⟨before⟩ ⟨after⟩ => ⟨before ≪≫ after⟩⟩

abbrev Hom (source target : BicategoryIsoClasses B) :=
  Quotient (mapSetoid source.original target.original)

private theorem compose_compatible {source middle target : B}
    {before before' : source ⟶ middle} {after after' : middle ⟶ target}
    (first : Nonempty (before ≅ before')) (second : Nonempty (after ≅ after')) :
    Nonempty (before ≫ after ≅ before' ≫ after') := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  exact ⟨Bicategory.whiskerRightIso first after ≪≫ Bicategory.whiskerLeftIso before' second⟩

def compose {source middle target : BicategoryIsoClasses B}
    (before : Hom source middle) (after : Hom middle target) : Hom source target :=
  Quotient.map₂ (fun first second => first ≫ second)
    (fun _ _ before _ _ after => compose_compatible before after)
    before after

instance category : Category.{v} (BicategoryIsoClasses B) where
  Hom := Hom
  id source := Quotient.mk _ (𝟙 source.original)
  comp before after := compose before after
  id_comp after := Quotient.inductionOn after fun after =>
    Quotient.sound ⟨Bicategory.leftUnitor after⟩
  comp_id before := Quotient.inductionOn before fun before =>
    Quotient.sound ⟨Bicategory.rightUnitor before⟩
  assoc before middle after := Quotient.inductionOn₃ before middle after fun before middle after =>
    Quotient.sound ⟨Bicategory.associator before middle after⟩

def of (source : B) : BicategoryIsoClasses B := ⟨source⟩

def classOf {source target : B} (mapping : source ⟶ target) : of source ⟶ of target :=
  Quotient.mk _ mapping

theorem classOf_equal_iff {source target : B} (first second : source ⟶ target) :
    classOf first = classOf second ↔ Nonempty (first ≅ second) :=
  Quotient.eq

theorem classOf_identity (source : B) : classOf (𝟙 source) = 𝟙 (of source) := rfl

theorem classOf_compose {source middle target : B}
    (before : source ⟶ middle) (after : middle ⟶ target) :
    classOf (before ≫ after) = classOf before ≫ classOf after := rfl

variable {D : Type u'} [Bicategory.{w',v'} D]

def map (action : Pseudofunctor B D) : BicategoryIsoClasses B ⥤ BicategoryIsoClasses D where
  obj source := of (action.obj source.original)
  map mapping := Quotient.map (fun mapping => action.map mapping)
    (fun first second comparison => by
      obtain ⟨comparison⟩ := (show Nonempty (first ≅ second) from comparison)
      exact ⟨action.map₂Iso comparison⟩) mapping
  map_id source := Quotient.sound ⟨action.mapId source.original⟩
  map_comp before after := Quotient.inductionOn₂ before after fun before after =>
    Quotient.sound ⟨action.mapComp before after⟩

theorem map_classOf (action : Pseudofunctor B D) {source target : B}
    (mapping : source ⟶ target) :
    (map action).map (classOf mapping) = classOf (action.map mapping) := rfl

end BicategoryIsoClasses

end Mettapedia.CategoryTheory
