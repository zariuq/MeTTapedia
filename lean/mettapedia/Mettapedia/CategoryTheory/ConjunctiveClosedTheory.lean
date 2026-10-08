import Mettapedia.CategoryTheory.ClosedTheoryIsoClasses
import Mettapedia.CategoryTheory.InternalConjunctiveObjectMaps

/-!
# Closed theories with an internal conjunctive object

The extra structure consists of an ordinary proposition object, truth and
conjunction satisfying four finite diagrams. Maps preserve these declarations
by two actual local squares. Compatible natural isomorphisms retain the
supplied proposition-object comparison; their classes form a genuine
category, with an actual forgetful functor to closed theory map classes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core

universe k

structure ConjunctiveClosedTheory where
  closed : LambdaTheory.{k,k}
  operations : InternalConjunctiveObject.Operations closed.Obj
  laws : operations.Laws

namespace ConjunctiveClosedTheory

structure Map (source target : ConjunctiveClosedTheory.{k}) where
  declarations : InternalConjunctiveObject.Map source.operations target.operations
  finite : PreservesFiniteLimits declarations.functor
  closed : MonoidalClosedFunctor declarations.functor

attribute [instance] Map.finite Map.closed

namespace Map

variable {source middle target : ConjunctiveClosedTheory.{k}}

abbrev functor (mapping : Map source target) := mapping.declarations.functor

def underlying (mapping : Map source target) : LambdaTheoryMap source.closed target.closed where
  functor := mapping.functor
  preservesFiniteLimits := mapping.finite
  preservesExponentials := mapping.closed

def identity (source : ConjunctiveClosedTheory.{k}) : Map source source where
  declarations := InternalConjunctiveObject.Map.identity source.operations
  finite := inferInstanceAs (PreservesFiniteLimits (𝟭 source.closed.Obj))
  closed := by
    change MonoidalClosedFunctor (𝟭 source.closed.Obj)
    exact cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts _ Adjunction.id

def compose (before : Map source middle) (after : Map middle target) : Map source target where
  declarations := InternalConjunctiveObject.Map.comp before.declarations after.declarations
  finite := comp_preservesFiniteLimits before.functor after.functor
  closed := CartesianClosedFunctorCoherence.closed_composition before.functor after.functor

end Map

structure MapIso {source target : ConjunctiveClosedTheory.{k}}
    (first second : Map source target) where
  comparison : first.functor ≅ second.functor
  proposition : comparison.hom.app source.operations.proposition ≫ second.declarations.proposition.hom =
    first.declarations.proposition.hom

namespace MapIso

variable {source middle target last : ConjunctiveClosedTheory.{k}}
variable {first second third : Map source target}

def refl (mapping : Map source target) : MapIso mapping mapping where
  comparison := Iso.refl _
  proposition := Category.id_comp _

def symm (before : MapIso first second) : MapIso second first where
  comparison := before.comparison.symm
  proposition := by
    change before.comparison.inv.app source.operations.proposition ≫
      first.declarations.proposition.hom = second.declarations.proposition.hom
    rw [← before.proposition, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

def trans (before : MapIso first second) (after : MapIso second third) : MapIso first third where
  comparison := before.comparison ≪≫ after.comparison
  proposition := by
    change (before.comparison.hom.app _ ≫ after.comparison.hom.app _) ≫ _ = _
    rw [Category.assoc, after.proposition, before.proposition]

def postcompose (before : MapIso first second) (after : Map target last) :
    MapIso (Map.compose first after) (Map.compose second after) where
  comparison := Functor.isoWhiskerRight before.comparison after.functor
  proposition := by
    change after.functor.map (before.comparison.hom.app _) ≫
      (after.functor.map second.declarations.proposition.hom ≫ after.declarations.proposition.hom) =
        after.functor.map first.declarations.proposition.hom ≫ after.declarations.proposition.hom
    rw [← Category.assoc, ← after.functor.map_comp, before.proposition]

def precompose (before : Map middle source) (after : MapIso first second) :
    MapIso (Map.compose before first) (Map.compose before second) where
  comparison := Functor.isoWhiskerLeft before.functor after.comparison
  proposition := by
    change after.comparison.hom.app (before.functor.obj _) ≫
      (second.functor.map before.declarations.proposition.hom ≫ second.declarations.proposition.hom) =
        first.functor.map before.declarations.proposition.hom ≫ first.declarations.proposition.hom
    rw [← Category.assoc, ← after.comparison.hom.naturality before.declarations.proposition.hom,
      Category.assoc, after.proposition]

def leftUnitor (mapping : Map source target) : MapIso (Map.compose (Map.identity source) mapping) mapping where
  comparison := Functor.leftUnitor mapping.functor
  proposition := by
    change 𝟙 _ ≫ mapping.declarations.proposition.hom =
      mapping.functor.map (𝟙 source.operations.proposition) ≫ mapping.declarations.proposition.hom
    rw [mapping.functor.map_id, Category.id_comp]

def rightUnitor (mapping : Map source target) : MapIso (Map.compose mapping (Map.identity target)) mapping where
  comparison := Functor.rightUnitor mapping.functor
  proposition := by
    change 𝟙 _ ≫ mapping.declarations.proposition.hom = mapping.declarations.proposition.hom ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

def associator (before : Map source middle) (between : Map middle target) (after : Map target last) :
    MapIso (Map.compose (Map.compose before between) after) (Map.compose before (Map.compose between after)) where
  comparison := Functor.associator before.functor between.functor after.functor
  proposition := by
    change 𝟙 _ ≫ (after.functor.map (between.functor.map before.declarations.proposition.hom) ≫
        (after.functor.map between.declarations.proposition.hom ≫ after.declarations.proposition.hom)) =
      after.functor.map (between.functor.map before.declarations.proposition.hom ≫
        between.declarations.proposition.hom) ≫ after.declarations.proposition.hom
    rw [Category.id_comp, after.functor.map_comp, Category.assoc]

end MapIso

def mapSetoid (source target : ConjunctiveClosedTheory.{k}) : Setoid (Map source target) where
  r first second := Nonempty (MapIso first second)
  iseqv := ⟨fun mapping => ⟨MapIso.refl mapping⟩,
    fun ⟨comparison⟩ => ⟨comparison.symm⟩,
    fun ⟨before⟩ ⟨after⟩ => ⟨before.trans after⟩⟩

private theorem compose_compatible {source middle target : ConjunctiveClosedTheory.{k}}
    {before before' : Map source middle} {after after' : Map middle target}
    (first : Nonempty (MapIso before before')) (second : Nonempty (MapIso after after')) :
    Nonempty (MapIso (Map.compose before after) (Map.compose before' after')) := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  exact ⟨(first.postcompose after).trans (second.precompose before')⟩

def compose {source middle target : ConjunctiveClosedTheory.{k}}
    (before : Quotient (mapSetoid source middle)) (after : Quotient (mapSetoid middle target)) :
    Quotient (mapSetoid source target) :=
  Quotient.map₂ Map.compose (fun _ _ before _ _ after => compose_compatible before after) before after

instance category : Category (ConjunctiveClosedTheory.{k}) where
  Hom source target := Quotient (mapSetoid source target)
  id source := Quotient.mk _ (Map.identity source)
  comp before after := compose before after
  id_comp after := Quotient.inductionOn after fun after => Quotient.sound ⟨MapIso.leftUnitor after⟩
  comp_id before := Quotient.inductionOn before fun before => Quotient.sound ⟨MapIso.rightUnitor before⟩
  assoc before middle after := Quotient.inductionOn₃ before middle after fun before middle after =>
    Quotient.sound ⟨MapIso.associator before middle after⟩

def classOf {source target : ConjunctiveClosedTheory.{k}} (mapping : Map source target) : source ⟶ target :=
  Quotient.mk _ mapping

theorem classOf_equal_iff {source target : ConjunctiveClosedTheory.{k}}
    (first second : Map source target) : classOf first = classOf second ↔ Nonempty (MapIso first second) :=
  Quotient.eq

theorem classOf_identity (source : ConjunctiveClosedTheory.{k}) : classOf (Map.identity source) = 𝟙 source := rfl

theorem classOf_compose {source middle target : ConjunctiveClosedTheory.{k}}
    (before : Map source middle) (after : Map middle target) :
    classOf (Map.compose before after) = classOf before ≫ classOf after := rfl

def forget : ConjunctiveClosedTheory.{k} ⥤ BicategoryIsoClasses LambdaTheory.{k,k} where
  obj source := ClosedTheoryIsoClasses.of source.closed
  map mapping := Quotient.map Map.underlying
    (fun first second same => by
      obtain ⟨same⟩ := (show Nonempty (MapIso first second) from same)
      exact ⟨LambdaTheory.isoOfNatIso same.comparison⟩) mapping
  map_id _ := Quotient.sound ⟨Iso.refl _⟩
  map_comp before after := Quotient.inductionOn₂ before after fun _ _ => Quotient.sound ⟨Iso.refl _⟩

theorem forget_classOf {source target : ConjunctiveClosedTheory.{k}} (mapping : Map source target) :
    forget.map (classOf mapping) = ClosedTheoryIsoClasses.classOf mapping.underlying := rfl

end ConjunctiveClosedTheory

end Mettapedia.CategoryTheory
