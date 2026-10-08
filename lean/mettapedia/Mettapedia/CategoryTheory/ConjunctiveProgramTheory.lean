import Mettapedia.CategoryTheory.ConjunctiveClosedTheory
import Mettapedia.CategoryTheory.ProgramReductionTheoryIsoClasses

/-!
# Conjunctive program theories and complete compatible maps

The underlying theory retains an actual program object and monic reduction
relation. The additional ordinary proposition object, truth and conjunction
satisfy four finite diagrams. Maps retain both the independent program and
proposition comparisons, and the complete reduction map.

Only maps are identified by compatible natural isomorphisms; every raw theory
object is retained. Both local object readings are data. Naturality and the
joint monicity of reduction endpoints determine the entire event comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core

universe k

structure ConjunctiveProgramTheory where
  programTheory : ProgramReductionTheory.Theory.{k,k}
  operations : InternalConjunctiveObject.Operations programTheory.closed.Obj
  laws : operations.Laws

namespace ConjunctiveProgramTheory

abbrev closed (source : ConjunctiveProgramTheory.{k}) := source.programTheory.closed

def conjunctive (source : ConjunctiveProgramTheory.{k}) : ConjunctiveClosedTheory.{k} :=
  ⟨source.closed, source.operations, source.laws⟩

structure Map (first second : ConjunctiveProgramTheory.{k}) where
  conjunctive : ConjunctiveClosedTheory.Map first.conjunctive second.conjunctive
  program : conjunctive.functor.obj first.programTheory.program ≅ second.programTheory.program
  reduction : conjunctive.functor.obj first.programTheory.Event ⟶ second.programTheory.Event
  source : reduction ≫ second.programTheory.source =
    conjunctive.functor.map first.programTheory.source ≫ program.hom
  target : reduction ≫ second.programTheory.target =
    conjunctive.functor.map first.programTheory.target ≫ program.hom

namespace Map

variable {source middle target last : ConjunctiveProgramTheory.{k}}

abbrev functor (mapping : Map source target) := mapping.conjunctive.functor

def underlying (mapping : Map source target) : ProgramReductionTheory.Map source.programTheory target.programTheory where
  closed := mapping.conjunctive.underlying
  program := mapping.program
  reduction := mapping.reduction
  source := mapping.source
  target := mapping.target

def identity (source : ConjunctiveProgramTheory.{k}) : Map source source where
  conjunctive := ConjunctiveClosedTheory.Map.identity source.conjunctive
  program := Iso.refl _
  reduction := 𝟙 _
  source := (Category.id_comp _).trans (Category.comp_id _).symm
  target := (Category.id_comp _).trans (Category.comp_id _).symm

def compose (before : Map source middle) (after : Map middle target) : Map source target where
  conjunctive := ConjunctiveClosedTheory.Map.compose before.conjunctive after.conjunctive
  program := (ProgramReductionTheory.Map.compose before.underlying after.underlying).program
  reduction := (ProgramReductionTheory.Map.compose before.underlying after.underlying).reduction
  source := (ProgramReductionTheory.Map.compose before.underlying after.underlying).source
  target := (ProgramReductionTheory.Map.compose before.underlying after.underlying).target

theorem complete_reduction_unique (mapping : Map source target)
    (candidate : mapping.functor.obj source.programTheory.Event ⟶ target.programTheory.Event)
    (sources : candidate ≫ target.programTheory.source =
      mapping.functor.map source.programTheory.source ≫ mapping.program.hom)
    (targets : candidate ≫ target.programTheory.target =
      mapping.functor.map source.programTheory.target ≫ mapping.program.hom) :
    candidate = mapping.reduction := mapping.underlying.reduction_unique candidate sources targets

end Map

structure MapIso {source target : ConjunctiveProgramTheory.{k}} (first second : Map source target) where
  conjunctive : ConjunctiveClosedTheory.MapIso first.conjunctive second.conjunctive
  program : conjunctive.comparison.hom.app source.programTheory.program ≫ second.program.hom = first.program.hom

namespace MapIso

variable {source middle target last : ConjunctiveProgramTheory.{k}}
variable {first second third : Map source target}

abbrev comparison (change : MapIso first second) := change.conjunctive.comparison

def underlying (change : MapIso first second) :
    ProgramReductionTheoryIsoClasses.MapIso first.underlying second.underlying :=
  ⟨change.comparison, change.program⟩

theorem reduction_square (change : MapIso first second) :
    change.comparison.hom.app source.programTheory.Event ≫ second.reduction = first.reduction :=
  change.underlying.reduction_square

def refl (mapping : Map source target) : MapIso mapping mapping where
  conjunctive := ConjunctiveClosedTheory.MapIso.refl mapping.conjunctive
  program := Category.id_comp _

def symm (change : MapIso first second) : MapIso second first where
  conjunctive := change.conjunctive.symm
  program := change.underlying.symm.program

def trans (before : MapIso first second) (after : MapIso second third) : MapIso first third where
  conjunctive := before.conjunctive.trans after.conjunctive
  program := (before.underlying.trans after.underlying).program

def postcompose (change : MapIso first second) (after : Map target last) :
    MapIso (Map.compose first after) (Map.compose second after) where
  conjunctive := change.conjunctive.postcompose after.conjunctive
  program := (change.underlying.postcompose after.underlying).program

def precompose (before : Map middle source) (change : MapIso first second) :
    MapIso (Map.compose before first) (Map.compose before second) where
  conjunctive := change.conjunctive.precompose before.conjunctive
  program := (change.underlying.precompose before.underlying).program

def leftUnitor (mapping : Map source target) : MapIso (Map.compose (Map.identity source) mapping) mapping where
  conjunctive := ConjunctiveClosedTheory.MapIso.leftUnitor mapping.conjunctive
  program := by
    change 𝟙 _ ≫ mapping.program.hom = mapping.functor.map (𝟙 _) ≫ mapping.program.hom
    rw [mapping.functor.map_id, Category.id_comp]

def rightUnitor (mapping : Map source target) : MapIso (Map.compose mapping (Map.identity target)) mapping where
  conjunctive := ConjunctiveClosedTheory.MapIso.rightUnitor mapping.conjunctive
  program := by
    change 𝟙 _ ≫ mapping.program.hom = mapping.program.hom ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

def associator (before : Map source middle) (between : Map middle target) (after : Map target last) :
    MapIso (Map.compose (Map.compose before between) after) (Map.compose before (Map.compose between after)) where
  conjunctive := ConjunctiveClosedTheory.MapIso.associator before.conjunctive between.conjunctive after.conjunctive
  program := by
    change 𝟙 _ ≫ (after.functor.map (between.functor.map before.program.hom) ≫
        (after.functor.map between.program.hom ≫ after.program.hom)) =
      after.functor.map (between.functor.map before.program.hom ≫ between.program.hom) ≫ after.program.hom
    rw [Category.id_comp, after.functor.map_comp, Category.assoc]

end MapIso

def mapSetoid (source target : ConjunctiveProgramTheory.{k}) : Setoid (Map source target) where
  r first second := Nonempty (MapIso first second)
  iseqv := ⟨fun mapping => ⟨MapIso.refl mapping⟩,
    fun ⟨change⟩ => ⟨change.symm⟩,
    fun ⟨before⟩ ⟨after⟩ => ⟨before.trans after⟩⟩

private theorem compose_compatible {source middle target : ConjunctiveProgramTheory.{k}}
    {before before' : Map source middle} {after after' : Map middle target}
    (first : Nonempty (MapIso before before')) (second : Nonempty (MapIso after after')) :
    Nonempty (MapIso (Map.compose before after) (Map.compose before' after')) := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  exact ⟨(first.postcompose after).trans (second.precompose before')⟩

def compose {source middle target : ConjunctiveProgramTheory.{k}}
    (before : Quotient (mapSetoid source middle)) (after : Quotient (mapSetoid middle target)) :
    Quotient (mapSetoid source target) :=
  Quotient.map₂ Map.compose (fun _ _ before _ _ after => compose_compatible before after) before after

instance category : Category (ConjunctiveProgramTheory.{k}) where
  Hom source target := Quotient (mapSetoid source target)
  id source := Quotient.mk _ (Map.identity source)
  comp before after := compose before after
  id_comp after := Quotient.inductionOn after fun after => Quotient.sound ⟨MapIso.leftUnitor after⟩
  comp_id before := Quotient.inductionOn before fun before => Quotient.sound ⟨MapIso.rightUnitor before⟩
  assoc before middle after := Quotient.inductionOn₃ before middle after fun before middle after =>
    Quotient.sound ⟨MapIso.associator before middle after⟩

def classOf {source target : ConjunctiveProgramTheory.{k}} (mapping : Map source target) : source ⟶ target :=
  Quotient.mk _ mapping

theorem classOf_equal_iff {source target : ConjunctiveProgramTheory.{k}} (first second : Map source target) :
    classOf first = classOf second ↔ Nonempty (MapIso first second) := Quotient.eq

def forget : ConjunctiveProgramTheory.{k} ⥤ ProgramReductionTheoryIsoClasses.{k} where
  obj source := ProgramReductionTheoryIsoClasses.of source.programTheory
  map mapping := Quotient.map Map.underlying
    (fun first second same => by
      obtain ⟨same⟩ := (show Nonempty (MapIso first second) from same)
      exact ⟨same.underlying⟩) mapping
  map_id _ := Quotient.sound ⟨ProgramReductionTheoryIsoClasses.MapIso.refl _⟩
  map_comp before after := Quotient.inductionOn₂ before after fun _ _ =>
    Quotient.sound ⟨ProgramReductionTheoryIsoClasses.MapIso.refl _⟩

theorem forget_classOf {source target : ConjunctiveProgramTheory.{k}} (mapping : Map source target) :
    forget.map (classOf mapping) = ProgramReductionTheoryIsoClasses.classOf mapping.underlying := rfl

end ConjunctiveProgramTheory

end Mettapedia.CategoryTheory
