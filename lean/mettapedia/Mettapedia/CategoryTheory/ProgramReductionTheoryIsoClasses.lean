import Mettapedia.CategoryTheory.ClosedTheoryIsoClasses
import Mettapedia.GSLT.Core.ProgramReductionTheory

/-!
# Program and reduction theories up to compatible map isomorphism

Maps retain the actual finite-limit closed functor, the program comparison
and the complete reduction arrow. A compatible natural isomorphism fixes
the independently supplied program reading. Its reduction square follows
from naturality at both endpoints and their joint monicity.

All theory objects are retained. Only maps are identified, through actual
compatible natural isomorphisms. The ordinary category below uses a common
object and hom universe, as required by its generated-extension consumers.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory
open Mettapedia.GSLT.Core

universe k

namespace ProgramReductionTheoryIsoClasses

structure MapIso {source target : ProgramReductionTheory.Theory.{k,k}}
    (first second : ProgramReductionTheory.Map source target) where
  comparison : first.closed.functor ≅ second.closed.functor
  program : comparison.hom.app source.program ≫ second.program.hom = first.program.hom

namespace MapIso

variable {source middle target last : ProgramReductionTheory.Theory.{k,k}}
variable {first second third : ProgramReductionTheory.Map source target}

theorem reduction_square (change : MapIso first second) :
    change.comparison.hom.app source.Event ≫ second.reduction = first.reduction := by
  apply target.endpoint_joint_cancel
  · rw [Category.assoc, second.source, ← Category.assoc,
      ← change.comparison.hom.naturality source.source, Category.assoc,
      change.program, first.source]
  · rw [Category.assoc, second.target, ← Category.assoc,
      ← change.comparison.hom.naturality source.target, Category.assoc,
      change.program, first.target]

def refl (mapping : ProgramReductionTheory.Map source target) : MapIso mapping mapping where
  comparison := Iso.refl _
  program := Category.id_comp _

def symm (change : MapIso first second) : MapIso second first where
  comparison := change.comparison.symm
  program := by
    change change.comparison.inv.app source.program ≫ first.program.hom = second.program.hom
    rw [← change.program, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

def trans (before : MapIso first second) (after : MapIso second third) : MapIso first third where
  comparison := before.comparison ≪≫ after.comparison
  program := by
    change (before.comparison.hom.app _ ≫ after.comparison.hom.app _) ≫ _ = _
    rw [Category.assoc, after.program, before.program]

def postcompose (change : MapIso first second) (after : ProgramReductionTheory.Map target last) :
    MapIso (ProgramReductionTheory.Map.compose first after)
      (ProgramReductionTheory.Map.compose second after) where
  comparison := Functor.isoWhiskerRight change.comparison after.closed.functor
  program := by
    change after.closed.functor.map (change.comparison.hom.app _) ≫
      (after.closed.functor.map second.program.hom ≫ after.program.hom) =
        after.closed.functor.map first.program.hom ≫ after.program.hom
    rw [← Category.assoc, ← after.closed.functor.map_comp, change.program]

def precompose (before : ProgramReductionTheory.Map middle source) (change : MapIso first second) :
    MapIso (ProgramReductionTheory.Map.compose before first)
      (ProgramReductionTheory.Map.compose before second) where
  comparison := Functor.isoWhiskerLeft before.closed.functor change.comparison
  program := by
    change change.comparison.hom.app (before.closed.functor.obj _) ≫
      (second.closed.functor.map before.program.hom ≫ second.program.hom) =
        first.closed.functor.map before.program.hom ≫ first.program.hom
    rw [← Category.assoc, ← change.comparison.hom.naturality before.program.hom,
      Category.assoc, change.program]

end MapIso

def mapSetoid (source target : ProgramReductionTheory.Theory.{k,k}) :
    Setoid (ProgramReductionTheory.Map source target) where
  r first second := Nonempty (MapIso first second)
  iseqv := ⟨fun mapping => ⟨MapIso.refl mapping⟩,
    fun ⟨change⟩ => ⟨change.symm⟩,
    fun ⟨before⟩ ⟨after⟩ => ⟨before.trans after⟩⟩

private theorem compose_compatible {source middle target : ProgramReductionTheory.Theory.{k,k}}
    {before before' : ProgramReductionTheory.Map source middle}
    {after after' : ProgramReductionTheory.Map middle target}
    (first : Nonempty (MapIso before before')) (second : Nonempty (MapIso after after')) :
    Nonempty (MapIso (ProgramReductionTheory.Map.compose before after)
      (ProgramReductionTheory.Map.compose before' after')) := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  exact ⟨(first.postcompose after).trans (second.precompose before')⟩

end ProgramReductionTheoryIsoClasses

structure ProgramReductionTheoryIsoClasses where
  original : ProgramReductionTheory.Theory.{k,k}

namespace ProgramReductionTheoryIsoClasses

def of (source : ProgramReductionTheory.Theory.{k,k}) : ProgramReductionTheoryIsoClasses := ⟨source⟩

def compose {source middle target : ProgramReductionTheoryIsoClasses.{k}}
    (before : Quotient (mapSetoid source.original middle.original))
    (after : Quotient (mapSetoid middle.original target.original)) :
    Quotient (mapSetoid source.original target.original) :=
  Quotient.map₂ ProgramReductionTheory.Map.compose
    (fun _ _ before _ _ after => compose_compatible before after) before after

instance category : Category (ProgramReductionTheoryIsoClasses.{k}) where
  Hom source target := Quotient (mapSetoid source.original target.original)
  id source := Quotient.mk _ (ProgramReductionTheory.Map.identity source.original)
  comp before after := compose before after
  id_comp after := Quotient.inductionOn after fun after =>
    congrArg (Quotient.mk _) (ProgramReductionTheory.Map.identity_compose after)
  comp_id before := Quotient.inductionOn before fun before =>
    congrArg (Quotient.mk _) (ProgramReductionTheory.Map.compose_identity before)
  assoc before middle after := Quotient.inductionOn₃ before middle after fun before middle after =>
    congrArg (Quotient.mk _) (ProgramReductionTheory.Map.compose_assoc before middle after)

def classOf {source target : ProgramReductionTheory.Theory.{k,k}}
    (mapping : ProgramReductionTheory.Map source target) : of source ⟶ of target :=
  Quotient.mk _ mapping

theorem classOf_equal_iff {source target : ProgramReductionTheory.Theory.{k,k}}
    (first second : ProgramReductionTheory.Map source target) :
    classOf first = classOf second ↔ Nonempty (MapIso first second) := Quotient.eq

theorem classOf_identity (source : ProgramReductionTheory.Theory.{k,k}) :
    classOf (ProgramReductionTheory.Map.identity source) = 𝟙 (of source) := rfl

theorem classOf_compose {source middle target : ProgramReductionTheory.Theory.{k,k}}
    (before : ProgramReductionTheory.Map source middle) (after : ProgramReductionTheory.Map middle target) :
    classOf (ProgramReductionTheory.Map.compose before after) = classOf before ≫ classOf after := rfl

def forget : ProgramReductionTheoryIsoClasses.{k} ⥤ BicategoryIsoClasses LambdaTheory.{k,k} where
  obj source := ClosedTheoryIsoClasses.of source.original.closed
  map mapping := Quotient.map ProgramReductionTheory.Map.closed
    (fun first second change => by
      obtain ⟨change⟩ := (show Nonempty (MapIso first second) from change)
      exact ⟨LambdaTheory.isoOfNatIso change.comparison⟩) mapping
  map_id _ := Quotient.sound ⟨Iso.refl _⟩
  map_comp before after := Quotient.inductionOn₂ before after fun _ _ => Quotient.sound ⟨Iso.refl _⟩

theorem forget_classOf {source target : ProgramReductionTheory.Theory.{k,k}}
    (mapping : ProgramReductionTheory.Map source target) :
    forget.map (classOf mapping) = ClosedTheoryIsoClasses.classOf mapping.closed := rfl

end ProgramReductionTheoryIsoClasses

end Mettapedia.CategoryTheory
