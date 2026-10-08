import Mettapedia.CategoryTheory.RelativeClosedSyntaxAssignmentTransportActionLaws
import Mettapedia.GSLT.Core.LambdaTheoryBicategory

/-!
# The weak closed theory action on a fixed relative presentation

An independently authored ordered presentation has a genuine category of
locally realized models in each target closed theory. Weak finite-limit and
closed maps transport these models through actual constructor comparisons.
Ordinary target cells act on their complete diagrams. The resulting action
is a pseudofunctor, with its unit, composition, whiskering and associativity
laws proved from those comparisons.

The authored presentation is fixed. This does not construct a signature of
modal type formers, a free-extension biadjunction or its induced monad.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedTheoryModelAction

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open SemanticModels AssignmentTransportAction

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable (headers : HeaderFormation signature)

def models (theory : LambdaTheory.{w,k}) : Cat.{k,max w k} :=
  Cat.of (Model signature theory.Obj)

def homAction (first last : LambdaTheory.{w,k}) :
    (first ⟶ last) ⥤ (models (signature := signature) first ⟶
      models (signature := signature) last) where
  obj mapping := (AssignmentTransportAction.action headers mapping.functor).toCatHom
  map input := (AssignmentTransportAction.change headers input).toCatHom₂
  map_id mapping := by
    apply Cat.Hom₂.ext
    exact change_identity headers
  map_comp before after := by
    apply Cat.Hom₂.ext
    exact change_compose headers before after

def action : Pseudofunctor LambdaTheory.{w,k} Cat.{k,max w k} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (models (signature := signature)) (homAction headers)
  mapId theory := Cat.Hom.isoMk (identityIso headers (D := theory.Obj))
  mapComp first second := Cat.Hom.isoMk (compositionIso headers first.functor second.functor)
  map₂_whisker_left := by
    intro first middle last mapping before after input
    apply Cat.Hom₂.ext
    exact change_whiskerLeft headers mapping.functor input
  map₂_whisker_right := by
    intro first middle last before after input mapping
    apply Cat.Hom₂.ext
    exact change_whiskerRight headers input mapping.functor
  map₂_associator := by
    intro first middle next last earlier later final
    apply Cat.Hom₂.ext
    exact composition_associativity headers earlier.functor later.functor final.functor
  map₂_left_unitor := by
    intro first last mapping
    apply Cat.Hom₂.ext
    exact composition_left_unitor headers mapping.functor
  map₂_right_unitor := by
    intro first last mapping
    apply Cat.Hom₂.ext
    exact composition_right_unitor headers mapping.functor

@[simp] theorem action_map {first last : LambdaTheory.{w,k}}
    (mapping : LambdaTheoryMap first last) :
    (action headers).map mapping =
      (AssignmentTransportAction.action headers mapping.functor).toCatHom := rfl

@[simp] theorem action_change {first last : LambdaTheory.{w,k}}
    {before after : LambdaTheoryMap first last} (input : before.functor ⟶ after.functor) :
    (action headers).map₂ input = (AssignmentTransportAction.change headers input).toCatHom₂ := rfl

theorem model_object_readout {first last : LambdaTheory.{w,k}}
    (mapping : LambdaTheoryMap first last) (model : Model signature first.Obj)
    (origin : symbols.ObjectName) :
    ((AssignmentTransportAction.action headers mapping.functor).obj model).meanings.object origin =
      mapping.functor.obj (model.meanings.object origin) :=
  image_object headers mapping.functor model origin

theorem model_cell_readout {first last : LambdaTheory.{w,k}}
    {before after : LambdaTheoryMap first last} (input : before.functor ⟶ after.functor)
    (model : Model signature first.Obj) (context : GeneratedCategory.Object signature) :
    ((AssignmentTransportAction.change headers input).app model).app context =
      (comparison headers before.functor model).inv.app context ≫
        input.app (model.diagram.obj context) ≫
          (comparison headers after.functor model).hom.app context := rfl

end Mettapedia.GSLT.Core.RelativeClosedTheoryModelAction
