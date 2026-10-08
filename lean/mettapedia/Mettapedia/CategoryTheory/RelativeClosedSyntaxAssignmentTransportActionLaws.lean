import Mettapedia.CategoryTheory.RelativeClosedSyntaxAssignmentTransportCoherence

/-!
# Whiskering and coherent pasting for weak model transport

Every comparison here is built from the independently realized diagrams.
Mapped isomorphism cancellation and ordinary naturality earn the two
whiskering laws. The unit and associativity equations concern the actual
chosen transported models, rather than identifying their raw meanings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.AssignmentTransportAction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Functor
open GeneratedCategory SemanticModels

universe k w z h j

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable (headers : HeaderFormation signature)
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {E : Type z} [Category.{k} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]
variable {H : Type h} [Category.{k} H]
variable [CartesianMonoidalCategory H] [MonoidalClosed H] [HasFiniteLimits H]
variable {J : Type j} [Category.{k} J]
variable [CartesianMonoidalCategory J] [MonoidalClosed J] [HasFiniteLimits J]

private instance composition_lex (first : D ⥤ E) (second : E ⥤ H)
    [PreservesFiniteLimits first] [PreservesFiniteLimits second] :
    PreservesFiniteLimits (first ⋙ second) := comp_preservesFiniteLimits first second

private instance composition_closed (first : D ⥤ E) (second : E ⥤ H)
    [PreservesFiniteLimits first] [PreservesFiniteLimits second]
    [MonoidalClosedFunctor first] [MonoidalClosedFunctor second] :
    MonoidalClosedFunctor (first ⋙ second) :=
  CartesianClosedFunctorCoherence.closed_composition first second

omit [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]
  [CartesianMonoidalCategory H] [MonoidalClosed H] [HasFiniteLimits H] in
private theorem mapped_comparison_cancel (mapping : E ⥤ H)
    {first last : Object signature ⥤ E} (compared : first ≅ last)
    (context : Object signature) {target : H}
    (tail : mapping.obj (first.obj context) ⟶ target) :
    mapping.map (compared.hom.app context) ≫ mapping.map (compared.inv.app context) ≫ tail = tail :=
  Iso.map_hom_inv_id_assoc (compared.app context) mapping tail

theorem change_whiskerLeft (mapping : D ⥤ E)
    [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]
    {before after : E ⥤ H}
    [PreservesFiniteLimits before] [MonoidalClosedFunctor before]
    [PreservesFiniteLimits after] [MonoidalClosedFunctor after]
    (input : before ⟶ after) :
    change headers (whiskerLeft mapping input) =
      (compositionIso headers mapping before).hom ≫
        whiskerLeft (action headers mapping) (change headers input) ≫
          (compositionIso headers mapping after).inv := by
  apply NatTrans.ext
  funext model
  apply NatTrans.ext
  funext context
  change (comparison headers (mapping ⋙ before) model).inv.app context ≫
      input.app (mapping.obj (model.diagram.obj context)) ≫
        (comparison headers (mapping ⋙ after) model).hom.app context =
    ((comparison headers (mapping ⋙ before) model).inv.app context ≫
      before.map ((comparison headers mapping model).hom.app context) ≫
        (comparison headers before (image headers mapping model)).hom.app context) ≫
    ((comparison headers before (image headers mapping model)).inv.app context ≫
      input.app ((image headers mapping model).diagram.obj context) ≫
        (comparison headers after (image headers mapping model)).hom.app context) ≫
    (((comparison headers after (image headers mapping model)).inv.app context ≫
      after.map ((comparison headers mapping model).inv.app context)) ≫
        (comparison headers (mapping ⋙ after) model).hom.app context)
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc (before.map ((comparison headers mapping model).hom.app context)),
    input.naturality, Category.assoc]
  rw [mapped_comparison_cancel]
  rfl

theorem change_whiskerRight {before after : D ⥤ E}
    [PreservesFiniteLimits before] [MonoidalClosedFunctor before]
    [PreservesFiniteLimits after] [MonoidalClosedFunctor after]
    (input : before ⟶ after) (mapping : E ⥤ H)
    [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping] :
    change headers (whiskerRight input mapping) =
      (compositionIso headers before mapping).hom ≫
        whiskerRight (change headers input) (action headers mapping) ≫
          (compositionIso headers after mapping).inv := by
  apply NatTrans.ext
  funext model
  apply NatTrans.ext
  funext context
  change (comparison headers (before ⋙ mapping) model).inv.app context ≫
      mapping.map (input.app (model.diagram.obj context)) ≫
        (comparison headers (after ⋙ mapping) model).hom.app context =
    ((comparison headers (before ⋙ mapping) model).inv.app context ≫
      mapping.map ((comparison headers before model).hom.app context) ≫
        (comparison headers mapping (image headers before model)).hom.app context) ≫
    ((comparison headers mapping (image headers before model)).inv.app context ≫
      mapping.map ((comparison headers before model).inv.app context ≫
        input.app (model.diagram.obj context) ≫ (comparison headers after model).hom.app context) ≫
          (comparison headers mapping (image headers after model)).hom.app context) ≫
    (((comparison headers mapping (image headers after model)).inv.app context ≫
      mapping.map ((comparison headers after model).inv.app context)) ≫
        (comparison headers (after ⋙ mapping) model).hom.app context)
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, mapping.map_comp,
    mapped_comparison_cancel]

theorem composition_associativity (first : D ⥤ E) (second : E ⥤ H) (last : H ⥤ J)
    [PreservesFiniteLimits first] [MonoidalClosedFunctor first]
    [PreservesFiniteLimits second] [MonoidalClosedFunctor second]
    [PreservesFiniteLimits last] [MonoidalClosedFunctor last] :
    change headers (Functor.associator first second last).hom =
      (compositionIso headers (first ⋙ second) last).hom ≫
        whiskerRight (compositionIso headers first second).hom (action headers last) ≫
          (Functor.associator (action headers first) (action headers second)
            (action headers last)).hom ≫
          whiskerLeft (action headers first) (compositionIso headers second last).inv ≫
            (compositionIso headers first (second ⋙ last)).inv := by
  apply NatTrans.ext
  funext model
  apply NatTrans.ext
  funext context
  change (comparison headers (first ⋙ second ⋙ last) model).inv.app context ≫
      𝟙 _ ≫ (comparison headers (first ⋙ second ⋙ last) model).hom.app context =
    ((comparison headers ((first ⋙ second) ⋙ last) model).inv.app context ≫
      last.map ((comparison headers (first ⋙ second) model).hom.app context) ≫
        (comparison headers last (image headers (first ⋙ second) model)).hom.app context) ≫
    ((comparison headers last (image headers (first ⋙ second) model)).inv.app context ≫
      last.map ((comparison headers (first ⋙ second) model).inv.app context ≫
        second.map ((comparison headers first model).hom.app context) ≫
          (comparison headers second (image headers first model)).hom.app context) ≫
        (comparison headers last (image headers second (image headers first model))).hom.app context) ≫
    𝟙 _ ≫
    (((comparison headers last (image headers second (image headers first model))).inv.app context ≫
      last.map ((comparison headers second (image headers first model)).inv.app context)) ≫
        (comparison headers (second ⋙ last) (image headers first model)).hom.app context) ≫
    (((comparison headers (second ⋙ last) (image headers first model)).inv.app context ≫
      last.map (second.map ((comparison headers first model).inv.app context))) ≫
        (comparison headers (first ⋙ second ⋙ last) model).hom.app context)
  simp only [Category.assoc, Category.id_comp, Iso.hom_inv_id_app_assoc,
    last.map_comp, mapped_comparison_cancel]
  rw [show last.map (second.map ((comparison headers first model).hom.app context)) ≫
        last.map (second.map ((comparison headers first model).inv.app context)) ≫
          (comparison headers (first ⋙ second ⋙ last) model).hom.app context =
          (comparison headers (first ⋙ second ⋙ last) model).hom.app context from
      mapped_comparison_cancel (second ⋙ last) (comparison headers first model) context _]
  rfl

theorem composition_left_unitor (mapping : D ⥤ E)
    [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping] :
    change headers (Functor.leftUnitor mapping).hom =
      (compositionIso headers (𝟭 D) mapping).hom ≫
        whiskerRight (identityIso headers (D := D)).hom (action headers mapping) ≫
          (Functor.leftUnitor (action headers mapping)).hom := by
  apply NatTrans.ext
  funext model
  apply NatTrans.ext
  funext context
  change (comparison headers mapping model).inv.app context ≫ 𝟙 _ ≫
      (comparison headers mapping model).hom.app context =
    ((comparison headers mapping model).inv.app context ≫
      mapping.map ((comparison headers (𝟭 D) model).hom.app context) ≫
        (comparison headers mapping (image headers (𝟭 D) model)).hom.app context) ≫
    ((comparison headers mapping (image headers (𝟭 D) model)).inv.app context ≫
      mapping.map ((comparison headers (𝟭 D) model).inv.app context) ≫
        (comparison headers mapping model).hom.app context) ≫ 𝟙 _
  simp only [Category.assoc, Category.id_comp, Category.comp_id,
    Iso.hom_inv_id_app_assoc, mapped_comparison_cancel]

theorem composition_right_unitor (mapping : D ⥤ E)
    [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping] :
    change headers (Functor.rightUnitor mapping).hom =
      (compositionIso headers mapping (𝟭 E)).hom ≫
        whiskerLeft (action headers mapping) (identityIso headers (D := E)).hom ≫
          (Functor.rightUnitor (action headers mapping)).hom := by
  apply NatTrans.ext
  funext model
  apply NatTrans.ext
  funext context
  change (comparison headers mapping model).inv.app context ≫ 𝟙 _ ≫
      (comparison headers mapping model).hom.app context =
    ((comparison headers mapping model).inv.app context ≫
      (comparison headers mapping model).hom.app context ≫
        (comparison headers (𝟭 E) (image headers mapping model)).hom.app context) ≫
      (comparison headers (𝟭 E) (image headers mapping model)).inv.app context ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id, Iso.inv_hom_id_app_assoc]
  exact (Iso.inv_hom_id_app (comparison headers mapping model) context).trans
    (Iso.hom_inv_id_app (comparison headers (𝟭 E) (image headers mapping model)) context).symm

end Mettapedia.CategoryTheory.RelativeClosedSyntax.AssignmentTransportAction
