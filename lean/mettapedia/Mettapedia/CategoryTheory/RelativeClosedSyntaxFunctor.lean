import Mettapedia.CategoryTheory.RelativeClosedSyntaxSoundness
import Mettapedia.CategoryTheory.RelativeClosedSyntaxCategory

/-!
# Actual quotient interpretation functor of relative closed syntax

Generated formation and the earned local-rule soundness theorem provide
successful evaluator reads. Values are extracted from that deterministic
evaluator. Generated equations then descend through the actual typed-arrow
quotient, earning a category functor and its identity/composition laws.

No arbitrary-arrow interpretation or functoriality is supplied as model data.
The base diagram is read back as its independently supplied functor. The
comparison with old base limits and exponentials is a separate obligation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a w z

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

variable (assignment : Assignment C symbols D) (realization : Realization signature assignment)

include assignment realization

theorem objectValue_isSome (object : GeneratedCategory.Object signature) :
    (assignment.evaluateObject object.code).isSome :=
  Option.isSome_iff_exists.mpr (sound assignment realization object.formed.some)

def objectValue (object : GeneratedCategory.Object signature) : D :=
  (assignment.evaluateObject object.code).get (objectValue_isSome assignment realization object)

theorem objectValue_readout (object : GeneratedCategory.Object signature) :
    assignment.evaluateObject object.code = some (objectValue assignment realization object) :=
  (Option.some_get _).symm

theorem objectValue_unique (object : GeneratedCategory.Object signature) (value : D)
    (read : assignment.evaluateObject object.code = some value) :
    objectValue assignment realization object = value :=
  Option.some.inj ((objectValue_readout assignment realization object).symm.trans read)

theorem rawArrowValue_isSome {source target : GeneratedCategory.Object signature}
    (arrow : GeneratedCategory.RawHom source target) :
    (ArrowValue.readAt (assignment.evaluateArrow arrow.code)
      (objectValue assignment realization source) (objectValue assignment realization target)).isSome := by
  obtain ⟨value, read⟩ := Interprets.arrowAt (sound assignment realization arrow.admitted.some)
    (objectValue_readout assignment realization source)
    (objectValue_readout assignment realization target)
  exact Option.isSome_iff_exists.mpr ⟨value, by rw [read]; exact ArrowValue.readAt_supplied value⟩

def rawArrowValue {source target : GeneratedCategory.Object signature}
    (arrow : GeneratedCategory.RawHom source target) :
    objectValue assignment realization source ⟶ objectValue assignment realization target :=
  (ArrowValue.readAt (assignment.evaluateArrow arrow.code)
    (objectValue assignment realization source) (objectValue assignment realization target)).get
      (rawArrowValue_isSome assignment realization arrow)

theorem rawArrowValue_checked {source target : GeneratedCategory.Object signature}
    (arrow : GeneratedCategory.RawHom source target) :
    ArrowValue.readAt (assignment.evaluateArrow arrow.code)
        (objectValue assignment realization source) (objectValue assignment realization target) =
      some (rawArrowValue assignment realization arrow) :=
  (Option.some_get _).symm

theorem rawArrowValue_readout {source target : GeneratedCategory.Object signature}
    (arrow : GeneratedCategory.RawHom source target) :
    assignment.evaluateArrow arrow.code = some ⟨objectValue assignment realization source,
      objectValue assignment realization target, rawArrowValue assignment realization arrow⟩ :=
  ArrowValue.readAt_eq_some (rawArrowValue_checked assignment realization arrow)

theorem rawArrowValue_unique {source target : GeneratedCategory.Object signature}
    (arrow : GeneratedCategory.RawHom source target)
    (value : objectValue assignment realization source ⟶ objectValue assignment realization target)
    (read : assignment.evaluateArrow arrow.code =
      some ⟨objectValue assignment realization source, objectValue assignment realization target, value⟩) :
    rawArrowValue assignment realization arrow = value :=
  ArrowValue.arrow_injective
    (Option.some.inj ((rawArrowValue_readout assignment realization arrow).symm.trans read))

theorem rawArrowValue_equation {source target : GeneratedCategory.Object signature}
    {before after : GeneratedCategory.RawHom source target}
    (same : GeneratedCategory.RawHom.Equivalent before after) :
    rawArrowValue assignment realization before = rawArrowValue assignment realization after :=
  Interprets.equal_arrows _ _ (sound assignment realization same.some)
    (rawArrowValue_readout assignment realization before)
    (rawArrowValue_readout assignment realization after)

def arrowValue {source target : GeneratedCategory.Object signature} (arrow : source ⟶ target) :
    objectValue assignment realization source ⟶ objectValue assignment realization target :=
  Quotient.lift (rawArrowValue assignment realization)
    (fun _ _ same => rawArrowValue_equation assignment realization same) arrow

@[simp] theorem arrowValue_classOf {source target : GeneratedCategory.Object signature}
    (arrow : GeneratedCategory.RawHom source target) :
    arrowValue assignment realization (GeneratedCategory.classOf arrow) =
      rawArrowValue assignment realization arrow := rfl

def functor : GeneratedCategory.Object signature ⥤ D where
  obj := objectValue assignment realization
  map := arrowValue assignment realization
  map_id object := by
    change rawArrowValue assignment realization (GeneratedCategory.RawHom.identity object) =
      𝟙 (objectValue assignment realization object)
    exact rawArrowValue_unique assignment realization _ _
      (assignment.evaluate_identity (objectValue_readout assignment realization object))
  map_comp before after := by
    refine Quotient.inductionOn₂ before after ?_
    intro first second
    change rawArrowValue assignment realization (GeneratedCategory.RawHom.compose first second) =
      rawArrowValue assignment realization first ≫ rawArrowValue assignment realization second
    exact rawArrowValue_unique assignment realization _ _
      (assignment.evaluate_compose _ _ (rawArrowValue_readout assignment realization first)
        (rawArrowValue_readout assignment realization second))

theorem functor_classOf {source target : GeneratedCategory.Object signature}
    (arrow : GeneratedCategory.RawHom source target) :
    (functor assignment realization).map (GeneratedCategory.classOf arrow) =
      rawArrowValue assignment realization arrow := rfl

theorem functor_complete_readout {source target : GeneratedCategory.Object signature}
    (arrow : GeneratedCategory.RawHom source target) :
    assignment.evaluateArrow arrow.code = some ⟨(functor assignment realization).obj source,
      (functor assignment realization).obj target,
      (functor assignment realization).map (GeneratedCategory.classOf arrow)⟩ :=
  rawArrowValue_readout assignment realization arrow

theorem functor_base_object (object : C) :
    (functor assignment realization).obj (GeneratedCategory.baseObject signature object) =
      assignment.base.obj object := rfl

theorem functor_base_arrow {source target : C} (arrow : source ⟶ target) :
    (functor assignment realization).map (GeneratedCategory.baseArrow (signature := signature) arrow) =
      assignment.base.map arrow :=
  rawArrowValue_unique assignment realization _ _ (assignment.evaluate_base_arrow arrow)

theorem functor_base : GeneratedCategory.baseFunctor signature ⋙ functor assignment realization =
    assignment.base := by
  refine _root_.CategoryTheory.Functor.ext
    (F := GeneratedCategory.baseFunctor signature ⋙ functor assignment realization)
    (G := assignment.base) (fun object =>
    functor_base_object assignment realization object) ?_
  intro source target arrow
  change (functor assignment realization).map (GeneratedCategory.baseArrow arrow) =
    𝟙 (assignment.base.obj source) ≫ assignment.base.map arrow ≫ 𝟙 (assignment.base.obj target)
  rw [Category.id_comp, Category.comp_id]
  exact functor_base_arrow assignment realization arrow

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
