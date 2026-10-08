import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctor
import Mettapedia.CategoryTheory.RelativeClosedSyntaxClosed
import Mettapedia.CategoryTheory.RelativeClosedSyntaxLimits

/-!
# Native structural readouts of the quotient interpretation

The independently evaluated formal product, function and equalizer objects
are compared to the target's actual choices. Projection, evaluation and
equalizer-inclusion readouts retain the complete native arrows. Their
endpoint comparisons are earned from the deterministic evaluator, rather
than supplied as interpretation or preservation capabilities.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe u v a w z

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (assignment : Assignment C symbols D) (realization : Realization signature assignment)

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
theorem ArrowValue.arrows_heq {source target before after : D}
    {first : source ⟶ target} {second : before ⟶ after}
    (same : (⟨source, target, first⟩ : ArrowValue D) = ⟨before, after, second⟩) :
    HEq first second := by
  have sourceSame : source = before := congrArg ArrowValue.source same
  have targetSame : target = after := congrArg ArrowValue.target same
  subst before
  subst after
  exact heq_of_eq (ArrowValue.arrow_injective same)

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
theorem ArrowValue.cast_source {source target before : D} (arrow : source ⟶ target)
    (same : source = before) :
    (⟨source, target, arrow⟩ : ArrowValue D) =
      ⟨before, target, eqToHom same.symm ≫ arrow⟩ := by
  subst before
  simp only [eqToHom_refl, Category.id_comp]

theorem functor_map_heq {source target : Object signature}
    (raw : RawHom source target) {before after : D} (arrow : before ⟶ after)
    (read : assignment.evaluateArrow raw.code = some ⟨before, after, arrow⟩) :
    HEq ((functor assignment realization).map (classOf raw)) arrow :=
  ArrowValue.arrows_heq
    (Option.some.inj ((functor_complete_readout assignment realization raw).symm.trans read))

theorem functor_representative_readout {source target : Object signature} (arrow : source ⟶ target) :
    assignment.evaluateArrow (representative arrow).code =
      some ⟨(functor assignment realization).obj source,
        (functor assignment realization).obj target, (functor assignment realization).map arrow⟩ :=
  (functor_complete_readout assignment realization (representative arrow)).trans
    (congrArg (fun value : (functor assignment realization).obj source ⟶
        (functor assignment realization).obj target =>
      some (⟨(functor assignment realization).obj source,
        (functor assignment realization).obj target, value⟩ : ArrowValue D))
      (congrArg (functor assignment realization).map (classOf_representative arrow)))

theorem functor_terminal_object :
    (functor assignment realization).obj (terminal signature) = 𝟙_ D := rfl

theorem functor_product_object (left right : Object signature) :
    (functor assignment realization).obj (product left right) =
      (functor assignment realization).obj left ⊗ (functor assignment realization).obj right :=
  objectValue_unique assignment realization (product left right) _
    (assignment.evaluate_product (objectValue_readout assignment realization left)
      (objectValue_readout assignment realization right))

theorem functor_exponential_object (argument result : Object signature) :
    (functor assignment realization).obj (exponentialObject argument result) =
      ((functor assignment realization).obj argument ⟶[D]
        (functor assignment realization).obj result) :=
  objectValue_unique assignment realization (exponentialObject argument result) _
    (assignment.evaluate_exponential (objectValue_readout assignment realization argument)
      (objectValue_readout assignment realization result))

theorem functor_equalizer_object {source target : Object signature} (before after : source ⟶ target) :
    (functor assignment realization).obj (equalizerObject before after) =
      equalizer ((functor assignment realization).map before) ((functor assignment realization).map after) :=
  objectValue_unique assignment realization (equalizerObject before after) _
    (assignment.evaluate_equalizer _ _ (objectValue_readout assignment realization source)
      (objectValue_readout assignment realization target)
      (functor_representative_readout assignment realization before)
      (functor_representative_readout assignment realization after))

theorem functor_first_heq (left right : Object signature) :
    HEq ((functor assignment realization).map (first left right))
      (CartesianMonoidalCategory.fst ((functor assignment realization).obj left)
        ((functor assignment realization).obj right)) :=
  functor_map_heq assignment realization
    ⟨.first left.code right.code, ⟨.first left.formed.some right.formed.some⟩⟩ _
    (assignment.evaluate_first (objectValue_readout assignment realization left)
      (objectValue_readout assignment realization right))

theorem functor_second_heq (left right : Object signature) :
    HEq ((functor assignment realization).map (second left right))
      (CartesianMonoidalCategory.snd ((functor assignment realization).obj left)
        ((functor assignment realization).obj right)) :=
  functor_map_heq assignment realization
    ⟨.second left.code right.code, ⟨.second left.formed.some right.formed.some⟩⟩ _
    (assignment.evaluate_second (objectValue_readout assignment realization left)
      (objectValue_readout assignment realization right))

theorem functor_first (left right : Object signature) :
    (functor assignment realization).map (first left right) =
      eqToHom (functor_product_object assignment realization left right) ≫
        CartesianMonoidalCategory.fst ((functor assignment realization).obj left)
          ((functor assignment realization).obj right) := by
  simpa only [eqToHom_refl, Category.comp_id] using
    (conj_eqToHom_iff_heq _ _ (functor_product_object assignment realization left right) rfl).mpr
      (functor_first_heq assignment realization left right)

theorem functor_second (left right : Object signature) :
    (functor assignment realization).map (second left right) =
      eqToHom (functor_product_object assignment realization left right) ≫
        CartesianMonoidalCategory.snd ((functor assignment realization).obj left)
          ((functor assignment realization).obj right) := by
  simpa only [eqToHom_refl, Category.comp_id] using
    (conj_eqToHom_iff_heq _ _ (functor_product_object assignment realization left right) rfl).mpr
      (functor_second_heq assignment realization left right)

theorem functor_equalizerInclusion_heq {source target : Object signature} (before after : source ⟶ target) :
    HEq ((functor assignment realization).map (equalizerInclusion before after))
      (equalizer.ι ((functor assignment realization).map before) ((functor assignment realization).map after)) :=
  functor_map_heq assignment realization
    ⟨.equalizerArrow source.code target.code (representative before).code (representative after).code,
      ⟨.equalizerArrow source.formed.some target.formed.some
        (representative before).admitted.some (representative after).admitted.some⟩⟩ _
    (assignment.evaluate_equalizer_arrow _ _ (objectValue_readout assignment realization source)
      (objectValue_readout assignment realization target)
      (functor_representative_readout assignment realization before)
      (functor_representative_readout assignment realization after))

theorem functor_equalizerInclusion {source target : Object signature} (before after : source ⟶ target) :
    (functor assignment realization).map (equalizerInclusion before after) =
      eqToHom (functor_equalizer_object assignment realization before after) ≫
        equalizer.ι ((functor assignment realization).map before) ((functor assignment realization).map after) := by
  simpa only [eqToHom_refl, Category.comp_id] using
    (conj_eqToHom_iff_heq _ _ (functor_equalizer_object assignment realization before after) rfl).mpr
      (functor_equalizerInclusion_heq assignment realization before after)

theorem functor_evaluation_heq (argument result : Object signature) :
    HEq ((functor assignment realization).map (GeneratedCategory.evaluation argument result))
      (Interpretation.evaluation ((functor assignment realization).obj argument)
        ((functor assignment realization).obj result)) :=
  functor_map_heq assignment realization
    ⟨.evaluation argument.code result.code, ⟨.evaluation argument.formed.some result.formed.some⟩⟩ _
    (assignment.evaluate_evaluation (objectValue_readout assignment realization argument)
      (objectValue_readout assignment realization result))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
