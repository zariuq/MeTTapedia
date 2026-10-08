import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationNativeExtension
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionModels

/-!
# Independent model recovery across the coded native augmentation

Restricting a target augmented model along the genuine coded augmentation
and then dropping native declarations agrees with restricting its original
model along the original expression translation. The proof compares actual
independent evaluator readouts. Complete native model recovery then detects
equality from the original model, without equating the raw generated objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation SemanticModels

universe k w

variable {C D : Type k} [Category.{k} C] [Category.{k} D]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {symbols nextSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable {E : Type w} [Category.{k} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
  [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
  [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E] in
private theorem assignment_ext {names : Symbols.{k}} {first last : Assignment C names E}
    (base : first.base = last.base) (objects : first.object = last.object)
    (arrows : first.arrow = last.arrow) : first = last := by
  cases first
  cases last
  cases base
  cases objects
  cases arrows
  rfl

variable (mapping : Translation signature next)
variable [PreservesFiniteLimits mapping.data.base] [MonoidalClosedFunctor mapping.data.base]
variable (model : Model (BaseExtension.extend next) E)

abbrev restrictAfter :=
  (BaseExtension.Models.restrict ((NativeExtension.extended mapping).precomposeModel model)).model

abbrev translateAfter := mapping.precomposeModel (BaseExtension.Models.restrict model).model

theorem restriction_object (origin : symbols.ObjectName) :
    (restrictAfter mapping model).meanings.object origin =
      (translateAfter mapping model).meanings.object origin := by
  have before : model.meanings.evaluateObject (BaseExtension.originalObjectCode (mapping.data.objects origin)) =
      some ((restrictAfter mapping model).meanings.object origin) :=
    objectValue_readout model.meanings model.realization
      ((NativeExtension.extended mapping).translatedObject (BaseExtension.originalObjects origin))
  have after : model.meanings.evaluateObject (BaseExtension.originalObjectCode (mapping.data.objects origin)) =
      some ((translateAfter mapping model).meanings.object origin) :=
    ((BaseExtension.originalMap next).evaluateObject_precompose model.meanings (mapping.data.objects origin)).trans
      (objectValue_readout (BaseExtension.Models.restrict model).model.meanings
        (BaseExtension.Models.restrict model).model.realization (mapping.translatedObject origin))
  exact Option.some.inj (before.symm.trans after)

theorem restriction_arrow (origin : symbols.ArrowName) :
    (restrictAfter mapping model).meanings.arrow origin =
      (translateAfter mapping model).meanings.arrow origin := by
  have before : model.meanings.evaluateArrow (BaseExtension.originalArrowCode (mapping.data.arrows origin)) =
      some ((restrictAfter mapping model).meanings.arrow origin) :=
    rawArrowValue_readout model.meanings model.realization
      ((NativeExtension.extended mapping).translatedArrow (BaseExtension.originalArrows origin))
  have after : model.meanings.evaluateArrow (BaseExtension.originalArrowCode (mapping.data.arrows origin)) =
      some ((translateAfter mapping model).meanings.arrow origin) :=
    ((BaseExtension.originalMap next).evaluateArrow_precompose model.meanings (mapping.data.arrows origin)).trans
      (rawArrowValue_readout (BaseExtension.Models.restrict model).model.meanings
        (BaseExtension.Models.restrict model).model.realization (mapping.translatedArrow origin))
  exact Option.some.inj (before.symm.trans after)

theorem restriction_model : restrictAfter mapping model = translateAfter mapping model := by
  apply Model.ext
  apply assignment_ext
  · exact (Functor.id_comp (mapping.data.base ⋙ model.meanings.base)).trans
      (congrArg (fun following => mapping.data.base ⋙ following) (Functor.id_comp model.meanings.base).symm)
  · exact funext (restriction_object mapping model)
  · exact funext (restriction_arrow mapping model)

private theorem extension_assignment_congr {first last : Assignment C symbols E}
    [PreservesFiniteLimits first.base] [MonoidalClosedFunctor first.base]
    [PreservesFiniteLimits last.base] [MonoidalClosedFunctor last.base]
    (same : first = last) :
    BaseExtension.WeakExtension.assignment first = BaseExtension.WeakExtension.assignment last := by
  cases same
  rfl

theorem restriction_injective :
    Function.Injective (fun supplied : Model (BaseExtension.extend signature) E =>
      (BaseExtension.Models.restrict supplied).model) := by
  intro before after same
  have original := congrArg Model.meanings same
  have augmented := extension_assignment_congr original
  apply Model.ext
  exact (BaseExtension.Models.assignment_recovered before).symm.trans
    (augmented.trans (BaseExtension.Models.assignment_recovered after))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeModels
