import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationModels
import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationComposition

/-!
# Complete model identity and composition for coded translations

Independently interpreted target expressions determine every local primitive
meaning. The earned all-expression evaluator laws prove that restricting a
model by an identity or a composite recovers the whole independent model,
including every supplied arrow and declared local equation. These are model
equalities, rather than asserted equality of raw generated objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.ModelLaws

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation SemanticModels

universe k w

private theorem assignment_ext {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
    {E : Type w} [Category.{k} E] {first last : Assignment C symbols E}
    (base : first.base = last.base) (objects : first.object = last.object)
    (arrows : first.arrow = last.arrow) : first = last := by
  cases first
  cases last
  cases base
  cases objects
  cases arrows
  rfl

variable {C D H : Type k} [Category.{k} C] [Category.{k} D] [Category.{k} H]
variable {symbols nextSymbols lastSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable {final : Signature (C := H) (symbols := lastSymbols)}
variable {E : Type w} [Category.{k} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]

theorem identity (headers : HeaderFormation signature) (model : Model signature E) :
    (Translation.identity headers).precomposeModel model = model := by
  apply Model.ext
  apply assignment_ext
  · exact Functor.id_comp model.meanings.base
  · funext origin
    exact objectValue_unique model.meanings model.realization
      ((Translation.identity headers).translatedObject origin) (model.meanings.object origin) rfl
  · funext origin
    exact Option.some.inj
      ((rawArrowValue_readout model.meanings model.realization
        ((Translation.identity headers).translatedArrow origin)).symm.trans rfl)

theorem compose (first : Translation signature next) (last : Translation next final)
    (model : Model final E) :
    first.precomposeModel (last.precomposeModel model) = (first.compose last).precomposeModel model := by
  apply Model.ext
  apply assignment_ext
  · rfl
  · funext origin
    have evaluated := last.evaluateObject_precompose model.meanings model.realization (first.data.objects origin)
    have before := objectValue_readout (last.precomposeModel model).meanings
      (last.precomposeModel model).realization (first.translatedObject origin)
    have after := objectValue_readout model.meanings model.realization ((first.compose last).translatedObject origin)
    exact Option.some.inj (before.symm.trans (evaluated.symm.trans after))
  · funext origin
    have evaluated := last.evaluateArrow_precompose model.meanings model.realization (first.data.arrows origin)
    have before := rawArrowValue_readout (last.precomposeModel model).meanings
      (last.precomposeModel model).realization (first.translatedArrow origin)
    have after := rawArrowValue_readout model.meanings model.realization ((first.compose last).translatedArrow origin)
    exact Option.some.inj (before.symm.trans (evaluated.symm.trans after))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.ModelLaws
