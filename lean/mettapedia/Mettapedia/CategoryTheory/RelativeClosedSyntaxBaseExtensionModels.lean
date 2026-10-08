import Mettapedia.CategoryTheory.RelativeClosedBaseRealizationUniqueness
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionWeakInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSemanticModels

/-!
# Recovery of independent native base-extension models

Any locally realized augmented model has a finite-limit closed base functor:
the generated base preserves these structures and its interpretation is an
actual finite-limit closed functor. Restriction recovers the old declarations.
Conversely, their weak closed base supplies the forced native inverses.

Both model-object roundtrips are proved from complete declaration values and
the independent evaluators. This object equivalence does not assert a
category equivalence on unrestricted primitive cells or a modal adjunction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseExtension.Models

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation SemanticModels

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

structure WeakModel where
  model : Model signature D
  baseFinite : PreservesFiniteLimits model.meanings.base
  baseClosed : MonoidalClosedFunctor model.meanings.base

attribute [instance] WeakModel.baseFinite WeakModel.baseClosed

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
  [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem assignment_ext {names : Symbols.{k}} {first second : Assignment C names D}
    (base : first.base = second.base) (objects : first.object = second.object)
    (arrows : first.arrow = second.arrow) : first = second := by
  cases first
  cases second
  cases base
  cases objects
  cases arrows
  rfl

instance augmented_base_finite (model : Model (extend signature) D) :
    PreservesFiniteLimits model.meanings.base := by
  have : PreservesFiniteLimits (baseFunctor (extend signature) ⋙ model.diagram) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (eqToIso (functor_base model.meanings model.realization))

instance augmented_base_closed (model : Model (extend signature) D) :
    MonoidalClosedFunctor model.meanings.base := by
  have : MonoidalClosedFunctor (baseFunctor (extend signature) ⋙ model.diagram) :=
    CartesianClosedFunctorCoherence.closed_composition _ _
  exact CartesianClosedFunctorCoherence.closed_of_naturalIso
    (eqToIso (functor_base model.meanings model.realization)).symm

def restrict (model : Model (extend signature) D) : WeakModel (signature := signature) (D := D) where
  model := ⟨(originalMap signature).precompose model.meanings,
    (originalMap signature).realization_precompose model.meanings model.realization⟩
  baseFinite := by
    change PreservesFiniteLimits (Functor.id C ⋙ model.meanings.base)
    exact comp_preservesFiniteLimits _ _
  baseClosed := by
    change MonoidalClosedFunctor (Functor.id C ⋙ model.meanings.base)
    exact CartesianClosedFunctorCoherence.closed_of_naturalIso
      (eqToIso (Functor.id_comp model.meanings.base))

def extendModel (model : WeakModel (signature := signature) (D := D)) : Model (extend signature) D :=
  ⟨WeakExtension.assignment model.model.meanings,
    WeakExtension.realization model.model.meanings model.model.realization⟩

theorem assignment_recovered (model : Model (extend signature) D) :
    (extendModel (restrict model)).meanings = model.meanings := by
  let old := (restrict model).model.meanings
  have base : ((comparisonMap signature).precompose model.meanings).base =
      (BaseComparisons.WeakDiagram.assignment old.base).base := rfl
  have native := BaseComparisons.RealizationUniqueness.assignment_equal
    ((comparisonMap signature).precompose model.meanings)
    ((comparisonMap signature).realization_precompose model.meanings model.realization)
    (BaseComparisons.WeakDiagram.assignment old.base)
    (BaseComparisons.WeakDiagram.realization old.base) base
  apply assignment_ext
  · exact Functor.id_comp model.meanings.base
  · rfl
  · funext origin
    cases origin with
    | inl choice =>
        exact (congrArg (fun supplied : Assignment C (BaseComparisons.symbols C) D =>
          supplied.arrow choice) native).symm
    | inr origin => rfl

theorem augmented_model_recovered (model : Model (extend signature) D) :
    extendModel (restrict model) = model := Model.ext (assignment_recovered model)

theorem original_model_recovered (model : WeakModel (signature := signature) (D := D)) :
    (restrict (extendModel model)).model = model.model :=
  Model.ext (WeakExtension.original_precompose (signature := signature) model.model.meanings)

omit [HasFiniteLimits C] in
private theorem weakModel_ext {first last : WeakModel (signature := signature) (D := D)}
    (same : first.model = last.model) : first = last := by
  rcases first with ⟨before, finite, closed⟩
  rcases last with ⟨after, laterFinite, laterClosed⟩
  change before = after at same
  subst after
  rfl

theorem weak_model_recovered (model : WeakModel (signature := signature) (D := D)) :
    restrict (extendModel model) = model := weakModel_ext (original_model_recovered model)

def objectEquivalence : WeakModel (signature := signature) (D := D) ≃ Model (extend signature) D where
  toFun := extendModel
  invFun := restrict
  left_inv := weak_model_recovered
  right_inv := augmented_model_recovered

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseExtension.Models
