import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationRealization
import Mettapedia.CategoryTheory.RelativeClosedBaseInterpretation

/-!
# Actual base comparison meanings over a weak closed functor

The independently constructed native base diagram is followed by the
supplied finite-limit closed functor. Its constructor-built normalization
gives actual inverse comparison arrows and earns each local declaration
equation. The complete base functor is then recovered as the supplied map.

Formal header values are read independently in the target's native choices.
The input contains no expression compatibility or declaration-realization
law. Independent target object sizes are retained at a common hom universe.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.WeakDiagram

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Interpretation FunctorNormalization

universe k w

variable {C : Type k} [Category.{k} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

private instance native_lex : PreservesFiniteLimits (NativeDiagram.interpretation (C := C)) := by
  dsimp only [NativeDiagram.interpretation]
  infer_instance

private instance native_closed : MonoidalClosedFunctor (NativeDiagram.interpretation (C := C)) := by
  dsimp only [NativeDiagram.interpretation]
  infer_instance

variable (mapping : C ⥤ D) [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]

abbrev mappedDiagram : GeneratedCategory.Object (signature (C := C)) ⥤ D :=
  NativeDiagram.interpretation (C := C) ⋙ mapping

instance mappedDiagram_lex : PreservesFiniteLimits (mappedDiagram mapping) :=
  comp_preservesFiniteLimits (NativeDiagram.interpretation (C := C)) mapping

instance mappedDiagram_closed : MonoidalClosedFunctor (mappedDiagram mapping) :=
  CartesianClosedFunctorCoherence.closed_composition (NativeDiagram.interpretation (C := C)) mapping

abbrev extracted := FunctorNormalization.assignment (mappedDiagram mapping) (headers (C := C))

omit [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]
  [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
theorem mapped_base_recovery : GeneratedCategory.baseFunctor (signature (C := C)) ⋙
    mappedDiagram mapping = mapping := by
  exact (congrArg (fun base : C ⥤ C => base ⋙ mapping)
    (NativeDiagram.base_recovery (C := C))).trans (Functor.id_comp mapping)

def assignment : Assignment C (symbols C) D where
  base := mapping
  object origin := origin.down.elim
  arrow := (extracted mapping).arrow

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
  [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem assignment_ext {first second : Assignment C (symbols C) D}
    (base : first.base = second.base) (objects : first.object = second.object)
    (arrows : first.arrow = second.arrow) : first = second := by
  cases first
  cases second
  cases base
  cases objects
  cases arrows
  rfl

theorem assignment_eq_extracted : assignment mapping = extracted mapping := by
  apply assignment_ext
  · exact (mapped_base_recovery mapping).symm
  · funext origin
    exact origin.down.elim
  · rfl

theorem realization : Realization (signature (C := C)) (assignment mapping) :=
  (assignment_eq_extracted mapping).symm ▸
    reconstruction_realization (mappedDiagram mapping) (headers (C := C))

def nativeSource : Choice C → D
  | .terminal => 𝟙_ D
  | .product first second => mapping.obj first ⊗ mapping.obj second
  | .equalizer before after => equalizer (mapping.map before) (mapping.map after)
  | .exponential argument result => mapping.obj argument ⟶[D] mapping.obj result

theorem source_read (choice : Choice C) :
    (assignment mapping).evaluateObject (sourceCode choice) = some (nativeSource mapping choice) := by
  cases choice with
  | terminal => rfl
  | product first second => exact (assignment mapping).evaluate_product rfl rfl
  | equalizer before after =>
      exact (assignment mapping).evaluate_equalizer (mapping.map before) (mapping.map after)
        rfl rfl rfl rfl
  | exponential argument result => exact (assignment mapping).evaluate_exponential rfl rfl

omit [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping] in
theorem target_read (semantic : Assignment C (symbols C) D) (choice : Choice C) :
    semantic.evaluateObject (targetCode choice) = some (semantic.base.obj (selected choice)) := rfl

theorem arrow_source (choice : Choice C) :
    ((assignment mapping).arrow choice).source = nativeSource mapping choice :=
  Option.some.inj (((realization mapping).source choice).symm.trans (source_read mapping choice))

theorem arrow_target (choice : Choice C) :
    ((assignment mapping).arrow choice).target = mapping.obj (selected choice) :=
  Option.some.inj (((realization mapping).target choice).symm.trans (target_read (assignment mapping) choice))

def inverse (choice : Choice C) : nativeSource mapping choice ⟶ mapping.obj (selected choice) :=
  eqToHom (arrow_source mapping choice).symm ≫ ((assignment mapping).arrow choice).arrow ≫
    eqToHom (arrow_target mapping choice)

theorem inverse_read (choice : Choice C) :
    (assignment mapping).evaluateArrow (.name choice) =
      some ⟨nativeSource mapping choice, mapping.obj (selected choice), inverse mapping choice⟩ := by
  change some ((assignment mapping).arrow choice) = _
  exact congrArg some (arrowValue_transport ((assignment mapping).arrow choice).arrow
    (arrow_source mapping choice) (arrow_target mapping choice))

def interpretation : GeneratedCategory.Object (signature (C := C)) ⥤ D :=
  Interpretation.functor (assignment mapping) (realization mapping)

theorem base_recovery : GeneratedCategory.baseFunctor (signature (C := C)) ⋙
    interpretation mapping = mapping :=
  Interpretation.functor_base (assignment mapping) (realization mapping)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.WeakDiagram
