import Mettapedia.CategoryTheory.RelativeClosedBaseClosed
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctor

/-!
# A genuine native model of the base comparison declarations

The original closed category interprets its own diagram. Formal terminal,
product, exponential and equalizer objects are evaluated independently by
the parser; the declared inverse arrows are given native identity meanings.
Product eta, function eta and equalizer monicity prove the authored inverse
equations. This is a consistency interpretation of the local comparison
presentation, not a type-former extension or an assumed universal property.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.NativeDiagram

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Interpretation

universe u v

variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]

def assignment : Assignment C (symbols C) C where
  base := Functor.id C
  object origin := origin.down.elim
  arrow choice := ⟨selected choice, selected choice, 𝟙 (selected choice)⟩

theorem source_read (choice : Choice C) :
    (assignment (C := C)).evaluateObject (sourceCode choice) = some (selected choice) := by
  cases choice with
  | terminal => rfl
  | product first second => exact (assignment (C := C)).evaluate_product rfl rfl
  | equalizer before after =>
      exact (assignment (C := C)).evaluate_equalizer before after rfl rfl rfl rfl
  | exponential argument result => exact (assignment (C := C)).evaluate_exponential rfl rfl

theorem target_read (choice : Choice C) :
    (assignment (C := C)).evaluateObject (targetCode choice) = some (selected choice) := rfl

theorem inverse_read (choice : Choice C) :
    (assignment (C := C)).evaluateArrow (.name choice) =
      some ⟨selected choice, selected choice, 𝟙 (selected choice)⟩ := rfl

omit [HasFiniteLimits C] in
theorem native_abstraction_evaluation (argument result : C) :
    Interpretation.abstraction (Interpretation.evaluation argument result) =
      𝟙 (argument ⟶[C] result) := by
  simpa only [Category.comp_id, CartesianMonoidalCategory.lift_fst_snd, Category.id_comp] using
    Interpretation.abstraction_eta (𝟙 (argument ⟶[C] result))

theorem forward_read (choice : Choice C) :
    (assignment (C := C)).evaluateArrow (forwardCode choice) =
      some ⟨selected choice, selected choice, 𝟙 (selected choice)⟩ := by
  cases choice with
  | terminal =>
      simpa only [forwardCode, selected, assignment, Functor.id_obj,
        CartesianMonoidalCategory.toUnit_unit] using
        (assignment (C := C)).evaluate_terminal_arrow
          ((assignment (C := C)).evaluate_base_object (𝟙_ C))
  | product first second =>
      simpa only [forwardCode, selected, assignment, Functor.id_obj, Functor.id_map,
        CartesianMonoidalCategory.lift_fst_snd] using
        (assignment (C := C)).evaluate_pair
          (CartesianMonoidalCategory.fst first second) (CartesianMonoidalCategory.snd first second)
          ((assignment (C := C)).evaluate_base_arrow (CartesianMonoidalCategory.fst first second))
          ((assignment (C := C)).evaluate_base_arrow (CartesianMonoidalCategory.snd first second))
  | equalizer before after =>
      have native : equalizer.lift (equalizer.ι before after) (equalizer.condition before after) =
          𝟙 (Limits.equalizer before after) := by
        apply equalizer.hom_ext
        rw [equalizer.lift_ι, Category.id_comp]
      simpa only [forwardCode, selected, native] using
        (assignment (C := C)).evaluate_equalizer_lift before after (equalizer.ι before after)
          (equalizer.condition before after) rfl rfl rfl rfl rfl rfl
  | exponential argument result =>
      have body : (assignment (C := C)).evaluateArrow
          (.compose (.name (.product (argument ⟶[C] result) argument))
            (.base (Interpretation.evaluation argument result))) =
        some ⟨(argument ⟶[C] result) ⊗ argument, result,
          Interpretation.evaluation argument result⟩ := by
        simpa only [selected, assignment, Functor.id_obj, Functor.id_map, Category.id_comp] using
          (assignment (C := C)).evaluate_compose _ _
            (inverse_read (.product (argument ⟶[C] result) argument))
            ((assignment (C := C)).evaluate_base_arrow (Interpretation.evaluation argument result))
      simpa only [forwardCode, selected, native_abstraction_evaluation] using
        (assignment (C := C)).evaluate_abstraction (Interpretation.evaluation argument result)
          rfl rfl rfl body

theorem equation_object_read (origin : Choice C × Bool) :
    (assignment (C := C)).evaluateObject (equationObject origin) = some (selected origin.1) := by
  rcases origin with ⟨choice, side⟩
  cases side
  · exact target_read choice
  · exact source_read choice

theorem left_read (origin : Choice C × Bool) :
    (assignment (C := C)).evaluateArrow (leftCode origin) =
      some ⟨selected origin.1, selected origin.1, 𝟙 (selected origin.1)⟩ := by
  rcases origin with ⟨choice, side⟩
  cases side
  · simpa only [leftCode, Bool.false_eq_true, ↓reduceIte, Category.id_comp] using
      (assignment (C := C)).evaluate_compose _ _ (forward_read choice) (inverse_read choice)
  · simpa only [leftCode, ↓reduceIte, Category.id_comp] using
      (assignment (C := C)).evaluate_compose _ _ (inverse_read choice) (forward_read choice)

theorem right_read (origin : Choice C × Bool) :
    (assignment (C := C)).evaluateArrow (rightCode origin) =
      some ⟨selected origin.1, selected origin.1, 𝟙 (selected origin.1)⟩ :=
  (assignment (C := C)).evaluate_identity (equation_object_read origin)

theorem realization : Realization (signature (C := C)) (assignment (C := C)) where
  source := source_read
  target := target_read
  equation origin := ⟨⟨selected origin.1, selected origin.1, 𝟙 (selected origin.1)⟩,
    equation_object_read origin, equation_object_read origin, left_read origin, right_read origin⟩

def interpretation : GeneratedCategory.Object (signature (C := C)) ⥤ C :=
  Interpretation.functor (assignment (C := C)) (realization (C := C))

theorem base_recovery : base (C := C) ⋙ interpretation (C := C) = Functor.id C :=
  Interpretation.functor_base (assignment (C := C)) (realization (C := C))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.NativeDiagram
