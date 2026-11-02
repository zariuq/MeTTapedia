import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapePotential
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverBindingProgress

/-!
# Recovered bindings decrease shape work

The stored recovery equation identifies the selected shape image with the
recovered body's shape. Thus the actual binding fixes every shape model.
Its support proof removes one positive image from the active finite sum.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeBindingProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualShapeErasure
open ContextualActiveSupport

variable {S : Signature} {V Next : Type} [DecidableEq V] {source : V → MetaArity S}

theorem recovered_shape {Γ : Ctx S} {sort : S.Srt} {left right : Term (signature S source) Γ sort}
    (binding : ContextualBindingCase.Case left right) (images : ShapeAssignment S V Next)
    (same : evaluate images left = evaluate images right) :
    images binding.chosen = evaluate images binding.body := by
  change evaluateObservation images (observe left) = evaluateObservation images (observe right) at same
  obtain ⟨rho, first | second⟩ := binding.recovered
  · rw [first.1, first.2] at same
    simpa only [evaluateObservation, observe, evaluate_rename, evaluate_generator] using same
  · rw [second.1, second.2] at same
    simpa only [evaluateObservation, observe, evaluate_rename, evaluate_generator] using same.symm

theorem components {Γ : Ctx S} {sort : S.Srt} {left right : Term (signature S source) Γ sort}
    (binding : ContextualBindingCase.Case left right) (images : ShapeAssignment S V Next)
    (same : evaluate images left = evaluate images right) :
    ∀ identity, images identity = evaluate images (ContextualBinding.answer binding.chosen binding.body identity) := by
  intro identity
  by_cases chosen : identity = binding.chosen
  · subst identity
    rw [ContextualBinding.answer_same]
    exact recovered_shape binding images same
  · rw [ContextualBinding.answer_other _ _ chosen _, evaluate_generator]

theorem selection_progress {problem : Problem source} (selection : ContextualBindingWorklist.Selection problem)
    (images : ShapeAssignment S V Next) (patterned : ProblemPattern problem) (models : ShapeModels images problem) :
    ShapeModels images selection.update.remaining ∧
      (∀ identity, images identity = evaluate images (selection.update.answer identity)) ∧
      ContextualShapePotential.potential images (active selection.update.remaining) <
        ContextualShapePotential.potential images (active problem) := by
  have head := ContextualBindingSelectionProgress.selected_member selection
  have fixed := components selection.binding images (models _ head)
  have restPattern : ProblemPattern (selection.before ++ selection.after) :=
    fun equation member => patterned equation (ContextualBindingSelectionProgress.retained_member selection member)
  have restModels : ShapeModels images (selection.before ++ selection.after) :=
    fun equation member => models equation (ContextualBindingSelectionProgress.retained_member selection member)
  refine ⟨(ContextualShapeTransport.models_of_components images _ images fixed _ restPattern).mpr restModels, fixed, ?_⟩
  have bounded := ContextualBindingSelectionProgress.removes_selected_declaration selection
  have smaller := ContextualShapePotential.monotone images bounded
  have present := ContextualBindingCaseProgress.source_name_is_active selection.binding problem head
  have sum := Finset.sum_erase_add (active problem) (fun identity => (images identity).size) present
  have positive := Mettapedia.Logic.LP.Term.size_pos (images selection.binding.chosen)
  unfold ContextualShapePotential.potential at smaller ⊢
  omega

theorem located_progress {Γ : Ctx S} {sort : S.Srt} {left right : Term (signature S source) Γ sort}
    (binding : ContextualBindingCase.Case left right) (before after : Problem source)
    (images : ShapeAssignment S V Next) (patterned : ProblemPattern (before ++ (observe left, observe right) :: after))
    (models : ShapeModels images (before ++ (observe left, observe right) :: after)) :
    let update := (ContextualSolverBindingProgress.choice binding before after).perform
    ShapeModels images update.remaining ∧
      (∀ identity, images identity = evaluate images (update.answer identity)) ∧
      ContextualSolverMeasure.Smaller (ContextualShapePotential.measure images update.remaining)
        (ContextualShapePotential.measure images (before ++ (observe left, observe right) :: after)) := by
  have progressed := selection_progress (ContextualSolverBindingProgress.selection binding before after) images patterned models
  refine ⟨?_, progressed.2.1, ContextualSolverMeasure.of_image_lt ?_⟩
  · rw [ContextualSolverBindingProgress.same_remaining]
    exact progressed.1
  · dsimp only [ContextualShapePotential.measure]
    rw [ContextualSolverBindingProgress.same_remaining]
    exact progressed.2.2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeBindingProgress
