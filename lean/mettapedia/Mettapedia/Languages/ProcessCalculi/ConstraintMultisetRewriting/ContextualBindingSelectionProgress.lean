import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklist
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingCaseProgress

/-!
# The executable queue selection preserves models and decreases active work

The queue retains a typed binding case and its actual location. Removing
that equation preserves both surrounding portions, under the computed
binding. Every model remains a model of the resulting equations, and the
finite sum of its images on active declarations strictly decreases.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingSelectionProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport
open ContextualBindingWorklist

variable {S : Signature} {V W : Type} [DecidableEq V] {source : V → MetaArity S} {next : W → MetaArity S}

theorem selected_member {problem : Problem source} (selection : ContextualBindingWorklist.Selection problem) :
    (observe selection.left, observe selection.right) ∈ problem := by
  exact Eq.mpr (congrArg (fun problem =>
    (observe selection.left, observe selection.right) ∈ problem) selection.split)
    (List.mem_append_right _ List.mem_cons_self)

theorem retained_member {problem : Problem source} (selection : ContextualBindingWorklist.Selection problem)
    {equation : Equation (Observation S source)}
    (member : equation ∈ selection.before ++ selection.after) : equation ∈ problem := by
  apply Eq.mpr (congrArg (fun problem => equation ∈ problem) selection.split)
  rcases List.mem_append.mp member with first | second
  · exact List.mem_append_left _ first
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ second)

theorem retained_active {problem : Problem source} (selection : ContextualBindingWorklist.Selection problem) :
    active (selection.before ++ selection.after) ⊆ active problem := by
  intro identity present
  obtain ⟨equation, member, inside⟩ := (mem_active identity _).mp present
  exact (mem_active identity _).mpr ⟨equation, retained_member selection member, inside⟩

theorem active_progress {problem : Problem source} (selection : ContextualBindingWorklist.Selection problem)
    (candidate : Assignment source next) :
    potential candidate (active selection.update.remaining) < potential candidate (active problem) := by
  apply binding_active_potential_decreases selection.binding.chosen selection.binding.body
    (selection.before ++ selection.after) (active problem) (retained_active selection)
    (ContextualBindingCaseProgress.body_is_covered selection.binding problem (selected_member selection))
    selection.binding.absent
    (ContextualBindingCaseProgress.source_name_is_active selection.binding problem (selected_member selection))

theorem removes_selected_declaration {problem : Problem source}
    (selection : ContextualBindingWorklist.Selection problem) :
    active selection.update.remaining ⊆ (active problem).erase selection.binding.chosen :=
  binding_removes_selected_name selection.binding.chosen selection.binding.body
    (selection.before ++ selection.after) (active problem) (retained_active selection)
    (ContextualBindingCaseProgress.body_is_covered selection.binding problem (selected_member selection))
    selection.binding.absent

theorem active_card_progress {problem : Problem source}
    (selection : ContextualBindingWorklist.Selection problem) :
    (active selection.update.remaining).card < (active problem).card := by
  have present := ContextualBindingCaseProgress.source_name_is_active selection.binding problem
    (selected_member selection)
  exact lt_of_le_of_lt (Finset.card_le_card (removes_selected_declaration selection))
    (Finset.card_erase_lt_of_mem present)

theorem choose_active_card_progress [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] {problem : Problem source} {update : ContextualBindingWorklist.Update problem}
    (computed : choose problem = some update) :
    (active update.remaining).card < (active problem).card := by
  unfold choose at computed
  obtain ⟨selection, _, rfl⟩ := Option.map_eq_some_iff.mp computed
  exact active_card_progress selection

theorem model_progress {problem : Problem source} (selection : ContextualBindingWorklist.Selection problem)
    (candidate : Assignment source next) (solved : Models candidate problem) :
    Models candidate selection.update.remaining ∧
      (∀ identity, candidate identity = instantiate candidate (selection.update.answer identity)) ∧
      potential candidate (active selection.update.remaining) < potential candidate (active problem) := by
  have equation := observe_injective (solved _ (selected_member selection))
  have fixed := ContextualBindingCaseProgress.candidate_is_fixed selection.binding candidate equation
  have components : ∀ identity, candidate identity = instantiate candidate (selection.update.answer identity) :=
    fun identity => (congrFun fixed identity).symm
  have restSolved : Models candidate (selection.before ++ selection.after) :=
    fun pair member => solved pair (retained_member selection member)
  exact ⟨(models_of_components candidate _ candidate components _).mp restSolved,
    components, active_progress selection candidate⟩

theorem choose_model_progress [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] {problem : Problem source} {update : ContextualBindingWorklist.Update problem}
    (computed : choose problem = some update) (candidate : Assignment source next)
    (solved : Models candidate problem) :
    Models candidate update.remaining ∧
      (∀ identity, candidate identity = instantiate candidate (update.answer identity)) ∧
      potential candidate (active update.remaining) < potential candidate (active problem) := by
  unfold choose at computed
  obtain ⟨selection, _, rfl⟩ := Option.map_eq_some_iff.mp computed
  exact model_progress selection candidate solved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingSelectionProgress
