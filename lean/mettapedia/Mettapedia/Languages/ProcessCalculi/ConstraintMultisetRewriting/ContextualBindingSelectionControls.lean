import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingSelectionProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklistControls

/-!
# Queue selection retains both sides of an initially blocked constraint

The computed choice skips a repeated spine, binds the later distinct spine,
and keeps both the earlier equation and a later closed equation. A separately
specified model remains valid and loses one active declaration image. The
repeated equation alone still has no falsely unique binding.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingSelectionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualBindingWorklist
open ContextualActiveSupport

abbrev base := Controls.base
abbrev declaration := Controls.declaration
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def problem : Problem declaration := Controls.unblockProblem ++
  [(observe (Controls.closed (Γ := [])), observe (Controls.constant (Γ := [])))]

def candidate : Assignment declaration declaration
  | false => Controls.constant
  | true => Controls.constant

theorem the_original_queue_has_an_independent_model : Models candidate problem := by
  intro equation member
  simp only [problem, Controls.unblockProblem, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | rfl <;> rfl

theorem selection_reaches_the_later_distinct_spine :
    (select problem).map (fun selected => selected.before.length) = some 1 := by
  decide +kernel

theorem the_suffix_is_retained_as_well :
    (select problem).map (fun selected => selected.after.length) = some 1 := by
  decide +kernel

theorem it_selects_the_open_declaration :
    (select problem).map (fun selected => selected.binding.chosen) = some false := by
  decide +kernel

theorem both_unselected_equations_survive_the_actual_update :
    (choose problem).map (fun update => update.remaining.length) = some 2 := by
  decide +kernel

theorem the_actual_update_decreases_the_same_models_active_work :
    ∃ update, choose problem = some update ∧ Models candidate update.remaining ∧
      (∀ identity, candidate identity = instantiate candidate (update.answer identity)) ∧
      potential candidate (active update.remaining) < potential candidate (active problem) := by
  have present : (choose problem).isSome = true := by decide +kernel
  cases computed : choose problem with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at present
  | some update =>
      exact ⟨update, rfl, ContextualBindingSelectionProgress.choose_model_progress computed candidate
        the_original_queue_has_an_independent_model⟩

theorem the_repeated_spine_alone_has_no_unique_choice :
    (select Controls.repeatedProblem).isSome = false := by
  decide +kernel

theorem unavailable_capture_alone_has_no_choice :
    (select Controls.captureProblem).isSome = false := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingSelectionControls
