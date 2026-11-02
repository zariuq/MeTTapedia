import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSelection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDecompositionControls
import Mettapedia.OSLF.Syntax.BindingArgumentSlotPositions
import Mettapedia.OSLF.Syntax.BindingVariableSpines

/-!
# Typed frame and spine controls

Selecting a declaration moves its identity while preserving mixed parameter
contexts and sorts. Both equation sides are transported and every solution
factors. Repeated field declarations keep distinct positions. Variable-spine
recognition accepts repetition, and declines a compound argument without
declaring that application or its equation impossible.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSelection.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

abbrev base := ContextualDecomposition.Controls.mixedSignature

def source (identity : Fin 3) : MetaArity base :=
  if identity.val = 0 then ([false, true], true)
  else if identity.val = 1 then ([], false) else ([true], true)

def chosen : Fin 3 := 2
abbrev target := declarations source chosen
abbrev before := signature base source
abbrev after := signature base target

def left : Term before [false, true] true :=
  .op (.inr (.mk 0)) (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))
def right : Term before [false, true] true :=
  .op (.inr (.mk chosen)) (.cons (.var (.succ .zero)) .nil)
def problem : ContextualResidual.Problem source := [(observe left, observe right)]

theorem the_selected_declaration_moves_to_its_port : split chosen chosen = .inl () := chosen_to_port chosen

theorem the_selected_port_retains_its_parameter_context_and_sort : target (.inl ()) = ([true], true) := rfl

theorem an_unselected_mixed_context_is_not_erased :
    target (.inr ⟨0, by decide⟩) = ([false, true], true) := rfl

theorem the_frame_change_preserves_all_residual_solutions :
    ContextualResidual.Reduction problem (reindex (split chosen) (forward_preserves source chosen))
      (ContextualResidual.mapProblem (reindex (split chosen) (forward_preserves source chosen)) problem) :=
  reduction source chosen problem

def witness : Assignment source source
  | ⟨0, _⟩ => .var (.succ .zero)
  | ⟨1, _⟩ => generator source 1
  | ⟨2, _⟩ => .var .zero
  | ⟨number + 3, impossible⟩ => by omega

theorem the_original_mixed_sort_equation_has_an_actual_solution : ContextualResidual.Models witness problem := by
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem that_solution_transports_to_the_selected_frame :
    ∃ residual : Assignment target source,
      ContextualResidual.Models residual
        (ContextualResidual.mapProblem (reindex (split chosen) (forward_preserves source chosen)) problem) ∧
      ∀ identity, witness identity = instantiate residual
        (reindex (split chosen) (forward_preserves source chosen) identity) :=
  the_frame_change_preserves_all_residual_solutions.complete source witness
    the_original_mixed_sort_equation_has_an_actual_solution

theorem selecting_a_different_sort_cannot_fake_arity_preservation :
    target (.inr ⟨1, by decide⟩) ≠ source chosen := by
  intro same
  have sorts := congrArg Prod.snd same
  cases sorts

theorem the_remaining_frame_has_two_declarations : Fintype.card (Remaining chosen) = 2 := by
  have same := remaining_cardinality chosen
  simp only [Fintype.card_fin] at same
  omega

abbrev repeatedFields : List (MetaArity base) := [([], false), ([], false)]
def firstField : ArgumentSlots.Slot repeatedFields := ⟨([], false), .zero⟩
def secondField : ArgumentSlots.Slot repeatedFields := ⟨([], false), .succ .zero⟩

theorem repeated_field_declarations_keep_distinct_indices :
    ArgumentSlots.toIndex firstField = 0 ∧ ArgumentSlots.toIndex secondField = 1 := ⟨rfl, rfl⟩

theorem repeated_fields_are_not_identified : firstField ≠ secondField := by
  intro same
  have impossible := congrArg ArgumentSlots.toIndex same
  cases impossible

theorem repeated_field_enumeration_has_two_members : Fintype.card (ArgumentSlots.Slot repeatedFields) = 2 :=
  ArgumentSlots.cardinality repeatedFields

def repeatedArguments : Args before [([], false), ([], false)] [false] :=
  .cons (.var .zero) (.cons (.var .zero) .nil)

def repeatedMap : Ren before [false, false] [false] := fun _ position => match position with
  | .zero => .zero
  | .succ .zero => .zero
  | .succ (.succ impossible) => nomatch impossible

theorem variable_spine_recovery_accepts_repeated_arguments :
    VariableSpines.recognize (S := before) [false, false] repeatedArguments = some repeatedMap := by
  apply VariableSpines.complete (S := before)
  intro sort position
  cases position with
  | zero => rfl
  | succ previous =>
      cases previous with
      | zero => rfl
      | succ impossible => cases impossible

def swappedArguments : Args before [([], true), ([], false)] [false, true] :=
  .cons (.var (.succ .zero)) (.cons (.var .zero) .nil)

def swappedMap : Ren before [true, false] [false, true] := fun _ position => match position with
  | .zero => .succ .zero
  | .succ .zero => .zero
  | .succ (.succ impossible) => nomatch impossible

theorem variable_spine_recovery_accepts_reordered_mixed_sorts :
    VariableSpines.recognize (S := before) [true, false] swappedArguments = some swappedMap := by
  apply VariableSpines.complete (S := before)
  intro sort position
  cases position with
  | zero => rfl
  | succ previous =>
      cases previous with
      | zero => rfl
      | succ impossible => cases impossible

def compoundArguments : Args before [([], false)] [] :=
  .cons (.op (.inl (.constant false)) .nil) .nil

theorem a_compound_argument_is_outside_this_spine_recognizer :
    VariableSpines.recognize (S := before) [false] compoundArguments = none := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSelection.Controls
