import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairSelection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDecompositionControls

/-!
# Pair selection keeps open mixed-sort declarations

The family is indexed by all natural numbers, while the selected equation
uses two holes. Reindexing retains unused declarations, their parameter
sorts, and actual future solutions. It cannot identify the two ports or
silently replace their different parameter interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairSelection.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

abbrev base := ContextualDecomposition.Controls.mixedSignature

def source (identity : Nat) : MetaArity base :=
  if identity = 7 then ([false, true], true)
  else if identity = 11 then ([true], true) else ([], false)

abbrev target := declarations source 7 11
abbrev before := signature base source
abbrev after := signature base target

def left : Term before [false, true] true :=
  .op (.inr (.mk 7)) (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))
def right : Term before [false, true] true :=
  .op (.inr (.mk 11)) (.cons (.var (.succ .zero)) .nil)
def problem : ContextualResidual.Problem source := [(observe left, observe right)]

theorem the_first_chosen_name_reaches_its_own_port :
    split 7 11 (by decide) 7 = .inl false := first_to_port _ _ _

theorem the_second_chosen_name_reaches_its_own_port :
    split 7 11 (by decide) 11 = .inl true := second_to_port _ _ _

theorem the_two_parameter_contexts_remain_different :
    target (.inl false) = ([false, true], true) ∧ target (.inl true) = ([true], true) := ⟨rfl, rfl⟩

theorem every_other_name_is_retained (identity : Nat) (left : identity ≠ 7) (right : identity ≠ 11) :
    (split 7 11 (by decide)).symm (.inr ⟨identity, left, right⟩) = identity := rfl

theorem retaining_a_distant_declaration_does_not_require_a_finite_frame :
    target (.inr ⟨1000000, by decide⟩) = ([], false) := rfl

def witness : Assignment source source := fun identity =>
  if first : identity = 7 then by subst identity; exact .var (.succ .zero)
  else if second : identity = 11 then by subst identity; exact .var .zero
  else generator source identity

theorem the_original_equation_has_a_mixed_sort_solution : ContextualResidual.Models witness problem := by
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem selection_transports_that_solution_and_every_old_image :
    ∃ residual : Assignment target source,
      ContextualResidual.Models residual
        (ContextualResidual.mapProblem
          (reindex (split 7 11 (by decide)) (forward_preserves source 7 11 (by decide))) problem) ∧
      ∀ identity, witness identity = instantiate residual
        (reindex (split 7 11 (by decide)) (forward_preserves source 7 11 (by decide)) identity) :=
  (reduction source 7 11 (by decide) problem).complete source witness
    the_original_equation_has_a_mixed_sort_solution

theorem selected_ports_cannot_be_merged :
    split 7 11 (by decide) 7 ≠ split 7 11 (by decide) 11 := ports_are_distinct _ _ _

theorem a_changed_sort_is_not_the_same_interface : target (.inr ⟨0, by decide⟩) ≠ target (.inl false) := by
  intro same
  have incompatible := congrArg Prod.snd same
  cases incompatible

theorem using_the_same_name_twice_does_not_meet_pair_selection : ¬ ((7 : Nat) ≠ 7) := by simp

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairSelection.Controls
