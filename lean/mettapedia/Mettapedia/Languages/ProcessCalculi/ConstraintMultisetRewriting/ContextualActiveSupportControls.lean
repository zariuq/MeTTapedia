import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveSupport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameControls

/-!
# An infinite declaration family has a finite computed binding roster

The repeated dependency is counted once as an identity. Replacing the
selected hole updates the actual remaining equations, preserves the model,
and drops its finite model potential from five nodes to two. A declaration
outside the roster is still detected by the ordinary support checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveSupportControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport

abbrev base := ContextualFrame.Controls.signature
def declaration (_ : Nat) : MetaArity base := ([], ())
abbrev extended := signature base declaration

def hole (identity : Nat) : Term extended [] () := generator declaration identity
def constant : Term extended [] () := .op (.inl .constant) .nil
def pair (left right : Term extended [] ()) : Term extended [] () :=
  .op (.inl .pair) (.cons left (.cons right .nil))
def body : Term extended [] () := pair (hole 1000003) (hole 1000003)
def remaining : Problem declaration :=
  [(observe (hole 1000003), observe constant), (observe (hole 987654321), observe constant)]
def problem : Problem declaration := (observe (hole 0), observe body) :: remaining
def image : Assignment declaration declaration := fun identity =>
  if identity = 0 then pair constant constant else constant
def bound : Assignment declaration declaration := ContextualBinding.answer 0 body

theorem the_computed_roster_has_three_distinct_names : active problem = {0, 1000003, 987654321} := by
  decide +kernel

theorem the_bound_name_disappears_from_the_actual_remaining_queue :
    active (mapProblem bound remaining) = {1000003, 987654321} := by
  decide +kernel

theorem the_repeated_dependency_does_not_duplicate_the_roster_cost : potential image (active problem) = 5 := by
  decide +kernel

theorem the_remaining_roster_cost_is_two : potential image (active (mapProblem bound remaining)) = 2 := by
  decide +kernel

theorem an_unlisted_dependency_is_detected : checkSupport [0, 1000003] (hole 987654321) = false := by
  decide +kernel

theorem the_original_equations_have_an_actual_model : Models image problem := by
  intro equation member
  simp only [problem, remaining, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem the_actual_binding_keeps_a_model_and_strictly_decreases_its_potential :
    ∃ residual : Assignment declaration declaration,
      Models residual (mapProblem bound remaining) ∧
      (∀ identity, image identity = instantiate residual (bound identity)) ∧
      potential residual (active (mapProblem bound remaining)) < potential image (active problem) := by
  exact binding_prefix_progress 0 body remaining (by decide) image the_original_equations_have_an_actual_model

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveSupportControls
