import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualVariableBinding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRenamingInverseControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSolver

/-!
# Variable binding accepts ambient ports and rejects undeclared capture

A mixed-sort swapped spine is solved and its reflexive residual is removed
by the common rigid normalizer. Another variable of the same sort outside
the declared image has no solution. With a repeated spine, two formal
projections solve the equation but cannot both factor through a single
chosen projection; the completeness theorem must retain its injectivity
hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualVariableBinding.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualFrameSelection.Controls (base swappedMap repeatedMap)

instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Bool)
instance : ∀ sort, DecidableEq (base.Op sort) := by
  intro sort first second
  cases first <;> cases second
  · exact isTrue rfl
  · exact isFalse (by intro same; cases same)
  · exact isFalse (by intro same; cases same)
  · exact isTrue rfl

def others (_ : Nat) : MetaArity base := ([false], false)
abbrev source := declarations (S := base) [true, false] false others

def left : Term (signature base source) [false, true] false :=
  rename swappedMap (generator source (.inl ()))
def right : Term (signature base source) [false, true] false := .var .zero
def problem : ContextualResidual.Problem source := [(observe left, observe right)]

def selectedAnswer : Assignment source others := answer [true, false] others (.succ .zero)

theorem the_swapped_ambient_variable_is_accepted :
    solve? [true, false] others swappedMap (result := false) .zero = some selectedAnswer := rfl

theorem variable_binding_is_complete_and_retains_the_queue :
    ContextualResidual.Reduction problem selectedAnswer (ContextualResidual.mapProblem selectedAnswer problem) :=
  reduction [true, false] others swappedMap ContextualRenamingInverse.Controls.swapped_injective
    .zero (.succ .zero) rfl problem (List.mem_singleton_self _)

theorem normalization_removes_the_solved_equation :
    ContextualRigidSolver.normalize (ContextualResidual.mapProblem selectedAnswer problem) = some [] := by cbv

theorem both_executable_reductions_solve_the_original_problem :
    ContextualResidual.Reduction problem selectedAnswer [] := by
  have combined := variable_binding_is_complete_and_retains_the_queue.compose
    (ContextualRigidSolver.normalization_reduction normalization_removes_the_solved_equation)
  simpa only [Assignment.compose_identity_left] using combined

theorem the_answer_actually_solves_the_input : ContextualResidual.Models selectedAnswer problem :=
  both_executable_reductions_solve_the_original_problem.finished_sound

theorem an_unselected_active_image_is_retained :
    targetPotential others (remainingAssignment [true, false] false others selectedAnswer) {9} + 1 =
      sourcePotential [true, false] false others selectedAnswer {9} :=
  removes_one_model_node [true, false] others (.succ .zero) selectedAnswer rfl {9}

def outsideMap : Ren base [false] [false, false] := fun _ position => match position with
  | .zero => .succ .zero
  | .succ impossible => nomatch impossible

theorem outsideMap_injective : ∀ sort, Function.Injective (outsideMap sort) := by
  intro sort first second _
  cases first with
  | zero =>
      cases second with
      | zero => rfl
      | succ impossible => cases impossible
  | succ impossible => cases impossible

theorem undeclared_ambient_capture_is_refused :
    solve? [false] others outsideMap (result := false) .zero = none := rfl

theorem the_refused_capture_has_no_later_contextual_solution
    {Variables : Type} (next : Variables → MetaArity base)
    (candidate : Assignment (declarations [false] false others) next) :
    rename (S := signature base next) outsideMap (candidate (.inl ())) ≠ .var .zero :=
  refused_has_no_solution [false] others outsideMap outsideMap_injective .zero rfl candidate

abbrev repeatedSource := declarations (S := base) [false, false] false others
def firstProjection : Assignment repeatedSource others := answer [false, false] others .zero
def secondProjection : Assignment repeatedSource others := answer [false, false] others (.succ .zero)

theorem both_repeated_spine_images_solve_the_same_equation :
    rename (S := signature base others) repeatedMap (firstProjection (.inl ())) = .var .zero ∧
      rename (S := signature base others) repeatedMap (secondProjection (.inl ())) = .var .zero := ⟨rfl, rfl⟩

theorem a_chosen_projection_is_not_complete_for_a_repeated_spine :
    ¬ ∃ remaining : Assignment others others,
      ∀ identity, secondProjection identity = instantiate remaining (firstProjection identity) := by
  rintro ⟨remaining, components⟩
  have impossible := components (.inl ())
  change (Term.var (S := signature base others) (Γ := [false, false]) (.succ .zero)) = .var .zero at impossible
  cases impossible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualVariableBinding.Controls
