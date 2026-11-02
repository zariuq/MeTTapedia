import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnifierProfiles
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingControls

/-!
# Function synthesis and a forbidden outer capture

Imitation, rigid normalization and contextual binding compose to synthesize
the closed identity lambda. Its helper may use the lambda's own binder, but
cannot acquire an undeclared ambient parameter. The unrelated declarations
remain in the answer interface throughout.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitation.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualBinding.Controls (base)

instance : DecidableEq base.Srt := by change DecidableEq Unit; infer_instance
instance : ∀ sort, DecidableEq (base.Op sort) := fun _ => by
  change DecidableEq ContextualFrame.Controls.Operator
  infer_instance

def others (_ : Nat) : MetaArity base := ([], ())
abbrev source := sourceDeclarations [] () others
abbrev target := targetDeclarations (S := base) [] (result := ()) ContextualFrame.Controls.Operator.lam others
abbrev lambdaSlot := ArgumentSlots.Slot (base.arity (s := ()) ContextualFrame.Controls.Operator.lam)

def slot : lambdaSlot := ⟨([()], ()), .zero⟩

private theorem slot_unique : ∀ position : lambdaSlot, position = slot
  | ⟨_, .zero⟩ => rfl
  | ⟨_, .succ impossible⟩ => nomatch impossible

instance : DecidableEq lambdaSlot := fun first second =>
  isTrue ((slot_unique first).trans (slot_unique second).symm)

def helper : lambdaSlot ⊕ Nat := .inl slot
def original : Unit ⊕ Nat := .inl ()

def lambda {V : Type} {declaration : V → MetaArity base} {Γ : Ctx base}
    (body : Term (signature base declaration) (() :: Γ) ()) : Term (signature base declaration) Γ () :=
  .op (.inl .lam) (.cons body .nil)

def problem : Problem source :=
  [(observe (generator source original), observe (lambda (Γ := []) (.var .zero)))]

def first : Assignment source target := answer [] ContextualFrame.Controls.Operator.lam others

theorem imitation_is_a_complete_residual_transformation :
    Reduction problem first (mapProblem first problem) :=
  reduction [] ContextualFrame.Controls.Operator.lam others (fun _ position => nomatch position)
    (.cons (.var .zero) .nil) problem (by
      with_unfolding_all exact List.mem_singleton_self _)

def child : Problem target := [(observe (generator target helper), observe (Term.var (S := signature base target) (Γ := [()]) .zero))]

theorem the_helper_scope_contains_the_lambda_binder : (target helper).1 = [()] := rfl

theorem normalization_produces_the_actual_open_child :
    ContextualRigidSolver.normalize (mapProblem first problem) = some child := by with_unfolding_all rfl

def second : Assignment target target := ContextualBinding.answer helper (.var .zero)

theorem binding_solves_the_child : Reduction child second [] := by
  exact of_principal_prefix
    (ContextualUnifierProfiles.binding (S := base) helper (Term.var (S := signature base target) .zero)
      (by simp [support])) []

def combined : Assignment source target := Assignment.compose second first

theorem all_three_reductions_compose : Reduction problem combined [] := by
  have decomposed := imitation_is_a_complete_residual_transformation.compose
    (ContextualRigidSolver.normalization_reduction normalization_produces_the_actual_open_child)
  have finished := decomposed.compose binding_solves_the_child
  simpa only [Assignment.compose_identity_left, combined] using finished

theorem synthesis_returns_the_closed_identity_lambda :
    combined original = lambda (.var .zero) := by with_unfolding_all rfl

theorem the_synthesized_answer_solves_the_original_problem : Models combined problem :=
  all_three_reductions_compose.finished_sound

theorem every_original_solution_factors_through_the_synthesized_answer
    {Variables : Type} (next : Variables → MetaArity base) (candidate : Assignment source next)
    (solved : Models candidate problem) :
    ∃ residual : Assignment target next,
      ∀ identity, candidate identity = instantiate residual (combined identity) := by
  obtain ⟨residual, _, factors⟩ := all_three_reductions_compose.complete next candidate solved
  exact ⟨residual, factors⟩

theorem unrelated_declarations_are_preserved (identity : Nat) :
    combined (.inr identity) = generator target (.inr identity) := by
  simp only [combined, Assignment.compose, first, answer, second, instantiate_generator]
  simp [ContextualBinding.answer, helper]

def emptyMap : Ren base [] [()] := fun _ position => nomatch position

def forbidden : Problem source :=
  [(observe (rename (S := signature base source) emptyMap (generator source original)),
    observe (lambda (Γ := [()]) (.var (.succ .zero))))]

def localOnly : Ren base [()] [(), ()] := fun _ position => match position with
  | .zero => .zero
  | .succ impossible => nomatch impossible

def forbiddenChild : Problem target :=
  [(observe (rename (S := signature base target) localOnly (generator target helper)),
    observe (Term.var (S := signature base target) (Γ := [(), ()]) (.succ .zero)))]

theorem forbidden_outer_dependence_is_retained_as_an_equation :
    ContextualRigidSolver.normalize (mapProblem first forbidden) = some forbiddenChild := by
  with_unfolding_all rfl

private theorem local_only_cannot_reach_outer {Variables : Type} (next : Variables → MetaArity base)
    (image : Term (signature base next) [()] ()) :
    rename (S := signature base next) localOnly image ≠ Term.var (.succ .zero) := by
  cases image with
  | var position =>
      cases position with
      | zero => intro same; cases same
      | succ impossible => cases impossible
  | op _ _ => intro same; cases same

theorem the_forbidden_child_has_no_solution_in_any_later_frame
    {Variables : Type} (next : Variables → MetaArity base) (candidate : Assignment target next) :
    ¬ Models candidate forbiddenChild := by
  intro solved
  have same := observe_injective (solved _ (List.mem_singleton_self _))
  have renamed := ContextualFamily.instantiate_rename (S := base) candidate localOnly (generator target helper)
  have generated := instantiate_generator (S := base) candidate helper
  have image := congrArg (fun term : Term (signature base next) [()] () =>
    rename (S := signature base next) localOnly term) generated
  exact local_only_cannot_reach_outer next (candidate helper) (image.symm.trans (renamed.symm.trans same))

theorem the_original_forbidden_capture_has_no_solution
    {Variables : Type} (next : Variables → MetaArity base) (candidate : Assignment source next) :
    ¬ Models candidate forbidden := by
  intro solved
  have imitate := reduction [] ContextualFrame.Controls.Operator.lam others emptyMap
    (.cons (Term.var (S := signature base source) (.succ .zero)) .nil) forbidden (by
      with_unfolding_all exact List.mem_singleton_self _)
  have keep := imitate.compose
    (ContextualRigidSolver.normalization_reduction forbidden_outer_dependence_is_retained_as_an_equation)
  obtain ⟨residual, childSolved, _⟩ := keep.complete next candidate solved
  exact the_forbidden_child_has_no_solution_in_any_later_frame next residual childSolved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitation.Controls
