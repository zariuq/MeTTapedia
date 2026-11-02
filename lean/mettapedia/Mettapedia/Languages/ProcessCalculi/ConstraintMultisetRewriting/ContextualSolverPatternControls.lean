import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatterns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternCompleteness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameImitationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSaturationControls

/-!
# Executed pattern preservation with retained context and fresh binding fields

Swapped input spines are structural patterns. A middle same-hole choice maps
both retained queue portions. Constructor imitation under a binder retains
its binding-field helper and a structural residual. Repeated and compound
applications remain legal, modelled terms outside this recovery fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment

abbrev base := ContextualFrame.Controls.signature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def residualCheck {V : Type} {source : V → MetaArity base} {problem : Problem source} :
    ContextualFrameWorklist.Result problem → Option Bool
  | .refuted _ => none
  | .residual update => some (checkProblem update.remaining)

def chosenSummary {V : Type} [DecidableEq V] (source : V → MetaArity base) (problem : Problem source) :
    Option (Nat × Bool) :=
  (ContextualFrameWorklist.choose problem).map fun update => (update.remaining.length, checkProblem update.remaining)

theorem swapped_input_spines_are_patterns : ProblemPattern ContextualFrameWorklist.Controls.swapProblem :=
  (checkProblem_iff _).mp (by decide +kernel)

theorem the_actual_swapped_run_keeps_the_fragment :
    residualCheck (ContextualFrameWorklist.run 1 ContextualFrameWorklist.Controls.declaration
      ContextualFrameWorklist.Controls.swapProblem) = some true := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 1 ContextualFrameWorklist.Controls.swapProblem
    ContextualFrameWorklist.Controls.declaration ContextualFrameWorklist.Controls.constantModel
    ContextualFrameWorklist.Controls.constant_models_swap]
  decide +kernel

abbrev source := ContextualFrameWorklist.Controls.declaration
abbrev extended := signature base source
def constant {Γ : Ctx base} : Term extended Γ () := .op (.inl .constant) .nil
def unary {Γ : Ctx base} (argument : Term extended Γ ()) : Term extended Γ () :=
  .op (.inr (.mk true)) (.cons argument .nil)
def pair {Γ : Ctx base} (left right : Term extended Γ ()) : Term extended Γ () :=
  .op (.inl .pair) (.cons left (.cons right .nil))

def before : Problem source :=
  [(observe (pair (unary (Term.var (S := extended) (.zero : Var [()] ()))) constant),
    observe (pair (constant (Γ := [()])) constant))]
def after : Problem source :=
  [(observe (unary (Term.var (S := extended) (.zero : Var [()] ()))), observe (constant (Γ := [()])))]
def framedProblem : Problem source := before ++ ContextualFrameWorklist.Controls.swapProblem ++ after

theorem the_retained_prefix_selected_equation_and_suffix_are_patterns : ProblemPattern framedProblem :=
  (checkProblem_iff _).mp (by decide +kernel)

theorem the_actual_middle_choice_keeps_both_retained_portions_in_the_fragment :
    chosenSummary source framedProblem = some (2, true) := by
  decide +kernel

theorem the_binder_imitation_input_is_structural : ProblemPattern ContextualFrameImitationControls.binderProblem :=
  (checkProblem_iff _).mp (by decide +kernel)

theorem the_actual_fresh_binding_field_and_residual_are_retained :
    residualCheck (ContextualFrameWorklist.run 1 ContextualFrameImitationControls.declaration
      ContextualFrameImitationControls.binderProblem) = some true ∧
      ContextualFrameImitationControls.originalFieldArity
        (ContextualFrameWorklist.run 1 ContextualFrameImitationControls.declaration
          ContextualFrameImitationControls.binderProblem) = some 1 := by
  constructor
  · rw [ContextualFrameWorklist.run_eq_local_on_model 1 ContextualFrameImitationControls.binderProblem
      ContextualFrameImitationControls.declaration ContextualFrameImitationControls.binderModel
      ContextualFrameImitationControls.binderModel_models_problem]
    decide +kernel
  · exact ContextualFrameImitationControls.a_binding_field_helper_retains_its_own_bound_variable

theorem every_returned_binding_field_residual_is_structural (fuel : Nat)
    {update : ContextualFrameUpdate.Update ContextualFrameImitationControls.binderProblem}
    (computed : ContextualFrameWorklist.run fuel ContextualFrameImitationControls.declaration
      ContextualFrameImitationControls.binderProblem = .residual update) : ProblemPattern update.remaining :=
  ContextualSolverPatterns.run_preserves fuel _ _ the_binder_imitation_input_is_structural computed

theorem repeated_and_compound_applications_do_not_acquire_a_false_pattern_proof :
    ¬ ProblemPattern ContextualBindingWorklist.Controls.repeatedProblem ∧
      ¬ ProblemPattern ContextualBindingWorklist.Controls.compoundProblem := by
  constructor <;> rw [← checkProblem_iff] <;> decide +kernel

theorem both_general_applications_remain_modelled_and_executable :
    Models ContextualFrameSaturationControls.generalModel ContextualFrameSaturationControls.generalProblem ∧
      ContextualFrameWorklist.run 1 ContextualFrameSaturationControls.generalSource
        ContextualFrameSaturationControls.generalProblem =
        .residual (ContextualFrameWorklist.identity ContextualFrameSaturationControls.generalProblem) :=
  ⟨ContextualFrameSaturationControls.the_repeated_and_compound_equations_have_a_model,
    ContextualFrameSaturationControls.the_actual_run_retains_both_general_equations⟩

theorem the_infinite_roster_problem_is_structural : ProblemPattern ContextualActiveSupportControls.problem :=
  (checkProblem_iff _).mp (by decide +kernel)

theorem the_infinite_family_has_an_actual_principal_finished_run :
    ∃ (fuel : Nat) (update : ContextualFrameUpdate.Update ContextualActiveSupportControls.problem),
      ContextualFrameWorklist.run fuel ContextualActiveSupportControls.declaration
        ContextualActiveSupportControls.problem = .residual update ∧
        update.remaining = [] ∧ Models update.answer ContextualActiveSupportControls.problem ∧
        ∀ {Later : Type} (later : Later → MetaArity base)
          (other : Assignment ContextualActiveSupportControls.declaration later),
          Models other ContextualActiveSupportControls.problem →
          ∃ factor : Assignment update.declaration later,
            ∀ identity, other identity = instantiate factor (update.answer identity) :=
  ContextualPatternCompleteness.solves_principally_of_model _ _ the_infinite_roster_problem_is_structural
    ContextualActiveSupportControls.image ContextualActiveSupportControls.the_original_equations_have_an_actual_model

def binderModel : Assignment ContextualFrameImitationControls.declaration ContextualFrameImitationControls.declaration
  | false => .op (.inl .lam) (.cons
      (ContextualFrameImitationControls.pair (Term.var .zero) ContextualFrameImitationControls.constant) .nil)
  | true => ContextualFrameImitationControls.constant

theorem the_binding_field_problem_has_an_independent_model :
    Models binderModel ContextualFrameImitationControls.binderProblem := by
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem the_binding_field_problem_finishes_in_the_actual_driver :
    ContextualFrameImitationControls.pendingCount
      (ContextualFrameWorklist.run 8 ContextualFrameImitationControls.declaration
        ContextualFrameImitationControls.binderProblem) = some 0 := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 8 ContextualFrameImitationControls.binderProblem
    ContextualFrameImitationControls.declaration binderModel the_binding_field_problem_has_an_independent_model]
  decide +kernel

theorem the_actual_binding_field_answer_factors_every_later_model :
    ∃ (fuel : Nat) (update : ContextualFrameUpdate.Update ContextualFrameImitationControls.binderProblem),
      ContextualFrameWorklist.run fuel ContextualFrameImitationControls.declaration
        ContextualFrameImitationControls.binderProblem = .residual update ∧
        update.remaining = [] ∧ Models update.answer ContextualFrameImitationControls.binderProblem ∧
        ∀ {Later : Type} (later : Later → MetaArity base)
          (other : Assignment ContextualFrameImitationControls.declaration later),
          Models other ContextualFrameImitationControls.binderProblem →
          ∃ factor : Assignment update.declaration later,
            ∀ identity, other identity = instantiate factor (update.answer identity) :=
  ContextualPatternCompleteness.solves_principally_of_model _ _ the_binder_imitation_input_is_structural
    binderModel the_binding_field_problem_has_an_independent_model

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternControls
