import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnrefutedPatternAvailability
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternControls

/-!
# Model-free dispatch on cyclic and scope-invalid pattern queues

The two-equation cycle has no higher-order model, but no individual equation
is an immediate scope or occurs refutation. The actual selector still has a
choice. A missing ambient variable is instead detected by the scope refuter.
The legal repeated/compound residual remains outside the pattern premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnrefutedPatternControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment

abbrev base := ContextualFrame.Controls.signature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def source (_ : Bool) : MetaArity base := ([()], ())
abbrev extended := signature base source

def call (identity : Bool) {Γ : Ctx base} (argument : Term extended Γ ()) : Term extended Γ () :=
  .op (.inr (.mk identity)) (.cons argument .nil)
def constant {Γ : Ctx base} : Term extended Γ () := .op (.inl .constant) .nil
def pair {Γ : Ctx base} (left right : Term extended Γ ()) : Term extended Γ () :=
  .op (.inl .pair) (.cons left (.cons right .nil))

def cycle : Problem source :=
  [(observe (call false (Term.var (S := extended) (.zero : Var [()] ()))),
    observe (call true (Term.var (S := extended) (.zero : Var [()] ())))),
   (observe (call true (Term.var (S := extended) (.zero : Var [()] ()))),
    observe (pair (call false (Term.var (S := extended) (.zero : Var [()] ()))) constant))]

theorem cycle_is_patterned : ProblemPattern cycle := (checkProblem_iff _).mp (by decide +kernel)

theorem cycle_is_already_normal : ContextualRigidSolver.normalize cycle = some cycle := by
  with_unfolding_all rfl

theorem the_cycle_has_no_immediate_equation_refutation : ContextualEquationRefutation.choose cycle = none := by
  with_unfolding_all rfl

theorem the_actual_cycle_selector_has_a_choice_without_a_model : (ContextualFrameWorklist.choose cycle).isSome = true := by
  have available := ContextualUnrefutedPatternAvailability.nonempty_normal_unrefuted_pattern_choice cycle
    (ContextualRigidNormalForm.normalization_normal cycle cycle_is_already_normal) cycle_is_patterned
    the_cycle_has_no_immediate_equation_refutation (by decide)
  cases computed : ContextualFrameWorklist.choose cycle with
  | none => exact False.elim (available computed)
  | some update => rfl

theorem formal_call_is_generator (identity : Bool) :
    call identity (Term.var (S := extended) (.zero : Var [()] ())) = generator source identity := rfl

theorem the_cycle_has_no_higher_order_model {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment source next) : ¬ Models candidate cycle := by
  intro solved
  have firstObserved := solved _ List.mem_cons_self
  have secondObserved := solved _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  dsimp only at firstObserved secondObserved
  have first := observe_injective (S := base) (source := next) firstObserved
  have second := observe_injective (S := base) (source := next) secondObserved
  simp only [formal_call_is_generator] at first second
  simp only [pair, constant, ContextualFamily.instantiate, ContextualFamily.instantiateArgs] at second
  have sameSizes := congrArg termSize first
  have impossible := congrArg termSize second
  simp only [termSize, argsSize] at impossible
  omega

def missingVariable : Problem source :=
  [(observe (call false (Term.var (S := extended) (.succ .zero : Var [(), ()] ()))),
    observe (Term.var (S := extended) (.zero : Var [(), ()] ())))]

theorem the_missing_variable_is_still_a_structural_pattern : ProblemPattern missingVariable :=
  (checkProblem_iff _).mp (by decide +kernel)

theorem the_actual_scope_refuter_detects_the_missing_variable :
    (ContextualEquationRefutation.choose missingVariable).isSome = true := by
  decide +kernel

theorem unsupported_general_applications_remain_legal_residuals :
    Models ContextualFrameSaturationControls.generalModel ContextualFrameSaturationControls.generalProblem ∧
      ¬ ProblemPattern ContextualFrameSaturationControls.generalProblem ∧
      ContextualFrameWorklist.choose ContextualFrameSaturationControls.generalProblem = none := by
  refine ⟨ContextualFrameSaturationControls.the_repeated_and_compound_equations_have_a_model, ?_, ?_⟩
  · rw [← checkProblem_iff]
    decide +kernel
  · rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnrefutedPatternControls
