import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameControls

/-!
# Constructor imitation joins the executable fresh-frame worklist

A closed hole cannot immediately recover a constructor containing an
ambient argument to another hole. Imitation introduces actual field helpers;
later bindings eliminate that dependence. Binding fields give their helper
its own local variables without adding the caller's ambient variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameImitationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualFrameWorklist

abbrev base := ContextualFrame.Controls.signature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
def declaration (identity : Bool) : MetaArity base := if identity then ([()], ()) else ([], ())
abbrev extended := signature base declaration

def hole {Γ : Ctx base} : Term extended Γ () := .op (.inr (.mk false)) .nil
def call {Γ : Ctx base} (argument : Term extended Γ ()) : Term extended Γ () :=
  .op (.inr (.mk true)) (.cons argument .nil)
def constant {Γ : Ctx base} : Term extended Γ () := .op (.inl .constant) .nil
def pair {Γ : Ctx base} (left right : Term extended Γ ()) : Term extended Γ () :=
  .op (.inl .pair) (.cons left (.cons right .nil))

def body : Term extended [()] () := pair (call (.var .zero)) constant
def problem : Problem declaration := [(observe (hole (Γ := [()])), observe body)]
def reversed : Problem declaration := [(observe body, observe (hole (Γ := [()])))]
def underBinder : Term extended [()] () :=
  .op (.inl .lam) (.cons (pair (.var .zero) (call (.var (.succ .zero)))) .nil)
def binderProblem : Problem declaration := [(observe (hole (Γ := [()])), observe underBinder)]

def pairModel : Assignment declaration declaration
  | false => pair constant constant
  | true => constant

theorem pairModel_models_problem : Models pairModel problem := by
  apply (models_observed_iff pairModel _ _).mpr
  rfl

theorem pairModel_models_reversed : Models pairModel reversed := by
  apply (models_observed_iff pairModel _ _).mpr
  rfl

def binderModel : Assignment declaration declaration
  | false => .op (.inl .lam) (.cons (pair (.var .zero) constant) .nil)
  | true => constant

theorem binderModel_models_problem : Models binderModel binderProblem := by
  apply (models_observed_iff binderModel _ _).mpr
  rfl

def pendingCount {problem : Problem declaration} : Result problem → Option Nat
  | .refuted _ => none
  | .residual update => some update.remaining.length

def rootOperator {Next : Type} (next : Next → MetaArity base) :
    {Γ : Ctx base} → Term (signature base next) Γ () → Option ContextualFrame.Controls.Operator
  | _, .op (.inl operator) _ => some operator
  | _, _ => none

def originalRoot {problem : Problem declaration} : Result problem → Option ContextualFrame.Controls.Operator
  | .refuted _ => none
  | .residual update => rootOperator update.declaration (update.answer false)

def rootArity {Next : Type} (next : Next → MetaArity base) :
    {Γ : Ctx base} → Term (signature base next) Γ () → Option Nat
  | _, .op (.inr (.mk identity)) _ => some (next identity).1.length
  | _, _ => none

def lambdaFieldArity {Next : Type} (next : Next → MetaArity base) :
    {Γ : Ctx base} → Term (signature base next) Γ () → Option Nat
  | _, .op (.inl .lam) (.cons field .nil) => rootArity next field
  | _, _ => none

def originalFieldArity {problem : Problem declaration} : Result problem → Option Nat
  | .refuted _ => none
  | .residual update => lambdaFieldArity update.declaration (update.answer false)

theorem the_direct_binding_pass_cannot_recover_the_ambient_argument :
    (ContextualBindingWorklist.tryEquation (observe (hole (Γ := [()])), observe body)).isSome = false := by
  decide +kernel

theorem imitation_builds_the_actual_rigid_head :
    originalRoot (run 1 declaration problem) = some .pair := by
  rw [run_eq_local_on_model 1 problem declaration pairModel pairModel_models_problem]
  decide +kernel

theorem the_field_equations_are_retained_after_imitation :
    pendingCount (run 1 declaration problem) = some 1 := by
  rw [run_eq_local_on_model 1 problem declaration pairModel pairModel_models_problem]
  decide +kernel

theorem the_fresh_fields_then_solve_the_original_equation :
    pendingCount (run 4 declaration problem) = some 0 := by
  rw [run_eq_local_on_model 4 problem declaration pairModel pairModel_models_problem]
  decide +kernel

theorem the_reverse_orientation_uses_the_same_solver :
    pendingCount (run 4 declaration reversed) = some 0 := by
  rw [run_eq_local_on_model 4 reversed declaration pairModel pairModel_models_reversed]
  decide +kernel

theorem a_binding_field_helper_retains_its_own_bound_variable :
    originalFieldArity (run 1 declaration binderProblem) = some 1 := by
  rw [run_eq_local_on_model 1 binderProblem declaration binderModel binderModel_models_problem]
  decide +kernel

theorem the_unresolved_overlap_under_the_binder_is_not_dropped :
    pendingCount (run 1 declaration binderProblem) = some 1 := by
  rw [run_eq_local_on_model 1 binderProblem declaration binderModel binderModel_models_problem]
  decide +kernel

theorem completion_produces_an_answer_for_the_actual_original_problem :
    ∃ update, run 4 declaration problem = .residual update ∧ update.remaining = [] ∧
      Models update.answer problem := by
  have count := the_fresh_fields_then_solve_the_original_equation
  generalize computed : run 4 declaration problem = result at count
  cases result with
  | refuted proof => cases count
  | residual update =>
      have empty : update.remaining = [] := by simpa using (Option.some.inj count)
      exact ⟨update, rfl, empty, update.completed empty⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameImitationControls
