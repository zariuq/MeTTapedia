import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaComparison

/-!
# Lambda transform controls and the demand-policy boundary

Binder crossing, both application contexts and unused arguments use the
uniform comparison. A source variable cannot acquire an execution. Full
beta reduction also admits an infinite reduction of unused work; recovering
this source relation therefore does not establish call-by-need adequacy.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaComparison.Controls

open Mettapedia.OSLF.Binding
open LambdaContextualRung

def identity {Γ : Ctx sig} : Term sig Γ .term := lamT (.var .zero)

def crossingBody : Term sig [.term, .term] .term := lamT (.var (.succ .zero))
def outerVariable : Term sig [.term] .term := .var .zero
def crossingInput : Term sig [.term] .term := appT (lamT crossingBody) outerVariable
def crossingResult : Term sig [.term] .term := lamT (.var (.succ .zero))

theorem crossing_preserves_the_enclosing_variable : Executes crossingInput crossingResult := by
  apply (source_step_iff_executes _ _).mp
  exact LambdaContextualRung.Step.beta crossingBody outerVariable

theorem lambda_body_context_executes :
    Executes (lamT crossingInput) (lamT crossingResult) := by
  apply (source_step_iff_executes _ _).mp
  exact LambdaContextualRung.Step.lamCong (LambdaContextualRung.Step.beta crossingBody outerVariable)

theorem left_application_context_executes :
    Executes (appT crossingInput outerVariable) (appT crossingResult outerVariable) := by
  apply (source_step_iff_executes _ _).mp
  exact LambdaContextualRung.Step.appCongL outerVariable (LambdaContextualRung.Step.beta crossingBody outerVariable)

theorem right_application_context_executes :
    Executes (appT outerVariable crossingInput) (appT outerVariable crossingResult) := by
  apply (source_step_iff_executes _ _).mp
  exact LambdaContextualRung.Step.appCongR outerVariable (LambdaContextualRung.Step.beta crossingBody outerVariable)

theorem variable_cannot_invent_an_execution {Γ : Ctx sig} (position : Var Γ .term)
    (output : Term sig Γ .term) : ¬ Executes (.var position) output :=
  fun executed => variable_has_no_step position ((source_step_iff_executes _ _).mpr executed)

theorem captured_result_is_not_the_inner_identity : crossingResult ≠ (identity : Term sig [.term] .term) := by
  intro same
  have bodies := (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1
  cases Term.var.inj bodies

theorem captured_replacement_refused : ¬ Executes crossingInput (identity : Term sig [.term] .term) := by
  intro executed
  have step := (source_step_iff_executes _ _).mpr executed
  cases step

def selfApplication : Term sig [] .term := lamT (appT (.var .zero) (.var .zero))
def omega : Term sig [] .term := appT selfApplication selfApplication
def unusedDivergence : Term sig [] .term := appT (lamT identity) omega

theorem unused_divergence_can_be_skipped : Executes unusedDivergence identity := by
  apply (source_step_iff_executes _ _).mp
  exact LambdaContextualRung.Step.beta identity omega

theorem omega_reduces_to_itself : LambdaContextualRung.Step [] omega omega :=
  LambdaContextualRung.Step.beta (appT (.var .zero) (.var .zero)) selfApplication

/-- The same source also allows repeatedly reducing its unused argument.
A demanded evaluation policy must exclude this path; transform's ability to
represent full reduction does not choose that policy automatically. -/
theorem unrestricted_contexts_can_repeat_unused_work : Executes unusedDivergence unusedDivergence := by
  apply (source_step_iff_executes _ _).mp
  exact LambdaContextualRung.Step.appCongR (lamT identity) omega_reduces_to_itself

theorem the_two_results_are_distinct : (identity : Term sig [] .term) ≠ unusedDivergence := by
  intro same
  cases (Term.op.inj same).1

theorem arbitrary_reduction_does_not_force_the_demanded_result :
    ¬ ∀ output, Executes unusedDivergence output → output = (identity : Term sig [] .term) := by
  intro assumed
  exact the_two_results_are_distinct (assumed _ unrestricted_contexts_can_repeat_unused_work).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaComparison.Controls
