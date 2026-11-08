import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaExecution

/-!
# Two retained lambda transitions at different binder depths

The first redex is beneath two binders and the next beneath one. Both use
the same local declaration family. The second input is the first actual
endpoint, including its equation, shared output, retained roots and scope
ledger. No source reconstruction occurs between the two transitions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaExecution.Controls

open Mettapedia.OSLF.Binding
open LambdaContextualRung (sig Srt Context appT lamT)

def identity {Γ : Ctx sig} : Term sig Γ .term := lamT (.var .zero)
def program : Term sig [] .term :=
  lamT (appT (lamT (appT identity (.var .zero))) (.var .zero))
def middle : Term sig [] .term := lamT (appT identity (.var .zero))
def finalValue : Term sig [] .term := identity

def innerContext : Context [] [.term, .term] :=
  .underLam (.appLeft (.underLam .hole) (.var .zero))
def outerContext : Context [] [.term] := .underLam .hole
def innerBody : Term sig [.term, .term, .term] .term := .var .zero
def innerArgument : Term sig [.term, .term] .term := .var .zero
def outerBody : Term sig [.term, .term] .term := .var .zero
def outerArgument : Term sig [.term] .term := .var .zero

theorem first_source_step : LambdaContextualRung.Step [] program middle :=
  innerContext.congr_step (.beta innerBody innerArgument)

theorem second_source_step : LambdaContextualRung.Step [] middle finalValue :=
  outerContext.congr_step (.beta outerBody outerArgument)

theorem firstAdmission : ContextualGuardedStep.Valid locals (initial program).1.declarations
    (initial program).1.occupied (selection (initial program).2)
    (rule (initial program).1.declarations innerContext) (initial program).1.inventory.rows
    (initial program).1.inventory.configuration
    (fun _ => output (initial program).1.declarations (initial program).1.occupied (initial program).2 innerContext) :=
  valid_of_source (initial program) innerContext innerBody innerArgument (initial_represents program)
def firstState : State [] := destination (initial program) innerContext firstAdmission

theorem first_represents : Represents firstState middle :=
  destination_represents (initial program) innerContext innerBody innerArgument (initial_represents program) firstAdmission

theorem secondAdmission : ContextualGuardedStep.Valid locals firstState.1.declarations
    firstState.1.occupied (selection firstState.2) (rule firstState.1.declarations outerContext)
    firstState.1.inventory.rows firstState.1.inventory.configuration
    (fun _ => output firstState.1.declarations firstState.1.occupied firstState.2 outerContext) :=
  valid_of_source firstState outerContext outerBody outerArgument first_represents
def secondState : State [] := destination firstState outerContext secondAdmission

theorem first_transition : Transition (initial program) firstState :=
  ⟨_, innerContext, firstAdmission, rfl⟩

theorem second_transition : Transition firstState secondState :=
  ⟨_, outerContext, secondAdmission, rfl⟩

theorem final_value_is_the_actual_retained_endpoint : Represents secondState finalValue :=
  destination_represents firstState outerContext outerBody outerArgument first_represents secondAdmission

theorem composed_path_uses_the_first_endpoint :
    Relation.ReflTransGen Transition (initial program) secondState :=
  (Relation.ReflTransGen.single first_transition).tail second_transition

theorem both_source_steps_are_recovered :
    Relation.ReflTransGen (LambdaContextualRung.Step []) program finalValue :=
  (finite_execution_iff program finalValue).mpr
    ⟨secondState, composed_path_uses_the_first_endpoint, final_value_is_the_actual_retained_endpoint⟩

theorem first_equation_is_retained : firstState.1.inventory.configuration.equations.length = 1 :=
  (equation_count_increases first_transition program (initial_represents program)).1

theorem two_equations_remain_after_the_second_step : secondState.1.inventory.configuration.equations.length = 2 := by
  have count := (equation_count_increases second_transition middle first_represents).1
  rw [first_equation_is_retained] at count
  exact count

theorem second_state_is_not_a_reset_equation_store :
    secondState.1.inventory.configuration.equations.length ≠
      (initial finalValue).1.inventory.configuration.equations.length := by
  rw [two_equations_remain_after_the_second_step]
  decide

theorem occurrence_identity_advances_twice : secondState.2 = 2 := rfl

theorem source_variable_has_no_selected_transition {Γ : Ctx sig} (position : Var Γ .term) :
    ¬ ∃ after, Transition (initial (.var position)) after := by
  rintro ⟨after, transition⟩
  obtain ⟨target, step, _⟩ := source_step_reflected transition (.var position) (initial_represents (.var position))
  exact LambdaContextualRung.variable_has_no_step position step

theorem both_retained_steps_have_actual_solver_returns :
    ∃ (firstFuel : Nat) (firstCache : Cache firstState) (firstComplete : firstCache.remaining = []),
      solveCached (initial program) innerContext (initialCache program) rfl firstFuel = .residual firstCache ∧
      ∃ (secondFuel : Nat) (secondCache : Cache secondState),
        solveCached firstState outerContext firstCache firstComplete secondFuel = .residual secondCache ∧
        secondCache.remaining = [] := by
  obtain ⟨firstFuel, firstCache, firstComputed, firstComplete⟩ :=
    solveCached_completes_valid (initial program) innerContext program (initial_represents program)
      (initialCache program) rfl firstAdmission
  obtain ⟨secondFuel, secondCache, secondComputed, secondComplete⟩ :=
    solveCached_completes_valid firstState outerContext middle first_represents firstCache firstComplete secondAdmission
  exact ⟨firstFuel, firstCache, firstComplete, firstComputed, secondFuel, secondCache, secondComputed, secondComplete⟩

theorem the_exact_two_step_endpoint_has_a_solver_history :
    ∃ cache : Cache secondState, SolverPath program secondState cache := by
  obtain ⟨firstFuel, firstCache, firstComplete, firstComputed,
    secondFuel, secondCache, secondComputed, secondComplete⟩ := both_retained_steps_have_actual_solver_returns
  have first : SolverPath program firstState firstCache :=
    .step .initial rfl innerContext firstAdmission firstFuel firstCache firstComputed firstComplete
  exact ⟨secondCache, .step first firstComplete outerContext secondAdmission secondFuel secondCache secondComputed secondComplete⟩

theorem source_variable_is_refuted_by_the_actual_solver {Γ : Ctx sig} (position : Var Γ .term) :
    ∃ fuel proof, solveCached (initial (.var position)) (.hole : Context Γ Γ)
      (initialCache (.var position)) rfl fuel = .refuted proof :=
  solveCached_refutes_inert_source (initial (.var position)) .hole (.var position)
    (initial_represents (.var position)) (initialCache (.var position)) rfl
    (fun _ => LambdaContextualRung.variable_has_no_step position)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LambdaExecution.Controls
