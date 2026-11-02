import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.QuotedLambdaRetained

/-!
# Retained quotation and activation controls

A lambda body constructs code capturing the caller's variable beneath an
inner lambda. The first actual transform leaves that code quoted; the second
activates it in the retained state. Both equations and both solver returns
are retained, and the final variable still refers to the caller.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.QuotedLambdaRetained.Controls

open Mettapedia.OSLF.Binding
open QuotedLambda (sig Context Redex app lam quote activate)
open LambdaContextualRung (Srt)

def program : Term sig [.term] .term := QuotedLambda.Controls.capturedProgram
def finalValue : Term sig [.term] .term := QuotedLambda.Controls.capturedResult
def middle : Term sig [.term] .term := activate (quote finalValue)
def firstContext : Context [.term] [.term] := .underActivate .hole
def firstRedex : Redex [.term] := .beta (quote (lam (.var (.succ .zero)))) (.var .zero)
def secondContext : Context [.term] [.term] := .hole
def secondRedex : Redex [.term] := .activation finalValue

theorem first_source_step : QuotedLambda.Step [.term] program middle := firstContext.congr_step firstRedex.step
theorem second_source_step : QuotedLambda.Step [.term] middle finalValue := secondContext.congr_step secondRedex.step

theorem firstAdmission : ContextualGuardedStep.Valid locals (initial program).1.declarations
    (initial program).1.occupied (selection (initial program).2)
    (rule (initial program).1.declarations .beta firstContext) (initial program).1.inventory.rows
    (initial program).1.inventory.configuration
    (fun _ => output (initial program).1.declarations (initial program).1.occupied (initial program).2 .beta firstContext) :=
  valid_of_source (initial program) firstContext firstRedex (initial_represents program)
def firstState : State [.term] := destination (initial program) .beta firstContext firstAdmission

theorem first_represents : Represents firstState middle :=
  destination_represents (initial program) firstContext firstRedex (initial_represents program) firstAdmission

theorem secondAdmission : ContextualGuardedStep.Valid locals firstState.1.declarations
    firstState.1.occupied (selection firstState.2) (rule firstState.1.declarations .activation secondContext)
    firstState.1.inventory.rows firstState.1.inventory.configuration
    (fun _ => output firstState.1.declarations firstState.1.occupied firstState.2 .activation secondContext) :=
  valid_of_source firstState secondContext secondRedex first_represents
def secondState : State [.term] := destination firstState .activation secondContext secondAdmission

theorem first_transition : Transition (initial program) firstState := ⟨.beta, _, firstContext, firstAdmission, rfl⟩
theorem second_transition : Transition firstState secondState := ⟨.activation, _, secondContext, secondAdmission, rfl⟩

theorem actual_endpoint_preserves_the_lexical_capture : Represents secondState finalValue :=
  destination_represents firstState secondContext secondRedex first_represents secondAdmission

theorem the_caller_was_not_replaced_by_the_inner_binder :
    ¬ Represents secondState (lam (.var .zero)) := by
  intro wrong
  exact QuotedLambda.Controls.the_result_did_not_capture_the_inner_binder
    (represents_unique actual_endpoint_preserves_the_lexical_capture wrong)

theorem actual_composition_uses_the_first_endpoint :
    Relation.ReflTransGen Transition (initial program) secondState :=
  (Relation.ReflTransGen.single first_transition).tail second_transition

theorem first_equation_remains : firstState.1.inventory.configuration.equations.length = 1 :=
  (equation_count_increases first_transition program (initial_represents program)).1

theorem activation_keeps_both_equations : secondState.1.inventory.configuration.equations.length = 2 := by
  have count := (equation_count_increases second_transition middle first_represents).1
  rw [first_equation_remains] at count
  exact count

theorem activation_did_not_reset_the_world :
    secondState.1.inventory.configuration.equations.length ≠
      (initial finalValue).1.inventory.configuration.equations.length := by
  rw [activation_keeps_both_equations]
  decide

theorem beta_and_activation_have_actual_solver_returns :
    ∃ (firstFuel : Nat) (firstCache : Cache firstState) (firstComplete : firstCache.remaining = []),
      solveCached (initial program) .beta firstContext (initialCache program) rfl firstFuel = .residual firstCache ∧
      ∃ (secondFuel : Nat) (secondCache : Cache secondState),
        solveCached firstState .activation secondContext firstCache firstComplete secondFuel = .residual secondCache ∧
        secondCache.remaining = [] := by
  obtain ⟨firstFuel, firstCache, firstComputed, firstComplete⟩ :=
    solveCached_completes_valid (initial program) .beta firstContext program (initial_represents program)
      (initialCache program) rfl firstAdmission
  obtain ⟨secondFuel, secondCache, secondComputed, secondComplete⟩ :=
    solveCached_completes_valid firstState .activation secondContext middle first_represents
      firstCache firstComplete secondAdmission
  exact ⟨firstFuel, firstCache, firstComplete, firstComputed, secondFuel, secondCache, secondComputed, secondComplete⟩

theorem exact_captured_endpoint_has_a_solver_history :
    ∃ cache : Cache secondState, SolverPath program secondState cache := by
  obtain ⟨firstFuel, firstCache, firstComplete, firstComputed,
    secondFuel, secondCache, secondComputed, secondComplete⟩ := beta_and_activation_have_actual_solver_returns
  have first : SolverPath program firstState firstCache :=
    .step .initial rfl .beta firstContext firstAdmission firstFuel firstCache firstComputed firstComplete
  exact ⟨secondCache, .step first firstComplete .activation secondContext secondAdmission
    secondFuel secondCache secondComputed secondComplete⟩

theorem quoted_loop_has_no_selected_transition :
    ¬ ∃ after, Transition (initial (quote QuotedLambda.Controls.looping)) after := by
  rintro ⟨after, transition⟩
  obtain ⟨target, step, _⟩ := source_step_reflected transition _ (initial_represents _)
  exact QuotedLambda.quote_is_inert _ target step

theorem actual_solver_refutes_a_rule_on_held_code {Γ Δ : Ctx sig}
    (code : Term sig Γ .term) (selected : QuotedLambdaExecution.Kind) (context : Context Γ Δ) :
    ∃ fuel proof, solveCached (initial (quote code)) selected context
      (initialCache (quote code)) rfl fuel = .refuted proof :=
  solveCached_refutes_inert_source (initial (quote code)) selected context (quote code)
    (initial_represents _) (initialCache _) rfl (QuotedLambda.quote_is_inert code)

def bindCapture : Sub sig [.term] [.term] := fun _ _ => lam (.var .zero)

/-- Lexical quotation is not the substitution-sealed name convention of
the separate paper-faithful rho profile. The distinction is observable even
though neither quotation executes its body. -/
theorem lexical_quotation_is_not_substitution_sealed :
    bind bindCapture (quote (.var .zero)) ≠ (quote (.var .zero) : Term sig [.term] .term) := by
  intro same
  have code := (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1
  cases code

def betaInput : Term sig [.term] .term := app (lam (.var .zero)) (.var .zero)

theorem reduction_does_not_identify_the_quoted_syntax :
    QuotedLambda.Step [.term] betaInput (.var .zero) ∧
      quote betaInput ≠ (quote (.var .zero) : Term sig [.term] .term) := by
  refine ⟨.beta _ _, ?_⟩
  intro same
  have code := (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1
  cases code

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.QuotedLambdaRetained.Controls
