import Mettapedia.Languages.LambdaCalculus.NamePassingEnvironmentEquations

/-!
# The pure fragment has no hidden environment equations

Environment scope equations cannot change a term made solely of variables,
abstractions and applications. This gives small inversion lemmas for actual
modulo-equation executions without normalizing the compiler or its runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing

open Mettapedia.OSLF.Binding

variable {Srt : Type} {nm : Srt}

def pure : {Γ : List Srt} → Expr nm Γ → Bool
  | _, .var _ => true
  | _, .lam body => pure body
  | _, .app function _ => pure function
  | _, .defn _ _ => false
  | _, .carrier _ _ _ => false

theorem pure_structural {Γ : List Srt} {left right : Expr nm Γ}
    (equal : Environment.StructuralEq left right) : pure left = pure right := by
  induction equal with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | appDefinition => rfl
  | appCarrier => rfl
  | lam _ ih => exact ih
  | app _ _ ih => exact ih
  | defn => rfl
  | carrier => rfl

theorem eq_of_pure {Γ : List Srt} {left right : Expr nm Γ}
    (equal : Environment.StructuralEq left right) (isPure : pure left = true) : left = right := by
  induction equal with
  | refl => rfl
  | symm equal ih => exact (ih ((pure_structural equal).trans isPure)).symm
  | trans first _ firstIH secondIH =>
      exact (firstIH isPure).trans (secondIH ((pure_structural first).symm.trans isPure))
  | appDefinition => cases isPure
  | appCarrier => cases isPure
  | lam _ ih => exact congrArg Expr.lam (ih isPure)
  | app argument _ ih => exact congrArg (fun function => Expr.app function argument) (ih isPure)
  | defn => cases isPure
  | carrier => cases isPure

theorem variable_no_modulo_step {Γ : List Srt} (name : Var Γ nm)
    {action : Environment.Action} {target : Expr nm Γ} :
    ¬ Environment.StepModulo action (.var name) target := by
  rintro ⟨redex, _, equal, step, _⟩
  have same := eq_of_pure equal rfl
  subst redex
  exact Environment.variable_no_step name step

/-- Applying the identity has exactly its supplied variable as endpoint,
including all allowed static environment equations. -/
theorem identity_modulo_step {Γ : List Srt} (argument : Var Γ nm)
    {action : Environment.Action} {target : Expr nm Γ}
    (step : Environment.StepModulo action (.app (.lam (.var .zero)) argument) target) :
    action = .beta ∧ target = .var argument := by
  obtain ⟨redex, result, equal, actual, after⟩ := step
  have same := eq_of_pure equal rfl
  subst redex
  cases actual with
  | beta => exact ⟨rfl, (eq_of_pure after rfl).symm⟩
  | app _ inner => exact (Environment.lambda_no_step _ inner).elim

end Mettapedia.Languages.LambdaCalculus.NamePassing
