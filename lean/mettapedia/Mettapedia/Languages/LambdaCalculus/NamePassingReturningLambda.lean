import Mettapedia.Languages.LambdaCalculus.NamePassingActiveForm

/-!
# Calling a lambda under nonrecursive environments

A returning lambda can have definitions and one-shot declarations enclosing
it, but no intervening application. Calling it crosses those declarations
using the independently authored application equations and then performs one
ordinary source beta event. Its result retains every enclosing declaration
and the correct shifted argument beneath each definition binder.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.Environment

open Mettapedia.OSLF.Binding

variable {Srt : Type} {nm : Srt}

theorem StepModulo.app {Γ : List Srt} {kind : Action} {source target : Expr nm Γ}
    (step : StepModulo kind source target) (argument : Var Γ nm) :
    StepModulo kind (.app source argument) (.app target argument) := by
  rcases step with ⟨first, second, before, firing, after⟩
  exact ⟨_, _, .app argument before, .app argument firing, .app argument after⟩

theorem StepModulo.defn {Γ : List Srt} {kind : Action} {source target : Expr nm (nm :: Γ)}
    (step : StepModulo kind source target) (value : Expr nm Γ) :
    StepModulo kind (.defn value source) (.defn value target) := by
  rcases step with ⟨first, second, before, firing, after⟩
  exact ⟨_, _, .defn (.refl _) before, .defn value firing, .defn (.refl _) after⟩

theorem StepModulo.carrier {Γ : List Srt} {kind : Action} {source target : Expr nm Γ}
    (step : StepModulo kind source target) (name : Var Γ nm) (value : Expr nm Γ) :
    StepModulo kind (.carrier name value source) (.carrier name value target) := by
  rcases step with ⟨first, second, before, firing, after⟩
  exact ⟨_, _, .carrier name (.refl _) before, .carrier name value firing,
    .carrier name (.refl _) after⟩

theorem StepModulo.changeSource {Γ : List Srt} {kind : Action} {source source' target : Expr nm Γ}
    (step : StepModulo kind source target) (equal : StructuralEq source' source) :
    StepModulo kind source' target := by
  rcases step with ⟨first, second, before, firing, after⟩
  exact ⟨_, _, .trans equal before, firing, after⟩

/-- A source lambda reached through only active environment constructors. -/
inductive ReturningLambda : {Γ : List Srt} → Expr nm Γ → Type where
  | lam {Γ} (body : Expr nm (nm :: Γ)) : ReturningLambda (.lam body)
  | defn {Γ} (value : Expr nm Γ) {body : Expr nm (nm :: Γ)} :
      ReturningLambda body → ReturningLambda (.defn value body)
  | carrier {Γ} (name : Var Γ nm) (value : Expr nm Γ) {body : Expr nm Γ} :
      ReturningLambda body → ReturningLambda (.carrier name value body)

/-- Compute the source successor before consulting any target execution. -/
def ReturningLambda.result : {Γ : List Srt} → {function : Expr nm Γ} →
    ReturningLambda function → Var Γ nm → Expr nm Γ
  | _, _, .lam body, argument => NamePassing.instantiate body argument
  | _, _, .defn value body, argument => .defn value (body.result (.succ argument))
  | _, _, .carrier name value body, argument => .carrier name value (body.result argument)

/-- Precisely one source beta event, with only published application-scope
administration and with all enclosing environments retained. -/
theorem ReturningLambda.call {Γ : List Srt} {function : Expr nm Γ}
    (returning : ReturningLambda function) (argument : Var Γ nm) :
    StepModulo .beta (.app function argument) (returning.result argument) := by
  induction returning with
  | lam body => exact (Step.beta body argument).toModulo
  | defn value body ih => exact ((ih (.succ argument)).defn value).changeSource (.appDefinition _ _ _)
  | carrier name value body ih => exact ((ih argument).carrier name value).changeSource (.appCarrier _ _ _ _)

end Mettapedia.Languages.LambdaCalculus.NamePassing.Environment
