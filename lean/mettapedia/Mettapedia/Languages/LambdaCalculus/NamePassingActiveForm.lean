import Mettapedia.Languages.LambdaCalculus.NamePassingEnvironmentEquations

/-!
# Exposing the active functional spine by published application equations

Only active application paths are rearranged. Lambda bodies and stored values
remain suspended. Outer definitions retain their exact binder and value, and
one-shot carriers retain their declaration. The resulting head form supplies
the source-side structure needed to identify a private call in a compiled
active frontier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.Environment

open Mettapedia.OSLF.Binding

variable {Srt : Type} {nm : Srt}

/-- A function spine with no definition or carrier between its pending calls. -/
inductive FunctionalSpine : {Γ : List Srt} → Expr nm Γ → Prop where
  | var {Γ} (name : Var Γ nm) : FunctionalSpine (.var name)
  | lam {Γ} (body : Expr nm (nm :: Γ)) : FunctionalSpine (.lam body)
  | app {Γ} {function : Expr nm Γ} (argument : Var Γ nm) :
      FunctionalSpine function → FunctionalSpine (.app function argument)

/-- The declarations enclosing that spine remain in their original order. -/
inductive ActiveForm : {Γ : List Srt} → Expr nm Γ → Prop where
  | spine {Γ} {term : Expr nm Γ} : FunctionalSpine term → ActiveForm term
  | defn {Γ} (value : Expr nm Γ) {body : Expr nm (nm :: Γ)} :
      ActiveForm body → ActiveForm (.defn value body)
  | carrier {Γ} (name : Var Γ nm) (value : Expr nm Γ) {body : Expr nm Γ} :
      ActiveForm body → ActiveForm (.carrier name value body)

/-- Push a pending argument through only its enclosing active declarations. -/
def applyActive : {Γ : List Srt} → Expr nm Γ → Var Γ nm → Expr nm Γ
  | _, .defn value body, argument => .defn value (applyActive body (.succ argument))
  | _, .carrier name value body, argument => .carrier name value (applyActive body argument)
  | _, .var name, argument => .app (.var name) argument
  | _, .lam body, argument => .app (.lam body) argument
  | _, .app function old, argument => .app (.app function old) argument

theorem applyActive_equivalent {Γ : List Srt} (function : Expr nm Γ) (argument : Var Γ nm) :
    StructuralEq (.app function argument) (applyActive function argument) := by
  induction function with
  | var => exact .refl _
  | lam => exact .refl _
  | app => exact .refl _
  | defn value body valueIH bodyIH =>
      exact .trans (.appDefinition _ _ _) (.defn (.refl _) (bodyIH (.succ argument)))
  | carrier name value body valueIH bodyIH =>
      exact .trans (.appCarrier _ _ _ _) (.carrier _ (.refl _) (bodyIH argument))

theorem applyActive_form {Γ : List Srt} {function : Expr nm Γ}
    (active : ActiveForm function) (argument : Var Γ nm) :
    ActiveForm (applyActive function argument) := by
  induction active with
  | spine spine =>
      cases spine with
      | var => exact .spine (.app _ (.var _))
      | lam => exact .spine (.app _ (.lam _))
      | app argument previous => exact .spine (.app _ (.app argument previous))
  | defn value active ih => exact .defn value (ih (.succ argument))
  | carrier name value active ih => exact .carrier name value (ih argument)

/-- Rearrange precisely the active path; suspended subexpressions are unchanged. -/
def activeForm : {Γ : List Srt} → Expr nm Γ → Expr nm Γ
  | _, .var name => .var name
  | _, .lam body => .lam body
  | _, .app function argument => applyActive (activeForm function) argument
  | _, .defn value body => .defn value (activeForm body)
  | _, .carrier name value body => .carrier name value (activeForm body)

theorem activeForm_equivalent {Γ : List Srt} (term : Expr nm Γ) :
    StructuralEq term (activeForm term) := by
  induction term with
  | var => exact .refl _
  | lam => exact .refl _
  | app function argument ih =>
      exact .trans (.app argument ih) (applyActive_equivalent _ _)
  | defn value body valueIH bodyIH => exact .defn (.refl _) bodyIH
  | carrier name value body valueIH bodyIH => exact .carrier name (.refl _) bodyIH

theorem activeForm_is_active {Γ : List Srt} (term : Expr nm Γ) :
    ActiveForm (activeForm term) := by
  induction term with
  | var => exact .spine (.var _)
  | lam => exact .spine (.lam _)
  | app function argument ih => exact applyActive_form ih argument
  | defn value body valueIH bodyIH => exact .defn value bodyIH
  | carrier name value body valueIH bodyIH => exact .carrier name value bodyIH

end Mettapedia.Languages.LambdaCalculus.NamePassing.Environment
