import Mettapedia.Languages.LambdaCalculus.NamePassingEnvironment

/-!
# Application scope laws for the nonrecursive name-passing fragment

Dal Zilio, `A Bisimulation for the Blue Calculus` (INRIA RR-3664),
Section 2.1, gives `(def p = R in P) u` equal to
`def p = R in (P u)` when `u` is not the defined name. An outer argument
becomes `succ argument` here, so the side condition is structural.

Section 2.2 distributes application over parallel composition and leaves
a one-shot declaration unchanged when applied. The existing `carrier`
constructor packages a body with such a declaration, giving the carrier
application law below. These laws supplement the independently authored
environment transitions; no source rule is defined by target execution.
This is the stated nonrecursive fragment, not the full recursive Blue
Calculus or its complete structural theory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.Environment

open Mettapedia.OSLF.Binding

variable {Srt : Type} {nm : Srt}

/-- Static application administration, including its actual source scopes. -/
inductive StructuralEq : {Γ : List Srt} → Expr nm Γ → Expr nm Γ → Prop where
  | refl {Γ} (term : Expr nm Γ) : StructuralEq term term
  | symm {Γ} {first second : Expr nm Γ} :
      StructuralEq first second → StructuralEq second first
  | trans {Γ} {first second third : Expr nm Γ} :
      StructuralEq first second → StructuralEq second third → StructuralEq first third
  | appDefinition {Γ} (value : Expr nm Γ) (body : Expr nm (nm :: Γ))
      (argument : Var Γ nm) :
      StructuralEq (.app (.defn value body) argument)
        (.defn value (.app body (.succ argument)))
  | appCarrier {Γ} (name : Var Γ nm) (value body : Expr nm Γ)
      (argument : Var Γ nm) :
      StructuralEq (.app (.carrier name value body) argument)
        (.carrier name value (.app body argument))
  | lam {Γ} {body body' : Expr nm (nm :: Γ)} :
      StructuralEq body body' → StructuralEq (.lam body) (.lam body')
  | app {Γ} {function function' : Expr nm Γ} (argument : Var Γ nm) :
      StructuralEq function function' → StructuralEq (.app function argument) (.app function' argument)
  | defn {Γ} {value value' : Expr nm Γ} {body body' : Expr nm (nm :: Γ)} :
      StructuralEq value value' → StructuralEq body body' →
        StructuralEq (.defn value body) (.defn value' body')
  | carrier {Γ} (name : Var Γ nm) {value value' body body' : Expr nm Γ} :
      StructuralEq value value' → StructuralEq body body' →
        StructuralEq (.carrier name value body) (.carrier name value' body')

theorem StructuralEq.rename {Γ Δ : List Srt}
    (environment : (s : Srt) → Var Γ s → Var Δ s) {first second : Expr nm Γ}
    (equal : StructuralEq first second) :
    StructuralEq (NamePassing.rename environment first) (NamePassing.rename environment second) := by
  induction equal generalizing Δ with
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih environment)
  | trans _ _ firstIH secondIH => exact .trans (firstIH environment) (secondIH environment)
  | appDefinition value body argument =>
      exact .appDefinition (NamePassing.rename environment value)
        (NamePassing.rename (liftRen environment [nm]) body) (environment _ argument)
  | appCarrier name value body argument =>
      exact .appCarrier (environment _ name) (NamePassing.rename environment value)
        (NamePassing.rename environment body) (environment _ argument)
  | lam _ ih => exact .lam (ih (liftRen environment [nm]))
  | app argument _ ih => exact .app (environment _ argument) (ih environment)
  | defn _ _ valueIH bodyIH => exact .defn (valueIH environment) (bodyIH (liftRen environment [nm]))
  | carrier name _ _ valueIH bodyIH =>
      exact .carrier (environment _ name) (valueIH environment) (bodyIH environment)

/-- One existing source communication with static administration at its
supplied endpoints. The action still records beta versus either lookup. -/
def StepModulo {Γ : List Srt} (action : Action) (source target : Expr nm Γ) : Prop :=
  ∃ activeSource activeTarget, StructuralEq source activeSource ∧
    Step action activeSource activeTarget ∧ StructuralEq activeTarget target

theorem Step.toModulo {Γ : List Srt} {action : Action} {source target : Expr nm Γ}
    (step : Step action source target) : StepModulo action source target :=
  ⟨source, target, .refl source, step, .refl target⟩

theorem StepModulo.rename {Γ Δ : List Srt}
    (environment : (s : Srt) → Var Γ s → Var Δ s) {action : Action}
    {source target : Expr nm Γ} (step : StepModulo action source target) :
    StepModulo action (NamePassing.rename environment source) (NamePassing.rename environment target) := by
  obtain ⟨activeSource, activeTarget, before, firing, after⟩ := step
  exact ⟨_, _, before.rename environment, firing.rename environment, after.rename environment⟩

/-- The floating declaration stays in place when the wrapped lambda is called. -/
theorem carrier_wrapped_beta {Γ : List Srt} (name : Var Γ nm) (value : Expr nm Γ)
    (body : Expr nm (nm :: Γ)) (argument : Var Γ nm) :
    StepModulo .beta (.app (.carrier name value (.lam body)) argument)
      (.carrier name value (NamePassing.instantiate body argument)) :=
  ⟨_, _, .appCarrier name value (.lam body) argument,
    .carrier name value (.beta body argument), .refl _⟩

/-- Application crosses a fresh definition scope without capturing its argument. -/
theorem definition_wrapped_beta {Γ : List Srt} (value : Expr nm Γ)
    (body : Expr nm (nm :: nm :: Γ)) (argument : Var Γ nm) :
    StepModulo .beta (.app (.defn value (.lam body)) argument)
      (.defn value (NamePassing.instantiate body (.succ argument))) :=
  ⟨_, _, .appDefinition value (.lam body) argument,
    .defn value (.beta body (.succ argument)), .refl _⟩

end Mettapedia.Languages.LambdaCalculus.NamePassing.Environment
