/-
# Beta-eta conversion for the Pure dependent fragment

This file adds conversion without changing Pure's universe-free scope.  The
relation is defined independently of the executable normalizer: beta and eta
contraction, congruence, and transitivity.  The normalizer is then proved to
produce a reduct, so equality of computed normal forms is a sound conversion
test.
-/

import Mettapedia.GSLT.LanguageDef.Pure.Statics

namespace Mettapedia.GSLT.LanguageDef.PureBetaEta

open Mettapedia.GSLT.LanguageDef.Pure

/-- Remove the binder at `cutoff`, failing exactly when it occurs free. -/
def unbind (cutoff : Nat) : Expr → Option Expr
  | .sort => some .sort
  | .bvar index =>
      if index < cutoff then some (.bvar index)
      else if index = cutoff then none
      else some (.bvar (index - 1))
  | .pi domain body => do
      pure (.pi (← unbind cutoff domain) (← unbind (cutoff + 1) body))
  | .lam domain body => do
      pure (.lam (← unbind cutoff domain) (← unbind (cutoff + 1) body))
  | .app fn argument => do
      pure (.app (← unbind cutoff fn) (← unbind cutoff argument))

/-- Beta/eta reduction closed under every expression constructor. -/
inductive Reduces : Expr → Expr → Prop where
  | refl {expression} : Reduces expression expression
  | beta {domain body argument} :
      Reduces (.app (.lam domain body) argument) (Expr.subst0 argument body)
  | eta {domain fn reduced} :
      unbind 0 fn = some reduced →
      Reduces (.lam domain (.app fn (.bvar 0))) reduced
  | pi {domain domain' body body'} :
      Reduces domain domain' → Reduces body body' →
      Reduces (.pi domain body) (.pi domain' body')
  | lam {domain domain' body body'} :
      Reduces domain domain' → Reduces body body' →
      Reduces (.lam domain body) (.lam domain' body')
  | app {fn fn' argument argument'} :
      Reduces fn fn' → Reduces argument argument' →
      Reduces (.app fn argument) (.app fn' argument')
  | trans {first second third} :
      Reduces first second → Reduces second third → Reduces first third

/-- Conversion by reduction to a common beta-eta reduct. -/
inductive Conv : Expr → Expr → Prop where
  | common {left right common} :
      Reduces left common → Reduces right common → Conv left right

mutual
/-- Fuel-bounded full beta normalization. -/
def betaNf : Nat → Expr → Expr
  | 0, expression => expression
  | _fuel + 1, .sort => .sort
  | _fuel + 1, .bvar index => .bvar index
  | fuel + 1, .pi domain body => .pi (betaNf fuel domain) (betaNf fuel body)
  | fuel + 1, .lam domain body => .lam (betaNf fuel domain) (betaNf fuel body)
  | fuel + 1, .app fn argument =>
      betaNfApp fuel (betaNf fuel fn) (betaNf fuel argument)

/-- One normalized application step. -/
def betaNfApp : Nat → Expr → Expr → Expr
  | 0, fn, argument => .app fn argument
  | fuel + 1, .lam _ body, argument => betaNf fuel (Expr.subst0 argument body)
  | _, fn, argument => .app fn argument
end

/-- Contract eta redexes after recursively normalizing their components. -/
def etaNf : Expr → Expr
  | .sort => .sort
  | .bvar index => .bvar index
  | .pi domain body => .pi (etaNf domain) (etaNf body)
  | .app fn argument => .app (etaNf fn) (etaNf argument)
  | .lam domain body =>
      let normalizedDomain := etaNf domain
      let normalizedBody := etaNf body
      match normalizedBody with
      | .app fn (.bvar 0) =>
          match unbind 0 fn with
          | some reduced => reduced
          | none => .lam normalizedDomain normalizedBody
      | _ => .lam normalizedDomain normalizedBody

/-- The fixed fuel used by the finite DTTBench bridge. -/
def normalizationFuel : Nat := 512

def normalForm (expression : Expr) : Expr :=
  etaNf (betaNf normalizationFuel expression)

def convBool (left right : Expr) : Bool := normalForm left == normalForm right

theorem betaNf_betaNfApp_sound : ∀ fuel,
    (∀ expression, Reduces expression (betaNf fuel expression)) ∧
    (∀ fn argument, Reduces (.app fn argument) (betaNfApp fuel fn argument)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro expression
        exact Reduces.refl
      · intro fn argument
        exact Reduces.refl
  | succ fuel ih =>
      constructor
      · intro expression
        cases expression with
        | sort => exact Reduces.refl
        | bvar index => exact Reduces.refl
        | pi domain body => exact Reduces.pi (ih.1 domain) (ih.1 body)
        | lam domain body => exact Reduces.lam (ih.1 domain) (ih.1 body)
        | app fn argument =>
            exact Reduces.trans
              (Reduces.app (ih.1 fn) (ih.1 argument))
              (ih.2 (betaNf fuel fn) (betaNf fuel argument))
      · intro fn argument
        cases fn with
        | lam domain body =>
            exact Reduces.trans Reduces.beta
              (ih.1 (Expr.subst0 argument body))
        | sort => exact Reduces.refl
        | bvar index => exact Reduces.refl
        | pi domain body => exact Reduces.refl
        | app nestedFn nestedArgument => exact Reduces.refl

theorem betaNf_sound (fuel : Nat) (expression : Expr) :
    Reduces expression (betaNf fuel expression) :=
  (betaNf_betaNfApp_sound fuel).1 expression

theorem betaNfApp_sound (fuel : Nat) (fn argument : Expr) :
    Reduces (.app fn argument) (betaNfApp fuel fn argument) :=
  (betaNf_betaNfApp_sound fuel).2 fn argument

theorem etaNf_sound (expression : Expr) : Reduces expression (etaNf expression) := by
  induction expression with
  | sort => exact Reduces.refl
  | bvar index => exact Reduces.refl
  | pi domain body domainIH bodyIH =>
      exact Reduces.pi domainIH bodyIH
  | app fn argument fnIH argumentIH =>
      exact Reduces.app fnIH argumentIH
  | lam domain body domainIH bodyIH =>
      rw [etaNf]
      generalize hdomain : etaNf domain = normalizedDomain
      generalize hbody : etaNf body = normalizedBody
      rw [hdomain] at domainIH
      rw [hbody] at bodyIH
      have hstructure :
          Reduces (.lam domain body) (.lam normalizedDomain normalizedBody) :=
        Reduces.lam domainIH bodyIH
      cases normalizedBody with
      | sort => exact hstructure
      | bvar index => exact hstructure
      | pi bodyDomain bodyBody => exact hstructure
      | lam bodyDomain bodyBody => exact hstructure
      | app fn argument =>
          cases argument with
          | sort => exact hstructure
          | pi argumentDomain argumentBody => exact hstructure
          | lam argumentDomain argumentBody => exact hstructure
          | app argumentFn argumentArgument => exact hstructure
          | bvar index =>
              cases index with
              | succ index => exact hstructure
              | zero =>
                  cases hunbind : unbind 0 fn with
                  | none => simpa [hunbind] using hstructure
                  | some reduced =>
                      simpa [hunbind] using
                        Reduces.trans hstructure (Reduces.eta hunbind)

theorem normalForm_sound (expression : Expr) :
    Reduces expression (normalForm expression) :=
  Reduces.trans (betaNf_sound normalizationFuel expression)
    (etaNf_sound (betaNf normalizationFuel expression))

theorem convBool_sound {left right : Expr}
    (hconv : convBool left right = true) : Conv left right := by
  unfold convBool at hconv
  have heq : normalForm left = normalForm right := of_decide_eq_true hconv
  exact Conv.common (normalForm_sound left) (heq ▸ normalForm_sound right)

theorem convBool_refl (expression : Expr) : convBool expression expression = true := by
  simp [convBool]

/-! Executable positive and negative conversion fixtures. -/

example :
    convBool (.app (.lam .sort (.bvar 0)) .sort) .sort = true := by decide

example :
    convBool (.lam .sort (.app (.bvar 1) (.bvar 0))) (.bvar 0) = true := by decide

example : convBool (.bvar 0) .sort = false := by decide

end Mettapedia.GSLT.LanguageDef.PureBetaEta
