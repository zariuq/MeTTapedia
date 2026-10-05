import Mathlib.Data.List.Basic

/-!
# MM0 preterms and simultaneous substitution

The application-spine representation follows the upstream MM0 formal model:
variables, term symbols and binary application. Preterms may be partially
applied; sorting and admissibility are separate judgments.

Substitution replaces variables simultaneously. A missing entry refuses the
operation instead of manufacturing a default variable. `Substitutes` states
the independent graph relation; the evaluator's agreement and composition
laws do not assume typing, dependency safety or definition conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

inductive Preterm where
  | var (index : Nat)
  | term (index : Nat)
  | app (function argument : Preterm)
  deriving DecidableEq, Repr

namespace Preterm

def applyArgs : Preterm → List Preterm → Preterm
  | function, [] => function
  | function, argument :: arguments => applyArgs (.app function argument) arguments

@[simp] theorem applyArgs_nil (function : Preterm) : applyArgs function [] = function := rfl

theorem applyArgs_append (function : Preterm) (first second : List Preterm) :
    applyArgs function (first ++ second) = applyArgs (applyArgs function first) second := by
  induction first generalizing function with
  | nil => rfl
  | cons argument arguments ih => exact ih (.app function argument)

/-- Syntactic occurrence, including occurrences under binding term symbols.
MM0 theorem instantiation needs this distinction from free-variable analysis. -/
inductive Occurs (index : Nat) : Preterm → Prop where
  | var : Occurs index (.var index)
  | function {function argument} : Occurs index function → Occurs index (.app function argument)
  | argument {function argument} : Occurs index argument → Occurs index (.app function argument)

end Preterm

abbrev Substitution := Nat → Option Preterm

namespace Substitution

def ofList (values : List Preterm) : Substitution := fun index => values[index]?

def identity : Substitution := fun index => some (.var index)

end Substitution

namespace Preterm

def substitute (substitution : Substitution) : Preterm → Option Preterm
  | .var index => substitution index
  | .term index => some (.term index)
  | .app function argument => do
      let function' ← substitute substitution function
      let argument' ← substitute substitution argument
      pure (.app function' argument')

/-- Independent structural rules for simultaneous substitution. -/
inductive Substitutes (substitution : Substitution) : Preterm → Preterm → Prop where
  | var {index value} : substitution index = some value → Substitutes substitution (.var index) value
  | term (index) : Substitutes substitution (.term index) (.term index)
  | app {function argument function' argument'} :
      Substitutes substitution function function' →
      Substitutes substitution argument argument' →
      Substitutes substitution (.app function argument) (.app function' argument')

theorem Substitutes.eval {substitution : Substitution} {source result : Preterm}
    (derivation : Substitutes substitution source result) :
    substitute substitution source = some result := by
  induction derivation with
  | var lookup => exact lookup
  | term => rfl
  | app _ _ ihFunction ihArgument => simp [substitute, ihFunction, ihArgument]

theorem substitute_sound {substitution : Substitution} {source result : Preterm}
    (accepted : substitute substitution source = some result) :
    Substitutes substitution source result := by
  induction source generalizing result with
  | var index => exact .var accepted
  | term index =>
      simp only [substitute, Option.some.injEq] at accepted
      subst result
      exact .term index
  | app function argument ihFunction ihArgument =>
      cases hf : substitute substitution function with
      | none => simp [substitute, hf] at accepted
      | some function' =>
          cases ha : substitute substitution argument with
          | none => simp [substitute, hf, ha] at accepted
          | some argument' =>
              simp [substitute, hf, ha] at accepted
              subst result
              exact .app (ihFunction hf) (ihArgument ha)

theorem substitute_eq_some_iff (substitution : Substitution) (source result : Preterm) :
    substitute substitution source = some result ↔ Substitutes substitution source result :=
  ⟨substitute_sound, Substitutes.eval⟩

theorem Substitutes.deterministic {substitution : Substitution} {source first second : Preterm}
    (left : Substitutes substitution source first)
    (right : Substitutes substitution source second) : first = second :=
  Option.some.inj (left.eval.symm.trans right.eval)

theorem substitute_none_iff (substitution : Substitution) (source : Preterm) :
    substitute substitution source = none ↔ ¬ ∃ result, Substitutes substitution source result := by
  constructor
  · intro refused ⟨result, derivation⟩
    have accepted := derivation.eval
    rw [refused] at accepted
    contradiction
  · intro noDerivation
    cases h : substitute substitution source with
    | none => rfl
    | some result => exact False.elim (noDerivation ⟨result, substitute_sound h⟩)

theorem Substitutes.lookup_exists {substitution : Substitution} {source result : Preterm}
    (derivation : Substitutes substitution source result) :
    ∀ index, Occurs index source → ∃ value, substitution index = some value := by
  induction derivation with
  | var lookup =>
      intro index occurs
      cases occurs
      exact ⟨_, lookup⟩
  | term => intro index occurs; cases occurs
  | app _ _ ihFunction ihArgument =>
      intro index occurs
      cases occurs with
      | function h => exact ihFunction index h
      | argument h => exact ihArgument index h

/-- Exactly the variables occurring in the input need substitution entries. -/
theorem substitute_defined_iff (substitution : Substitution) (source : Preterm) :
    (∃ result, substitute substitution source = some result) ↔
      ∀ index, Occurs index source → ∃ value, substitution index = some value := by
  constructor
  · rintro ⟨result, accepted⟩
    exact (substitute_sound accepted).lookup_exists
  · intro lookups
    induction source with
    | var index => exact lookups index .var
    | term index => exact ⟨.term index, rfl⟩
    | app function argument ihFunction ihArgument =>
        obtain ⟨function', hf⟩ := ihFunction (fun index h => lookups index (.function h))
        obtain ⟨argument', ha⟩ := ihArgument (fun index h => lookups index (.argument h))
        exact ⟨.app function' argument', by simp [substitute, hf, ha]⟩

theorem substitute_ofList_defined_iff (values : List Preterm) (source : Preterm) :
    (∃ result, substitute (Substitution.ofList values) source = some result) ↔
      ∀ index, Occurs index source → index < values.length := by
  rw [substitute_defined_iff]
  constructor
  · intro lookups index occurrence
    obtain ⟨value, lookup⟩ := lookups index occurrence
    exact (List.getElem?_eq_some_iff.mp lookup).1
  · intro bounds index occurrence
    have h := bounds index occurrence
    exact ⟨values[index], List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩⟩

/-- Changes outside the input's variable support cannot affect its substitution. -/
theorem substitute_congr (first second : Substitution) (source : Preterm)
    (agree : ∀ index, Occurs index source → first index = second index) :
    substitute first source = substitute second source := by
  induction source with
  | var index => exact agree index .var
  | term => rfl
  | app function argument ihFunction ihArgument =>
      simp only [substitute,
        ihFunction (fun index h => agree index (.function h)),
        ihArgument (fun index h => agree index (.argument h))]

@[simp] theorem substitute_identity (source : Preterm) :
    substitute Substitution.identity source = some source := by
  induction source with
  | var => rfl
  | term => rfl
  | app function argument ihFunction ihArgument => simp [substitute, ihFunction, ihArgument]

end Preterm

namespace Substitution

/-- Apply `first` and then `second` to each replacement term. -/
def compose (second first : Substitution) : Substitution :=
  fun index => (first index).bind (Preterm.substitute second)

end Substitution

namespace Preterm

/-- Composition preserves refusal as well as every successful result. -/
theorem substitute_compose (second first : Substitution) (source : Preterm) :
    substitute (Substitution.compose second first) source =
      (substitute first source).bind (substitute second) := by
  induction source with
  | var => rfl
  | term => rfl
  | app function argument ihFunction ihArgument =>
      simp only [substitute, ihFunction, ihArgument]
      cases hf : substitute first function <;> cases ha : substitute first argument <;>
        simp [substitute]

theorem Substitutes.compose {second first : Substitution} {source middle result : Preterm}
    (before : Substitutes first source middle) (after : Substitutes second middle result) :
    Substitutes (Substitution.compose second first) source result := by
  apply substitute_sound
  rw [substitute_compose, before.eval]
  exact after.eval

/-- A composed derivation factors through the same intermediate computation. -/
theorem Substitutes.factor {second first : Substitution} {source result : Preterm}
    (derivation : Substitutes (Substitution.compose second first) source result) :
    ∃ middle, Substitutes first source middle ∧ Substitutes second middle result := by
  have accepted := derivation.eval
  rw [substitute_compose] at accepted
  cases h : substitute first source with
  | none => simp [h] at accepted
  | some middle =>
      exact ⟨middle, substitute_sound h, substitute_sound (by simpa [h] using accepted)⟩

end Preterm

end Mettapedia.Languages.MM0.Kernel
