import Mettapedia.Languages.MM0.Kernel.Term
import Mathlib.Data.Finset.Basic

/-!
# MM0 context-relative bound-variable support

A bound variable contributes its own context index. A regular open variable
contributes its declared bound dependencies. Applications retain the support
of every child, including arguments supplied to bound slots. This occurrence
analysis is distinct from binder-sensitive free-variable analysis.

The computation refuses undefined variables. It does not validate sorts,
dependency declarations, saturation or theorem substitution: those require
the separate context and typing judgments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

inductive Binder where
  | bound (sort : Nat)
  | regular (sort : Nat) (dependencies : Finset Nat)
  deriving DecidableEq

namespace Binder

def sort : Binder → Nat
  | .bound sort => sort
  | .regular sort _ => sort

end Binder

abbrev Context := List Binder

namespace Preterm

def support? (context : Context) : Preterm → Option (Finset Nat)
  | .var index => do
      match ← context[index]? with
      | .bound _ => pure {index}
      | .regular _ dependencies => pure dependencies
  | .term _ => some ∅
  | .app function argument => do
      let left ← support? context function
      let right ← support? context argument
      pure (left ∪ right)

/-- Independent rules computing complete context-relative occurrence support. -/
inductive Supports (context : Context) : Preterm → Finset Nat → Prop where
  | bound {index sort : Nat} :
      context[index]? = some (.bound sort) → Supports context (.var index) {index}
  | regular {index sort : Nat} {dependencies : Finset Nat} :
      context[index]? = some (.regular sort dependencies) →
      Supports context (.var index) dependencies
  | term (index : Nat) : Supports context (.term index) ∅
  | app {function argument : Preterm} {left right : Finset Nat} :
      Supports context function left → Supports context argument right →
      Supports context (.app function argument) (left ∪ right)

/-- An occurrence of a target bound variable, including declared dependencies
of regular variables and occurrences under binding constructors. -/
inductive HasVar (context : Context) (index : Nat) : Preterm → Prop where
  | bound {sort : Nat} : context[index]? = some (.bound sort) →
      HasVar context index (.var index)
  | regular {sourceIndex sort : Nat} {dependencies : Finset Nat} :
      context[sourceIndex]? = some (.regular sort dependencies) →
      index ∈ dependencies → HasVar context index (.var sourceIndex)
  | function {function argument : Preterm} :
      HasVar context index function → HasVar context index (.app function argument)
  | argument {function argument : Preterm} :
      HasVar context index argument → HasVar context index (.app function argument)

theorem hasVar_var_iff (context : Context) (index sourceIndex : Nat) :
    HasVar context index (.var sourceIndex) ↔
      (∃ sort, context[sourceIndex]? = some (.bound sort) ∧ index = sourceIndex) ∨
      ∃ sort dependencies, context[sourceIndex]? = some (.regular sort dependencies) ∧
        index ∈ dependencies := by
  constructor
  · intro occurs
    cases occurs with
    | bound lookup => exact .inl ⟨_, lookup, rfl⟩
    | regular lookup member => exact .inr ⟨_, _, lookup, member⟩
  · intro occurrence
    rcases occurrence with ⟨sort, lookup, same⟩ | ⟨sort, dependencies, lookup, member⟩
    · subst index
      exact .bound lookup
    · exact .regular lookup member

@[simp] theorem hasVar_term_iff (context : Context) (index symbol : Nat) :
    ¬ HasVar context index (.term symbol) := by
  intro occurs
  cases occurs

theorem hasVar_app_iff (context : Context) (index : Nat) (function argument : Preterm) :
    HasVar context index (.app function argument) ↔
      HasVar context index function ∨ HasVar context index argument := by
  constructor
  · intro occurs
    cases occurs with
    | function head => exact .inl head
    | argument tail => exact .inr tail
  · intro occurs
    cases occurs with
    | inl head => exact .function head
    | inr tail => exact .argument tail

theorem Supports.eval {context : Context} {source : Preterm} {support : Finset Nat}
    (derivation : Supports context source support) : support? context source = some support := by
  induction derivation with
  | bound lookup => simp [support?, lookup]
  | regular lookup => simp [support?, lookup]
  | term => rfl
  | app _ _ ihFunction ihArgument => simp [support?, ihFunction, ihArgument]

theorem support_sound {context : Context} {source : Preterm} {support : Finset Nat}
    (accepted : support? context source = some support) : Supports context source support := by
  induction source generalizing support with
  | var index =>
      cases lookup : context[index]? with
      | none => simp [support?, lookup] at accepted
      | some binder =>
          cases binder with
          | bound sort =>
              simp [support?, lookup] at accepted
              subst support
              exact .bound lookup
          | regular sort dependencies =>
              simp [support?, lookup] at accepted
              subst support
              exact .regular lookup
  | term symbol =>
      simp only [support?, Option.some.injEq] at accepted
      subst support
      exact .term symbol
  | app function argument ihFunction ihArgument =>
      cases left : support? context function with
      | none => simp [support?, left] at accepted
      | some functionSupport =>
          cases right : support? context argument with
          | none => simp [support?, left, right] at accepted
          | some argumentSupport =>
              simp [support?, left, right] at accepted
              subst support
              exact .app (ihFunction left) (ihArgument right)

theorem support_eq_some_iff (context : Context) (source : Preterm) (support : Finset Nat) :
    support? context source = some support ↔ Supports context source support :=
  ⟨support_sound, Supports.eval⟩

theorem Supports.deterministic {context : Context} {source : Preterm}
    {first second : Finset Nat} (left : Supports context source first)
    (right : Supports context source second) : first = second :=
  Option.some.inj (left.eval.symm.trans right.eval)

theorem support_none_iff (context : Context) (source : Preterm) :
    support? context source = none ↔ ¬ ∃ support, Supports context source support := by
  constructor
  · intro refused ⟨support, derivation⟩
    have accepted := derivation.eval
    rw [refused] at accepted
    contradiction
  · intro noDerivation
    cases result : support? context source with
    | none => rfl
    | some support => exact False.elim (noDerivation ⟨support, support_sound result⟩)

theorem Supports.mem_iff_hasVar {context : Context} {source : Preterm}
    {support : Finset Nat} (derivation : Supports context source support) (index : Nat) :
    index ∈ support ↔ HasVar context index source := by
  induction derivation with
  | bound lookup => simp [hasVar_var_iff, lookup]
  | regular lookup => simp [hasVar_var_iff, lookup]
  | term => simp
  | app _ _ ihFunction ihArgument =>
      simp only [Finset.mem_union, hasVar_app_iff, ihFunction, ihArgument]

theorem Supports.lookup_exists {context : Context} {source : Preterm}
    {support : Finset Nat} (derivation : Supports context source support) :
    ∀ index, Occurs index source → ∃ binder, context[index]? = some binder := by
  induction derivation with
  | bound lookup =>
      intro index occurs
      cases occurs
      exact ⟨_, lookup⟩
  | regular lookup =>
      intro index occurs
      cases occurs
      exact ⟨_, lookup⟩
  | term => intro index occurs; cases occurs
  | app _ _ ihFunction ihArgument =>
      intro index occurs
      cases occurs with
      | function head => exact ihFunction index head
      | argument tail => exact ihArgument index tail

/-- Undefined variable occurrences, rather than empty support, cause refusal. -/
theorem support_defined_iff (context : Context) (source : Preterm) :
    (∃ support, support? context source = some support) ↔
      ∀ index, Occurs index source → ∃ binder, context[index]? = some binder := by
  constructor
  · rintro ⟨support, accepted⟩
    exact (support_sound accepted).lookup_exists
  · intro lookups
    induction source with
    | var index =>
        obtain ⟨binder, lookup⟩ := lookups index .var
        cases binder with
        | bound sort => exact ⟨{index}, by simp [support?, lookup]⟩
        | regular sort dependencies => exact ⟨dependencies, by simp [support?, lookup]⟩
    | term symbol => exact ⟨∅, rfl⟩
    | app function argument ihFunction ihArgument =>
        obtain ⟨left, acceptedLeft⟩ := ihFunction (fun index h => lookups index (.function h))
        obtain ⟨right, acceptedRight⟩ := ihArgument (fun index h => lookups index (.argument h))
        exact ⟨left ∪ right, by simp [support?, acceptedLeft, acceptedRight]⟩

/-- A successful complete support computation detects exactly the independent
occurrences. A live child alone does not make an undefined whole preterm valid. -/
theorem support_membership_iff (context : Context) (source : Preterm) (index : Nat) :
    (∃ support, support? context source = some support ∧ index ∈ support) ↔
      (∃ support, support? context source = some support) ∧ HasVar context index source := by
  constructor
  · rintro ⟨support, accepted, member⟩
    exact ⟨⟨support, accepted⟩, ((support_sound accepted).mem_iff_hasVar index).mp member⟩
  · rintro ⟨⟨support, accepted⟩, occurs⟩
    exact ⟨support, accepted, ((support_sound accepted).mem_iff_hasVar index).mpr occurs⟩

/-- Every occurrence at any position of an application spine is retained. -/
theorem hasVar_applyArgs_iff (context : Context) (index : Nat)
    (function : Preterm) (arguments : List Preterm) :
    HasVar context index (applyArgs function arguments) ↔
      HasVar context index function ∨ ∃ argument ∈ arguments, HasVar context index argument := by
  induction arguments generalizing function with
  | nil => simp [applyArgs]
  | cons argument arguments ih =>
      rw [applyArgs, ih, hasVar_app_iff]
      simp only [List.mem_cons]
      constructor
      · rintro ((head | first) | ⟨child, member, occurs⟩)
        · exact .inl head
        · exact .inr ⟨argument, .inl rfl, first⟩
        · exact .inr ⟨child, .inr member, occurs⟩
      · rintro (head | ⟨child, same | member, occurs⟩)
        · exact .inl (.inl head)
        · subst child
          exact .inl (.inr occurs)
        · exact .inr ⟨child, member, occurs⟩

end Preterm

end Mettapedia.Languages.MM0.Kernel
