import Mathlib.Data.List.Monad
import Mathlib.Data.Fin.Basic

/-!
# Binding occurrences and callable names

A scoped sequencing occurrence and a runtime invocation are different syntax
constructors. Names, argument packets, effects and callable resolution remain
parameters. A packet can contain any number of arguments; arity selection
belongs to the resolver. In particular this interface imposes no globally
reserved spelling and no fixed language vocabulary.

Head specialization substitutes known callable names while retaining call
role, argument evaluation and the invocation handler. It remains valid for
any resolver, so it does not cache the absence of a declaration. The theorem
is about this intermediate representation, not a native compiler refinement.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BindingDispatch

universe u

inductive Head (Name : Type u) where
  | known : Name → Head Name
  | dynamic : Nat → Head Name
  deriving DecidableEq

variable {Name Value : Type u} {M : Type u → Type u}

def Head.resolve (names : Nat → Name) : Head Name → Name
  | .known name => name
  | .dynamic index => names index

def Head.specialize (known : Nat → Option Name) : Head Name → Head Name
  | .known name => .known name
  | .dynamic index => match known index with
      | some name => .known name
      | none => .dynamic index

def Agrees (known : Nat → Option Name) (names : Nat → Name) : Prop :=
  ∀ index name, known index = some name → names index = name

theorem Head.resolve_specialize (known : Nat → Option Name) (names : Nat → Name)
    (agrees : Agrees known names) (head : Head Name) :
    (head.specialize known).resolve names = head.resolve names := by
  cases head with
  | known name => rfl
  | dynamic index =>
      simp only [specialize]
      cases h : known index with
      | none => rfl
      | some name => exact (agrees index name h).symm

theorem Head.specialize_idempotent (known : Nat → Option Name) (head : Head Name) :
    (head.specialize known).specialize known = head.specialize known := by
  cases head with
  | known name => rfl
  | dynamic index => cases h : known index <;> simp [specialize, h]

/-- `none` means no applicable interpretation, not an interpreted call which
produced zero answers. Recovery applies to the callee, not its argument. -/
structure Runtime (M : Type u → Type u) (Name Value : Type u) where
  lookup : Name → Value → Option (M Value)
  data : Name → Value → Value
  recover : M Value → M Value

def Runtime.invoke [Monad M] (runtime : Runtime M Name Value)
    (name : Name) (argument : Value) : M Value :=
  match runtime.lookup name argument with
  | some computation => runtime.recover computation
  | none => pure (runtime.data name argument)

theorem Runtime.invoke_declared [Monad M] (runtime : Runtime M Name Value)
    (name : Name) (argument : Value) (computation : M Value)
    (found : runtime.lookup name argument = some computation) :
    runtime.invoke name argument = runtime.recover computation := by
  simp only [invoke, found]

theorem Runtime.invoke_unknown [Monad M] (runtime : Runtime M Name Value)
    (name : Name) (argument : Value) (absent : runtime.lookup name argument = none) :
    runtime.invoke name argument = pure (runtime.data name argument) := by
  simp only [invoke, absent]

inductive Expr (M : Type u → Type u) (Name Value : Type u) : Nat → Type u where
  | value {n} : Value → Expr M Name Value n
  | var {n} : Fin n → Expr M Name Value n
  | action {n} : M Value → Expr M Name Value n
  | bind {n} : Expr M Name Value n → Expr M Name Value (n + 1) → Expr M Name Value n
  | invoke {n} : Head Name → Expr M Name Value n → Expr M Name Value n

def push {n : Nat} (value : Value) (env : Fin n → Value) : Fin (n + 1) → Value :=
  Fin.cases value env

def Expr.eval [Monad M] (runtime : Runtime M Name Value) (names : Nat → Name) :
    {n : Nat} → Expr M Name Value n → (Fin n → Value) → M Value
  | _, .value payload, _ => pure payload
  | _, .var index, env => pure (env index)
  | _, .action computation, _ => computation
  | _, .bind source body, env => do
      let value ← source.eval runtime names env
      body.eval runtime names (push value env)
  | _, .invoke head argument, env => do
      let value ← argument.eval runtime names env
      runtime.invoke (head.resolve names) value

def Expr.specialize (known : Nat → Option Name) :
    {n : Nat} → Expr M Name Value n → Expr M Name Value n
  | _, .value payload => .value payload
  | _, .var index => .var index
  | _, .action computation => .action computation
  | _, .bind source body => .bind (source.specialize known) (body.specialize known)
  | _, .invoke head argument => .invoke (head.specialize known) (argument.specialize known)

/-- Specialization eliminates dynamic name lookups without changing an
invocation into binding syntax. No law is required of the handler. -/
theorem Expr.eval_specialize [Monad M] (runtime : Runtime M Name Value)
    (known : Nat → Option Name) (names : Nat → Name) (agrees : Agrees known names)
    {n : Nat} (expr : Expr M Name Value n) (env : Fin n → Value) :
    (expr.specialize known).eval runtime names env = expr.eval runtime names env := by
  induction expr with
  | value value => rfl
  | var index => rfl
  | action computation => rfl
  | bind source body ihSource ihBody => simp only [specialize, eval, ihSource, ihBody]
  | invoke head argument ih =>
      simp only [specialize, eval, ih, Head.resolve_specialize known names agrees]

theorem Expr.specialize_idempotent (known : Nat → Option Name)
    {n : Nat} (expr : Expr M Name Value n) :
    (expr.specialize known).specialize known = expr.specialize known := by
  induction expr <;> simp_all only [specialize, Head.specialize_idempotent]

/-- Renaming value variables is independent of specializing callable names. -/
def Expr.rename : {n m : Nat} → (Fin n → Fin m) →
    Expr M Name Value n → Expr M Name Value m
  | _, _, _, .value payload => .value payload
  | _, _, ρ, .var index => .var (ρ index)
  | _, _, _, .action computation => .action computation
  | _, _, ρ, .bind source body =>
      .bind (source.rename ρ) (body.rename (Fin.cases 0 (fun i => (ρ i).succ)))
  | _, _, ρ, .invoke head argument => .invoke head (argument.rename ρ)

theorem Expr.specialize_rename (known : Nat → Option Name) {n m : Nat}
    (expr : Expr M Name Value n) (ρ : Fin n → Fin m) :
    (expr.rename ρ).specialize known = (expr.specialize known).rename ρ := by
  induction expr generalizing m <;> simp_all only [rename, specialize]

end Mettapedia.TypeTheory.BindingDispatch
