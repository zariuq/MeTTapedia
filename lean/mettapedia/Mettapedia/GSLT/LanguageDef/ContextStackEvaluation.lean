import Mathlib.Data.Option.Basic

/-!
# Evaluating calls inside constructors with a context stack

An equation body such as `(Cons $x (app $xs $ys))` builds a value around a
further call.  Evaluated directly, the call runs first and the constructor is
applied to its value when it returns (`direct`): every level of the recursion
waits for the one inside it.

A context-stack evaluation records the constructor with its other children,
as a one-hole context, and continues with the inner call at once
(`withContexts`).  When a call finally answers a value, the recorded contexts
are applied to it, innermost first (`plug`).  No level waits, so the
recursion runs as a loop.

The two agree: with the same fuel, evaluating a call under contexts `K` gives
the direct value of the call with `K` applied (`withContexts_eq`), and with
no contexts the direct value itself (`withContexts_nil`).  The order matters:
applying the contexts outermost first builds a different value
(`plug_order_matters`).
-/

namespace Mettapedia.GSLT.LanguageDef.ContextStackEvaluation

/-- What the equation a call selects does: answer a value, or build a value
around a further call, given as the one-hole context that builds it. -/
inductive Step (V C : Type*) where
  | done (v : V)
  | wrap (context : V → V) (next : C)

variable {V C : Type*}

/-- Direct evaluation: a context waits for the value of its call.  `none` is
a call that selects no equation, or runs out of fuel. -/
def direct (step : C → Option (Step V C)) : Nat → C → Option V
  | 0, _ => none
  | n + 1, c =>
    match step c with
    | none => none
    | some (.done v) => some v
    | some (.wrap context next) => (direct step n next).map context

/-- Apply recorded contexts to a value, the most recently recorded first. -/
def plug : List (V → V) → V → V
  | [], v => v
  | context :: rest, v => plug rest (context v)

/-- Context-stack evaluation: a context is recorded and the inner call runs
at once; the value a call answers gets every recorded context. -/
def withContexts (step : C → Option (Step V C)) :
    Nat → List (V → V) → C → Option V
  | 0, _, _ => none
  | n + 1, contexts, c =>
    match step c with
    | none => none
    | some (.done v) => some (plug contexts v)
    | some (.wrap context next) => withContexts step n (context :: contexts) next

theorem plug_cons (context : V → V) (rest : List (V → V)) (v : V) :
    plug (context :: rest) v = plug rest (context v) := rfl

/-- Evaluating under recorded contexts is direct evaluation followed by
applying them. -/
theorem withContexts_eq (step : C → Option (Step V C)) :
    ∀ (n : Nat) (contexts : List (V → V)) (c : C),
      withContexts step n contexts c = (direct step n c).map (plug contexts)
  | 0, _, _ => rfl
  | n + 1, contexts, c => by
    unfold withContexts direct
    cases h : step c with
    | none => rfl
    | some s =>
      cases s with
      | done v => rfl
      | wrap context next =>
        show withContexts step n (context :: contexts) next =
          Option.map (plug contexts) (Option.map context (direct step n next))
        rw [withContexts_eq step n (context :: contexts) next, Option.map_map]
        rfl

/-- With nothing recorded, context-stack evaluation is direct evaluation. -/
theorem withContexts_nil (step : C → Option (Step V C)) (n : Nat) (c : C) :
    withContexts step n [] c = direct step n c := by
  rw [withContexts_eq]
  cases direct step n c <;> rfl

/-- A call that answers under one evaluation answers the same under the
other, whatever contexts are recorded. -/
theorem withContexts_some_iff (step : C → Option (Step V C)) (n : Nat)
    (contexts : List (V → V)) (c : C) (v : V) :
    withContexts step n contexts c = some v ↔
      ∃ w, direct step n c = some w ∧ plug contexts w = v := by
  rw [withContexts_eq]
  cases direct step n c with
  | none =>
    constructor
    · intro h
      cases h
    · rintro ⟨_, h, _⟩
      cases h
  | some w =>
    constructor
    · intro h
      exact ⟨w, rfl, Option.some.inj h⟩
    · rintro ⟨w', hw, rfl⟩
      rw [Option.some.inj hw]
      rfl

/-- Applying the contexts outermost first is not the same evaluation: two
contexts that do not commute give different values. -/
theorem plug_order_matters :
    plug [(fun n : Nat => n + 1), (fun n => 2 * n)] 0 ≠
      plug [(fun n : Nat => 2 * n), (fun n => n + 1)] 0 := by
  decide

end Mettapedia.GSLT.LanguageDef.ContextStackEvaluation
