import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Data

/-!
# Composition of terminating equation computations

These judgments expose successful computations of the existing evaluator.
Their introduction laws assemble finite runs, taking the maximum of the
required fuel amounts. They neither search for proofs nor interpret guest
operations. Exhaustion remains distinct from a completed result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

def Evaluates (P : Program) (H : Host) (environment : Env) (source result : Term) : Prop :=
  ∃ fuel, eval P H fuel environment source = .value result

def Applies (P : Program) (H : Host) (head : String) (arguments : List Term) (result : Term) : Prop :=
  ∃ fuel, apply P H fuel head arguments = .value result

theorem Evaluates.at_least {P : Program} {H : Host} {environment : Env} {source result : Term}
    (computation : Evaluates P H environment source result) :
    ∃ fuel, ∀ more, fuel ≤ more → eval P H more environment source = .value result := by
  obtain ⟨fuel, done⟩ := computation
  exact ⟨fuel, fun more enough => (eval_le enough (by rw [done]; intro h; cases h)).trans done⟩

theorem Applies.at_least {P : Program} {H : Host} {head : String} {arguments : List Term}
    {result : Term} (computation : Applies P H head arguments result) :
    ∃ fuel, ∀ more, fuel ≤ more → apply P H more head arguments = .value result := by
  obtain ⟨fuel, done⟩ := computation
  exact ⟨fuel, fun more enough => (apply_le enough (by rw [done]; intro h; cases h)).trans done⟩

theorem Evaluates.deterministic {P : Program} {H : Host} {environment : Env}
    {source first second : Term} (left : Evaluates P H environment source first)
    (right : Evaluates P H environment source second) : first = second := by
  obtain ⟨n, left⟩ := left.at_least
  obtain ⟨m, right⟩ := right.at_least
  exact Outcome.value.inj ((left (max n m) (Nat.le_max_left _ _)).symm.trans
    (right (max n m) (Nat.le_max_right _ _)))

theorem Applies.deterministic {P : Program} {H : Host} {head : String}
    {arguments : List Term} {first second : Term} (left : Applies P H head arguments first)
    (right : Applies P H head arguments second) : first = second := by
  obtain ⟨n, left⟩ := left.at_least
  obtain ⟨m, right⟩ := right.at_least
  exact Outcome.value.inj ((left (max n m) (Nat.le_max_left _ _)).symm.trans
    (right (max n m) (Nat.le_max_right _ _)))

/-- A completed run at any fuel agrees with the successful finite run.
In particular, a smaller fuel cannot turn resource exhaustion into refusal. -/
theorem Applies.completed {P : Program} {H : Host} {head : String} {arguments : List Term}
    {result : Term} (computation : Applies P H head arguments result) (fuel : Nat)
    (finished : apply P H fuel head arguments ≠ .exhausted) :
    apply P H fuel head arguments = .value result := by
  obtain ⟨needed, computed⟩ := computation.at_least
  have stable := apply_le (Nat.le_max_left fuel needed) finished
  exact stable.symm.trans (computed _ (Nat.le_max_right _ _))

theorem Evaluates.variable {P : Program} {H : Host} {environment : Env} {name : String}
    {value : Term} (found : environment.lookup name = some value) :
    Evaluates P H environment (.var name) value :=
  ⟨1, by simp [eval, evalStep, found]⟩

theorem Evaluates.symbol (P : Program) (H : Host) (environment : Env) (name : String) :
    Evaluates P H environment (.sym name) (.sym name) := ⟨1, rfl⟩

theorem Evaluates.literal (P : Program) (H : Host) (environment : Env) (spelling : String) :
    Evaluates P H environment (.lit spelling) (.lit spelling) := ⟨1, rfl⟩

theorem PassiveData.evaluates {P : Program} {H : Host} {value : Term}
    (passive : PassiveData P H value) (environment : Env) :
    Evaluates P H environment value value :=
  ⟨sizeOf value + 1, passive.eval_eq_value environment _ (Nat.lt_succ_self _)⟩

theorem evaluates_items {P : Program} {H : Host} {environment : Env} {sources results : List Term}
    (computations : List.Forall₂ (Evaluates P H environment) sources results) :
    ∃ fuel, ∀ more, fuel ≤ more → evalItems P H more environment sources = .values results := by
  induction computations with
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | cons first rest ih =>
      obtain ⟨n, first⟩ := first.at_least
      obtain ⟨m, tail⟩ := ih
      refine ⟨max n m, ?_⟩
      intro more enough
      have hf := first more ((Nat.le_max_left _ _).trans enough)
      have ht := tail more ((Nat.le_max_right _ _).trans enough)
      change (match eval P H more environment _ with
        | .value value => match evalItems P H more environment _ with
          | .values values => ItemsOutcome.values (value :: values)
          | .stop outcome => ItemsOutcome.stop outcome
        | outcome => ItemsOutcome.stop outcome) = _
      rw [hf, ht]

theorem Evaluates.call {P : Program} {H : Host} {environment : Env} {head : String}
    {arguments values : List Term} {result : Term} (ordinary : ¬ Special head arguments)
    (children : List.Forall₂ (Evaluates P H environment) arguments values)
    (operation : Applies P H head values result) :
    Evaluates P H environment (.expr (.sym head :: arguments)) result := by
  obtain ⟨n, children⟩ := evaluates_items children
  obtain ⟨m, operation⟩ := operation.at_least
  refine ⟨max n m + 1, ?_⟩
  rw [eval, evalStep_head ordinary]
  change (match evalItems P H (max n m) environment arguments with
    | .values values => apply P H (max n m) head values
    | .stop outcome => outcome) = _
  rw [children _ (Nat.le_max_left _ _)]
  exact operation _ (Nat.le_max_right _ _)

theorem Applies.equation {P : Program} {H : Host} {head : String} {arguments : List Term}
    {equation : Equation} {environment : Env} {result : Term}
    (defined : P.definesAt head arguments.length = true)
    (selected : P.select head arguments = some (equation, environment))
    (body : Evaluates P H environment equation.body result) :
    Applies P H head arguments result := by
  obtain ⟨fuel, body⟩ := body
  exact ⟨fuel, by simp [apply, applyWith, defined, selected, body]⟩

theorem Applies.primitive {P : Program} {H : Host} {head : String} {arguments : List Term}
    {result : Term} (undefined : P.defines head = false)
    (computed : H.primitive head arguments = .value result) :
    Applies P H head arguments result :=
  ⟨0, by simp [apply, applyWith, Program.definesAt_false_of_defines_false undefined, undefined,
    computed]⟩

theorem Applies.constructor {P : Program} {H : Host} {head : String} {arguments : List Term}
    (undefined : P.defines head = false) (unhandled : H.primitive head arguments = .unhandled) :
    Applies P H head arguments (.expr (.sym head :: arguments)) :=
  ⟨0, by simp [apply, applyWith, Program.definesAt_false_of_defines_false undefined, undefined,
    unhandled]⟩

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
