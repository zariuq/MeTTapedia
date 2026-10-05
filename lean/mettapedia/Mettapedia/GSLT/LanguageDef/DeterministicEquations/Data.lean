import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Termination

/-!
# Constructor data in deterministic equation programs

Kernel terms are data. A constructor vocabulary must stay disjoint from the
program's defined heads, the host's primitives and the evaluator's special
forms. This module states that condition structurally and proves that
evaluation preserves every such data term. It does not assume the desired
evaluation result or impose a fixed depth limit.

Values obtained from a variable binding are already values: reading a binding
does not evaluate its contents. This also explains why the direct application
interface can receive kernel syntax containing arbitrary guest names.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

/-- Constructor syntax that evaluation may traverse without interpreting it. -/
inductive PassiveData (P : Program) (H : Host) : Term → Prop where
  | sym (name : String) : PassiveData P H (.sym name)
  | lit (spelling : String) : PassiveData P H (.lit spelling)
  | nil : PassiveData P H (.expr [])
  | node {head : String} {arguments : List Term} :
      (¬ Special head arguments) → P.defines head = false →
      H.primitive head arguments = .unhandled →
      (∀ argument ∈ arguments, PassiveData P H argument) →
      PassiveData P H (.expr (.sym head :: arguments))
  | list {arguments : List Term} :
      (∀ argument ∈ arguments, PassiveData P H argument) →
      PassiveData P H (.list arguments)

theorem Program.definesAt_false_of_defines_false {P : Program} {head : String}
    (undefined : P.defines head = false) (arity : Nat) : P.definesAt head arity = false := by
  simp only [Program.defines, List.any_eq_false] at undefined
  simp only [Program.definesAt, List.any_eq_false]
  intro equation member
  simp [undefined equation member]

theorem evalItemsWith_preserves {ev : Env → Term → Outcome} {environment : Env}
    (arguments : List Term)
    (preserves : ∀ argument ∈ arguments, ev environment argument = .value argument) :
    evalItemsWith ev environment arguments = .values arguments := by
  induction arguments with
  | nil => rfl
  | cons first rest ih =>
      simp only [evalItemsWith, preserves first (by simp)]
      rw [ih (fun argument member => preserves argument (by simp [member]))]

/-- An explicit sufficient fuel bound, independent of guest syntax and names. -/
theorem PassiveData.eval_eq_value {P : Program} {H : Host} {value : Term}
    (data : PassiveData P H value) (environment : Env) (fuel : Nat)
    (enough : sizeOf value < fuel) : eval P H fuel environment value = .value value := by
  induction fuel generalizing value with
  | zero => omega
  | succ fuel ih =>
      cases data with
      | sym => rfl
      | lit => rfl
      | nil => rfl
      | @node head arguments ordinary undefined unhandled children =>
          have items : evalItemsWith (eval P H fuel) environment arguments = .values arguments := by
            apply evalItemsWith_preserves
            intro argument member
            apply ih (children argument member)
            have smaller := List.sizeOf_lt_of_mem member
            simp only [Term.expr.sizeOf_spec, List.cons.sizeOf_spec] at enough
            omega
          rw [eval, evalStep_head ordinary, items]
          simp [applyWith, undefined, Program.definesAt_false_of_defines_false undefined, unhandled]
      | @list arguments children =>
          have items : evalItemsWith (eval P H fuel) environment arguments = .values arguments := by
            apply evalItemsWith_preserves
            intro argument member
            apply ih (children argument member)
            have smaller := List.sizeOf_lt_of_mem member
            simp only [Term.list.sizeOf_spec] at enough
            omega
          simp only [eval, evalStep, items]

theorem PassiveData.terminates {P : Program} {H : Host} {value : Term}
    (data : PassiveData P H value) (environment : Env) :
    ∃ fuel, eval P H fuel environment value = .value value :=
  ⟨sizeOf value + 1, data.eval_eq_value environment _ (Nat.lt_succ_self _)⟩

/-- All completed evaluations of passive data give that same data. -/
theorem PassiveData.completed {P : Program} {H : Host} {value : Term}
    (data : PassiveData P H value) (environment : Env) (fuel : Nat)
    (finished : eval P H fuel environment value ≠ .exhausted) :
    eval P H fuel environment value = .value value := by
  have stable := eval_mono P H fuel (sizeOf value + 1) environment value finished
  have computed := data.eval_eq_value environment (fuel + (sizeOf value + 1)) (by omega)
  exact stable.symm.trans computed

/-- Reading a value is not a request to execute that value. -/
theorem eval_bound_value (P : Program) (H : Host) (environment : Env) (name : String)
    (value : Term) (fuel : Nat) (lookup : environment.lookup name = some value) :
    eval P H (fuel + 1) environment (.var name) = .value value := by
  simp [eval, evalStep, lookup]

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
