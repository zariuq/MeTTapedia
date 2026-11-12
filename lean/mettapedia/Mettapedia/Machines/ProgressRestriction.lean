import Mettapedia.Machines.ProgressObservation

/-!
# Progress on an invariant domain

Well-foundedness is needed on the modeled execution domain. Restricting a
quiver to a predicate is sound for executions starting there only when every
event preserves that predicate. Otherwise a restriction may delete an escaping
execution and conceal its divergence.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProgressObservation

universe u v w

variable {V : Type u} [Quiver.{v} V] {Label : Type w}

def DomainClosed (domain : V → Prop) : Prop :=
  ∀ {a b : V}, domain a → (a ⟶ b) → domain b

abbrev restrictedQuiver (domain : V → Prop) : Quiver {state : V // domain state} :=
  ⟨fun a b => a.val ⟶ b.val⟩

def restrictedObservation (read : Observation V Label) (domain : V → Prop) :
    @Observation {state : V // domain state} (restrictedQuiver domain) Label :=
  fun event => read event

theorem execution_stays (domain : V → Prop) (closed : DomainClosed domain)
    (execution : Execution V) (initial : domain (execution.state 0)) (n : ℕ) :
    domain (execution.state n) := by
  induction n with
  | zero => exact initial
  | succ n ih => exact closed ih (execution.event n)

def restrictExecution (domain : V → Prop) (closed : DomainClosed domain)
    (execution : Execution V) (initial : domain (execution.state 0)) :
    @Execution {state : V // domain state} (restrictedQuiver domain) := by
  letI : Quiver {state : V // domain state} := restrictedQuiver domain
  exact { state := fun n => ⟨execution.state n, execution_stays domain closed execution initial n⟩
          event := fun n => execution.event n }

/-- Restricted productivity applies to the original run because domain closure is proved. -/
theorem progress_from_restriction (read : Observation V Label) (domain : V → Prop)
    (closed : DomainClosed domain)
    (progress : @NonZeno {state : V // domain state} (restrictedQuiver domain) Label
      (restrictedObservation read domain))
    (execution : Execution V) (initial : domain (execution.state 0)) (start : ℕ) :
    ∃ n, start ≤ n ∧ (read (execution.event n)).isSome = true :=
  progress (restrictExecution domain closed execution initial) start

end Mettapedia.Machines.ProgressObservation
