import Mettapedia.GSLT.Dynamics.CandidateLocalResolution

/-!+# Charged guards and candidate valuation

`where` is an eligibility test on an already identified candidate. A provider
may establish it, refute it, or retain a dependency on which it must wait.
Waiting is an operational outcome, not a third truth value. Rich derivation
evidence remains in the candidate; the proposition here licenses execution.

Guard checks and the authorized action have separate receipts. A rejected or
deferred check leaves the action's store untouched, but does not refund work
spent checking. Nothing in this interface requires a numerical semantic value,
ML scoring, or a particular location of scoring in an inference algorithm.

The hoisting theorem concerns a fixed pure guard and valuation. It proves exact
ordered occurrence equality and the saved valuation charges. It does not move
guards through mutations or through computations on which they depend.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.GuardedWork

open ContextualCandidateValuation

universe u v w x

inductive Decision (eligible : Prop) (Dependency : Type u) where
  | accept (evidence : eligible)
  | reject (refutation : ¬ eligible)
  | defer (dependency : Dependency)

inductive Result (Output : Type u) (Dependency : Type v) where
  | emitted (output : Output)
  | rejected
  | waiting (dependency : Dependency)
  deriving Repr, DecidableEq

/-- The probe has already run. Its receipt is retained on every path.
Dependency may include a context version, wakeup token, and retained work. -/
def attempt {eligible : Prop} {Dependency : Type u} {Store : Type v}
    {Output : Type w} {Cost : Type x} [Add Cost]
    (probe : Cost × Decision eligible Dependency)
    (action : eligible → Store → Cost × (Output × Store)) (store : Store) :
    Cost × (Result Output Dependency × Store) :=
  match probe.2 with
  | .accept proof =>
      let result := action proof store
      (probe.1 + result.1, (.emitted result.2.1, result.2.2))
  | .reject _ => (probe.1, (.rejected, store))
  | .defer dependency => (probe.1, (.waiting dependency, store))

@[simp] theorem attempt_defer {eligible : Prop} {Dependency : Type u}
    {Store : Type v} {Output : Type w} {Cost : Type x} [Add Cost]
    (spent : Cost) (dependency : Dependency)
    (action : eligible → Store → Cost × (Output × Store)) (store : Store) :
    attempt (spent, .defer dependency) action store =
      (spent, (.waiting dependency, store)) := rfl

@[simp] theorem attempt_reject {eligible : Prop} {Dependency : Type u}
    {Store : Type v} {Output : Type w} {Cost : Type x} [Add Cost]
    (spent : Cost) (no : ¬ eligible)
    (action : eligible → Store → Cost × (Output × Store)) (store : Store) :
    attempt (Dependency := Dependency) (spent, .reject no) action store =
      (spent, (.rejected, store)) := rfl

/-- Checking cannot consume an action's state unless it establishes eligibility. -/
theorem unchanged_unless_accepted {eligible : Prop} {Dependency : Type u}
    {Store : Type v} {Output : Type w} {Cost : Type x} [Add Cost]
    (probe : Cost × Decision eligible Dependency)
    (action : eligible → Store → Cost × (Output × Store)) (store : Store)
    (notAccepted : ∀ proof, probe.2 ≠ .accept proof) :
    (attempt probe action store).2.2 = store ∧
      (attempt probe action store).1 = probe.1 := by
  rcases probe with ⟨spent, decision⟩
  cases decision with
  | accept proof => exact (notAccepted proof rfl).elim
  | reject no => exact ⟨rfl, rfl⟩
  | defer dependency => exact ⟨rfl, rfl⟩

section PureValuation

variable {Candidate : Type u} {Value : Type v}

def valueThenGuard (guard : Candidate → Bool) (value : Candidate → Value)
    (candidates : List Candidate) : List (ValuedOccurrence Candidate Value) :=
  (attachValues value candidates).filter fun row => guard row.occurrence

def guardThenValue (guard : Candidate → Bool) (value : Candidate → Value)
    (candidates : List Candidate) : List (ValuedOccurrence Candidate Value) :=
  attachValues value (candidates.filter guard)

/-- No quotient is taken: equal candidates occurring twice remain two rows. -/
theorem hoist_guard (guard : Candidate → Bool) (value : Candidate → Value)
    (candidates : List Candidate) :
    valueThenGuard guard value candidates = guardThenValue guard value candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
      cases accepted : guard candidate <;>
        simpa [valueThenGuard, guardThenValue, attachValues, accepted] using ih

variable {Cost : Type w} [AddCommMonoid Cost]

def totalCharge (charge : Candidate → Cost) (candidates : List Candidate) : Cost :=
  (candidates.map charge).sum

def eagerCharge (guardCost valueCost : Candidate → Cost)
    (candidates : List Candidate) : Cost :=
  totalCharge guardCost candidates + totalCharge valueCost candidates

def guardedCharge (guard : Candidate → Bool) (guardCost valueCost : Candidate → Cost)
    (candidates : List Candidate) : Cost :=
  totalCharge guardCost candidates + totalCharge valueCost (candidates.filter guard)

def rejectedCharge (guard : Candidate → Bool) (valueCost : Candidate → Cost)
    (candidates : List Candidate) : Cost :=
  totalCharge valueCost (candidates.filter fun candidate => !(guard candidate))

theorem partition_charge (guard : Candidate → Bool) (charge : Candidate → Cost)
    (candidates : List Candidate) :
    totalCharge charge candidates =
      totalCharge charge (candidates.filter guard) + rejectedCharge guard charge candidates := by
  induction candidates with
  | nil => simp [totalCharge, rejectedCharge]
  | cons candidate rest ih =>
      cases accepted : guard candidate <;>
        simp_all [totalCharge, rejectedCharge] <;> abel

/-- Exact accounting, valid also for a vector of costs. Commutativity is about
the account, not permission to commute effectful computations. -/
theorem hoist_charge (guard : Candidate → Bool) (guardCost valueCost : Candidate → Cost)
    (candidates : List Candidate) :
    eagerCharge guardCost valueCost candidates =
      guardedCharge guard guardCost valueCost candidates +
        rejectedCharge guard valueCost candidates := by
  unfold eagerCharge guardedCharge
  rw [partition_charge guard valueCost candidates]
  exact (add_assoc _ _ _).symm

theorem hoist_nat_charge_le (guard : Candidate → Bool) (guardCost valueCost : Candidate → Nat)
    (candidates : List Candidate) :
    guardedCharge guard guardCost valueCost candidates ≤ eagerCharge guardCost valueCost candidates := by
  rw [hoist_charge]
  exact Nat.le_add_right _ _

end PureValuation

namespace Controls

/-- Scoring two identical retained occurrences still costs twice. -/
theorem duplicates_and_saved_scoring :
    (guardThenValue (fun n : Nat => n == 2) (fun n => n * 10) [1, 2, 2]).map
      ValuedOccurrence.value = [20, 20] ∧
    eagerCharge (fun _ : Nat => 1) (fun _ => 100) [1, 2, 2] = 303 ∧
    guardedCharge (fun n : Nat => n == 2) (fun _ => 1) (fun _ => 100) [1, 2, 2] = 203 := by
  decide

def action (_proof : 1 < 2) (state : Nat) : Nat × (Nat × Nat) :=
  (5, (state + 1, state + 1))

theorem waiting_retains_store_and_charge :
    attempt (3, Decision.defer (eligible := 1 < 2) "dependency") action 7 =
      (3, (.waiting "dependency", 7)) := rfl

theorem accepted_charges_probe_and_action :
    attempt (Dependency := String) (3, Decision.accept (by decide : 1 < 2)) action 7 =
      (8, (.emitted 8, 8)) := rfl

/-- Re-evaluating a guard against a different context changes eligibility. -/
theorem context_change_invalidates_hoisting :
    guardThenValue (fun n : Nat => n < 2) id [2] ≠
      guardThenValue (fun n : Nat => n < 3) id [2] := by decide

/-- The same retained dependency is not evidence that the guard is false. -/
theorem waiting_is_not_rejection :
    (Result.waiting "dependency" : Result Nat String) ≠ .rejected := by decide

end Controls

#print axioms unchanged_unless_accepted
#print axioms hoist_guard
#print axioms hoist_charge

end Mettapedia.GSLT.Dynamics.GuardedWork
