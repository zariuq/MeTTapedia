import Mettapedia.Machines.ErrorBoundaryContracts.AttemptIdentity

/-! A persisted reservation and a one-use local dispatch permit are different
objects. This model counts grants, not external effects. Its validity argument
is supplied by checking the current ledger owner, generation and active phase.
Restart invalidates old permits; it does not manufacture a fresh reservation. -/

namespace Mettapedia.Machines.ErrorBoundaryContracts.DispatchPermit

universe u v w
variable {α : Type u} {ε : Type v} {Id : Type w}

def claim (used valid : Bool) : Bool × Nat :=
  if valid && !used then (true, 1) else (used, 0)

def run : Bool → List Bool → Bool × Nat
  | used, [] => (used, 0)
  | used, valid :: rest =>
    let first := claim used valid
    let later := run first.1 rest
    (later.1, first.2 + later.2)

theorem claim_accounting (used valid : Bool) :
    (claim used valid).1.toNat = used.toNat + (claim used valid).2 := by
  cases used <;> cases valid <;> rfl

theorem run_accounting (used : Bool) (requests : List Bool) :
    (run used requests).1.toNat = used.toNat + (run used requests).2 := by
  induction requests generalizing used with
  | nil => simp [run]
  | cons valid rest ih =>
    simp only [run]
    rw [ih, claim_accounting]
    omega

theorem at_most_one_grant (requests : List Bool) : (run false requests).2 ≤ 1 := by
  have h := run_accounting false requests
  have bound : (run false requests).1.toNat ≤ 1 := by
    cases (run false requests).1 <;> decide
  simp only [Bool.toNat_false, Nat.zero_add] at h
  omega

theorem used_permit_never_grants (requests : List Bool) :
    (run true requests).2 = 0 := by
  have h := run_accounting true requests
  have bound : (run true requests).1.toNat ≤ 1 := by
    cases (run true requests).1 <;> decide
  simp only [Bool.toNat_true] at h
  omega

theorem rejected_request_keeps_permit (used : Bool) : claim used false = (used, 0) := by
  cases used <;> rfl

def ready (task : Supervision.Task α ε) : Bool :=
  match task.phase, task.remaining with
  | .ready, _ + 1 => true
  | _, _ => false

def nextReady : List (Id × Supervision.Task α ε) → Option Id
  | [] => none
  | (id, task) :: rest => if ready task then some id else nextReady rest

theorem nextReady_skips_unready (earlier rest : List (Id × Supervision.Task α ε))
    (h : ∀ entry ∈ earlier, ready entry.2 = false) :
    nextReady (earlier ++ rest) = nextReady rest := by
  induction earlier with
  | nil => rfl
  | cons entry tail ih =>
    simp only [List.cons_append, nextReady, h entry (by simp), Bool.false_eq_true,
      ↓reduceIte]
    exact ih (fun x hx => h x (by simp [hx]))

theorem uncertain_does_not_block_ready (first second : Id) (n : Nat) :
    nextReady [(first, (⟨n, .uncertain, false⟩ : Supervision.Task α ε)),
      (second, Supervision.initial (n + 1))] = some second := by
  simp [nextReady, ready, Supervision.initial]

example : run false [false, true, true, false, true] = (true, 1) := rfl
example : run true [true, true] = (true, 0) := rfl

end Mettapedia.Machines.ErrorBoundaryContracts.DispatchPermit
