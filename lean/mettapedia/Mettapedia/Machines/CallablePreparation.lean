import Mathlib.Tactic

/-!
# Retained signatures do not certify missing workers

After an exact callable signature is checked, the native cursor may retain
that metadata even if worker preparation returns no plan. The source caches
only prepared plans. The target additionally retains the checked arity, but
must ask preparation again when its worker is missing.

The input stream records successive preparation results, including temporary
refusals. The refinement preserves the complete worker/fallback selection
trace and consumption of preparation results. It does not prove body execution
or native pointer safety. Exact identity/arity matching and immutable signature
publication are separate laws in CallableArityCache; current execution
authority and owned return transfer retain their existing obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CallablePreparation

inductive Route where
  | fallback
  | worker (plan : Nat)
  deriving DecidableEq, Repr

structure Entry where
  arity : Nat
  prepared : Option Nat
  deriving DecidableEq, Repr

structure SourceStep where
  route : Route
  cached : Option Nat
  remaining : List (Option Nat)
  deriving DecidableEq, Repr

structure TargetStep where
  route : Route
  entry : Entry
  remaining : List (Option Nat)
  deriving DecidableEq, Repr

def source (cached : Option Nat) (attempts : List (Option Nat)) : SourceStep :=
  match cached with
  | some plan => ⟨.worker plan, cached, attempts⟩
  | none => match attempts with
    | [] => ⟨.fallback, none, []⟩
    | none :: rest => ⟨.fallback, none, rest⟩
    | some plan :: rest => ⟨.worker plan, some plan, rest⟩

def target (entry : Entry) (attempts : List (Option Nat)) : TargetStep :=
  match entry.prepared with
  | some plan => ⟨.worker plan, entry, attempts⟩
  | none => match attempts with
    | [] => ⟨.fallback, entry, []⟩
    | next :: rest =>
      let updated := { entry with prepared := next }
      match next with
      | none => ⟨.fallback, updated, rest⟩
      | some plan => ⟨.worker plan, updated, rest⟩

theorem step_refines (entry : Entry) (attempts : List (Option Nat)) :
    ((target entry attempts).route, (target entry attempts).entry.prepared,
      (target entry attempts).remaining) =
    ((source entry.prepared attempts).route, (source entry.prepared attempts).cached,
      (source entry.prepared attempts).remaining) := by
  rcases entry with ⟨arity, cached⟩
  cases cached with
  | some plan => rfl
  | none =>
      cases attempts with
      | nil => rfl
      | cons next rest => cases next <;> rfl

def sourceRun : Nat → Option Nat → List (Option Nat) → List Route
  | 0, _, _ => []
  | count + 1, cached, attempts =>
      let step := source cached attempts
      step.route :: sourceRun count step.cached step.remaining

def targetRun : Nat → Entry → List (Option Nat) → List Route
  | 0, _, _ => []
  | count + 1, entry, attempts =>
      let step := target entry attempts
      step.route :: targetRun count step.entry step.remaining

theorem trace_refines (count : Nat) (entry : Entry) (attempts : List (Option Nat)) :
    targetRun count entry attempts = sourceRun count entry.prepared attempts := by
  induction count generalizing entry attempts with
  | zero => rfl
  | succ count ih =>
      have same := step_refines entry attempts
      have route := congrArg (fun state => state.1) same
      have cached := congrArg (fun state => state.2.1) same
      have remaining := congrArg (fun state => state.2.2) same
      dsimp only at route cached remaining
      simp only [targetRun, sourceRun]
      rw [route, ih, cached, remaining]

theorem signature_survives (entry : Entry) (attempts : List (Option Nat)) :
    (target entry attempts).entry.arity = entry.arity := by
  rcases entry with ⟨arity, cached⟩
  cases cached with
  | some plan => rfl
  | none =>
      cases attempts with
      | nil => rfl
      | cons next rest => cases next <;> rfl

theorem prepared_plan_skips_preparation (arity plan : Nat) (attempts : List (Option Nat)) :
    target ⟨arity, some plan⟩ attempts = ⟨.worker plan, ⟨arity, some plan⟩, attempts⟩ := by
  rfl

theorem failed_preparation_remains_retryable (arity plan : Nat) :
    targetRun 2 ⟨arity, none⟩ [none, some plan] = [.fallback, .worker plan] := by
  rfl

theorem successful_preparation_is_reused (arity plan other : Nat) :
    targetRun 3 ⟨arity, none⟩ [none, some plan, some other] =
      [.fallback, .worker plan, .worker plan] := by
  rfl

/-- The old read of an already retained entry considered its missing plan
terminal, without consuming a later preparation opportunity. -/
def oldRetainedRoute (entry : Entry) : Route :=
  match entry.prepared with
  | none => .fallback
  | some plan => .worker plan

theorem missing_plan_is_not_a_refusal_certificate (arity plan : Nat) :
    oldRetainedRoute ⟨arity, none⟩ ≠ (target ⟨arity, none⟩ [some plan]).route := by
  simp [oldRetainedRoute, target]

end Mettapedia.Machines.CallablePreparation

#print axioms Mettapedia.Machines.CallablePreparation.step_refines
#print axioms Mettapedia.Machines.CallablePreparation.trace_refines
#print axioms Mettapedia.Machines.CallablePreparation.signature_survives
#print axioms Mettapedia.Machines.CallablePreparation.prepared_plan_skips_preparation
#print axioms Mettapedia.Machines.CallablePreparation.failed_preparation_remains_retryable
#print axioms Mettapedia.Machines.CallablePreparation.successful_preparation_is_reused
#print axioms Mettapedia.Machines.CallablePreparation.missing_plan_is_not_a_refusal_certificate
