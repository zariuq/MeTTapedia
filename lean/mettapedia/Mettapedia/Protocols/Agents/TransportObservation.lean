import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Conservative transport observations and independent deadlines

Transport failure is not synonymous with timeout. A safe application view can
discard URLs, headers and response bytes while retaining the native error code.
It may claim timeout only when that distinguished code was actually observed;
an unclassified failure is not evidence of a deadline.

The clock model separately describes total, first-body-byte and body-idle
limits. Zero disables a limit. Body progress changes the silence anchor, not
the request's execution-start anchor. Queue/admission latency is outside this
clock model. The hard bound is invariant under an arbitrary
progress trace. A status observation or soft attention wait cannot create a
new request identity.

These are mathematical interface contracts. They do not prove that a given
provider, proxy, socket or C implementation generated a particular failure.
In particular a native timeout code does not identify which clock expired.
The native code mapping and time representation require executable witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.TransportObservation

inductive FailureKind | timeout | transport | unknown
  deriving DecidableEq, Repr

structure FailureView (Code : Type) where
  code : Option Code
  kind : FailureKind
  deriving DecidableEq, Repr

variable {Code : Type} [DecidableEq Code]

/-- This is a projection of evidence already received, not a guess from elapsed
time or a failed model call. Sensitive source text is outside this interface. -/
def viewFailure (timeoutCode : Code) (observed : Option Code) : FailureView Code :=
  ⟨observed, match observed with
    | none => .unknown
    | some code => if code = timeoutCode then .timeout else .transport⟩

theorem failure_code_preserved (timeoutCode : Code) (observed : Option Code) :
    (viewFailure timeoutCode observed).code = observed := rfl

/-- The timeout label reflects positive native evidence in both directions. -/
theorem timeout_iff_native_timeout (timeoutCode : Code) (observed : Option Code) :
    (viewFailure timeoutCode observed).kind = .timeout ↔ observed = some timeoutCode := by
  cases observed with
  | none => simp [viewFailure]
  | some code =>
    by_cases h : code = timeoutCode <;> simp_all [viewFailure]

theorem failure_projection_injective (timeoutCode : Code) :
    Function.Injective (viewFailure timeoutCode) := by
  intro a b h
  exact congrArg FailureView.code h

/-- Collapsing every native failure to timeout cannot satisfy the reflection
contract as soon as a non-timeout code is possible. -/
theorem blanket_timeout_unsound (timeoutCode other : Code) (different : other ≠ timeoutCode) :
    (viewFailure timeoutCode (some other)).kind ≠ .timeout := by
  simp [viewFailure, different]

structure Limits where
  hard : Nat
  firstBody : Nat
  bodyIdle : Nat
  deriving DecidableEq, Repr

structure Clock where
  started : Nat
  lastBody : Option Nat
  deriving DecidableEq, Repr

def expired (duration anchor now : Nat) : Bool :=
  decide (0 < duration ∧ anchor + duration ≤ now)

def silenceExpired (limits : Limits) (clock : Clock) (now : Nat) : Bool :=
  match clock.lastBody with
  | none => expired limits.firstBody clock.started now
  | some last => expired limits.bodyIdle last now

def deadlineExpired (limits : Limits) (clock : Clock) (now : Nat) : Bool :=
  expired limits.hard clock.started now || silenceExpired limits clock now

def observeBody (clock : Clock) (sampleTime : Nat) : Clock :=
  { clock with lastBody := some sampleTime }

def observeBodies (clock : Clock) (arrivals : List Nat) : Clock :=
  arrivals.foldl observeBody clock

theorem progress_preserves_start (clock : Clock) (arrivals : List Nat) :
    (observeBodies clock arrivals).started = clock.started := by
  induction arrivals generalizing clock with
  | nil => rfl
  | cons sampleTime rest ih =>
    simpa [observeBodies, observeBody] using ih (observeBody clock sampleTime)

/-- No volume or timing of response-body progress can extend the hard bound. -/
theorem hard_bound_survives_progress (limits : Limits) (clock : Clock)
    (arrivals : List Nat) (now : Nat) (enabled : 0 < limits.hard)
    (due : clock.started + limits.hard ≤ now) :
    deadlineExpired limits (observeBodies clock arrivals) now = true := by
  simp [deadlineExpired, expired, progress_preserves_start, enabled, due]

theorem all_limits_disabled (clock : Clock) (now : Nat) :
    deadlineExpired ⟨0, 0, 0⟩ clock now = false := by
  cases h : clock.lastBody <;> simp [deadlineExpired, silenceExpired, expired, h]

/-- After the first body byte, the first-byte clock no longer decides silence. -/
theorem after_body_uses_idle (limits : Limits) (clock : Clock) (sampleTime now : Nat) :
    silenceExpired limits (observeBody clock sampleTime) now =
      expired limits.bodyIdle sampleTime now := rfl

/-- The subtraction-based C guard has this meaning under a monotone sample;
without `anchor ≤ now`, unsigned subtraction is not justified by this model. -/
theorem elapsed_guard_equivalent (duration anchor now : Nat) (monotone : anchor ≤ now) :
    expired duration anchor now = true ↔ 0 < duration ∧ duration ≤ now - anchor := by
  simp only [expired, decide_eq_true_eq]
  omega

structure Pending (Request : Type) where
  request : Request
  clock : Clock
  limits : Limits
  observedAt : Nat
  observationCount : Nat

/-- A soft attention interval observes the same owned operation. The function
does not model a timeout/cancellation, which are separate terminal outcomes. -/
def softObserve {Request : Type} (pending : Pending Request) (sampleTime : Nat) : Pending Request :=
  { pending with
    observedAt := max pending.observedAt sampleTime
    observationCount := pending.observationCount + 1 }

theorem soft_observations_preserve_request {Request : Type} (pending : Pending Request)
    (observations : List Nat) :
    (observations.foldl softObserve pending).request = pending.request := by
  induction observations generalizing pending with
  | nil => rfl
  | cons sampleTime rest ih => simpa [softObserve] using ih (softObserve pending sampleTime)

theorem soft_observations_counted {Request : Type} (pending : Pending Request)
    (observations : List Nat) :
    (observations.foldl softObserve pending).observationCount =
      pending.observationCount + observations.length := by
  induction observations generalizing pending with
  | nil => simp
  | cons sampleTime rest ih =>
    simpa [softObserve, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using ih (softObserve pending sampleTime)

#print axioms timeout_iff_native_timeout
#print axioms failure_projection_injective
#print axioms hard_bound_survives_progress
#print axioms elapsed_guard_equivalent

end Mettapedia.Protocols.Agents.TransportObservation
