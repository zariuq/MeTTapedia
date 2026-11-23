import Mettapedia.Protocols.Agents.RejectionGateFastPath
import Mettapedia.Protocols.Agents.TurnHealth

/-!
# The loop's retry wait, decided on the rejection gate's fast path

After a failed turn the loop waits before its next model call. The wait is
a pure function of the health record's `retry_at`, the time, and the host's
hold on a retained rejection:

* a context repair pending: 0, so the loop goes on to the repair;
* a block waiting for corrective input: 1, so the bounded wait keeps polling;
* a hold the host could not decide: 1, the block is kept;
* otherwise the backoff left until `retry_at`, rounded up.

The host is asked only when a block is possible: the record holds one, or
the process latched a rejection (`RejectionGateFastPath.consults`).

Invariants proved here:

* on every reachable state the native wait is the wait Python's
  `retry_wait_seconds` gives, which asks the host every time;
* a block the host cannot decide never grants a retry;
* the loop never retries before the time the failure's pacing set
  (`TurnHealth.pace`), and the backoff only counts down.

The counterexample is a wait that takes an undecided host for a clear one:
a retained block, whose record holds no backoff, is retried at once.

This is an abstract contract, not a refinement proof of
`src/rejection_gate_cetta.metta`, `provider_rejection` or `cognitive_health`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.LoopRetryWait

open RejectionGateFastPath

/-- The host's hold on the wait, as `native_llm_host.rejection_hold` names it;
`none` when the host was not asked. -/
inductive Hold where
  | none | clear | repair | blocked | undecided
  deriving DecidableEq

/-- `gate:wait`: the record's `retry_at`, the time, the hold. -/
def wait (retryAt now : ℚ) : Hold → ℕ
  | .repair => 0
  | .blocked => 1
  | .undecided => 1
  | .none => ⌈retryAt - now⌉₊
  | .clear => ⌈retryAt - now⌉₊

/-- The host's decision on a state it is asked about. -/
def hostHold (s : State) (repair : Bool) : Hold :=
  if hostBlocks s then (if repair then .repair else .blocked) else .clear

/-- `gate:retry-wait`: the host is asked only on a possible block, and may
fail to answer. -/
def nativeWait (s : State) (repair answers : Bool) (retryAt now : ℚ) : ℕ :=
  if consults s then wait retryAt now (if answers then hostHold s repair else .undecided)
  else wait retryAt now .none

/-- `cognitive_health.retry_wait_seconds`: it asks the host every time. -/
def pythonWait (s : State) (repair : Bool) (retryAt now : ℚ) : ℕ :=
  if hostBlocks s then (if repair then 0 else 1) else ⌈retryAt - now⌉₊

/-- Where the host answers, the native wait is Python's on every state
satisfying the fast path's invariant. -/
theorem native_is_python {s : State} (h : Invariant s) (repair : Bool) (retryAt now : ℚ) :
    nativeWait s repair true retryAt now = pythonWait s repair retryAt now := by
  unfold nativeWait pythonWait
  by_cases hc : consults s
  · simp only [hc, if_true]
    unfold hostHold
    by_cases hb : hostBlocks s <;> cases repair <;> simp [hb, wait]
  · have fast : RejectionGateFastPath.decide s = .fast := by simp [RejectionGateFastPath.decide, hc]
    have hb := fast_path_sound h fast
    simp [hc, hb, wait]

/-- On every reachable state of the gate. -/
theorem reachable_native_is_python (es : List Event) (repair : Bool) (retryAt now : ℚ) :
    nativeWait (run initial es) repair true retryAt now = pythonWait (run initial es) repair retryAt now :=
  native_is_python (run_invariant es) repair retryAt now

/-- A possible block the host cannot decide never grants a retry. -/
theorem undecided_holds {s : State} (repair : Bool) (retryAt now : ℚ) (hc : consults s = true) :
    nativeWait s repair false retryAt now = 1 := by
  simp [nativeWait, hc, wait]

/-- A held block, no repair pending: the loop polls each second. -/
theorem held_block_polls {s : State} (retryAt now : ℚ) (hc : consults s = true) (hb : hostBlocks s = true) :
    nativeWait s false true retryAt now = 1 := by
  simp [nativeWait, hc, hostHold, hb, wait]

/-- Without a hold, the wait covers the backoff: the next call is not before
`retry_at`. -/
theorem covers_backoff (retryAt now : ℚ) : retryAt ≤ now + (wait retryAt now .none : ℚ) := by
  have := Nat.le_ceil (retryAt - now)
  simp only [wait]
  linarith

/-- The backoff only counts down. -/
theorem counts_down (retryAt now later : ℚ) (h : now ≤ later) :
    wait retryAt later .none ≤ wait retryAt now .none := by
  simp only [wait]
  exact Nat.ceil_mono (by linarith)

/-- A failed turn paced at time `t` (`TurnHealth.pace`) records
`retry_at = t + wait`; at `t` the loop waits at least that long. -/
theorem honours_the_pace (base cap : ℚ) (streak : ℕ) (f : TurnHealth.Facts) (t : ℚ) :
    (TurnHealth.pace base cap streak f).1 ≤ (wait (t + (TurnHealth.pace base cap streak f).1) t .none : ℚ) := by
  have := covers_backoff (t + (TurnHealth.pace base cap streak f).1) t
  linarith

/-- The rejected design: an undecided host taken for a clear one. -/
def waitUndecidedClear (s : State) (repair answers : Bool) (retryAt now : ℚ) : ℕ :=
  if consults s then wait retryAt now (if answers then hostHold s repair else .clear)
  else wait retryAt now .none

/-- A retained rejection clears the record's backoff (`retry_at = 0`); with
the host unreachable, that design retries it at once. -/
theorem undecided_clear_retries_a_block :
    let s := step initial (.reject true)
    hostBlocks s = true ∧ waitUndecidedClear s false false 0 100 = 0 ∧ nativeWait s false false 0 100 = 1 := by
  simp [step, initial, hostBlocks, waitUndecidedClear, nativeWait, consults, wait]

end Mettapedia.Protocols.Agents.LoopRetryWait
