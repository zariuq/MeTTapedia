/-!
# A requested stop of the execution gateway is not a dispatch failure

A supervisor's stop reaches the gateway and its store worker alike. A store
call in flight then fails, and the dispatch thread records a failure. The
earlier gateway ended with an error whenever a failure was recorded, so a stop
that had been asked for was logged as a failed unit (`failure_alone_blames_stop`).

The rule kept here ends with an error only when a failure was recorded and no
stop was requested. A requested stop always ends cleanly
(`requested_stop_is_clean`); a failure with no request still ends with an error
(`unrequested_failure_is_an_error`); and the request is monotone: once made, no
later event of the run turns the ending into an error (`request_is_final`).
Ignoring failures altogether would hide a broken store (`always_clean_hides_failure`).

What was in flight is left to the durable store: the request's state is not
changed by the ending (`ending_keeps_in_flight`), and the next start settles
every request still recorded as running (`recover_settles_running`), a started
write as uncertain, never replayed.

These are protocol-level statements about an abstract state, not a refinement
proof of the runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.GatewayRequestedStop

/-- A request's recorded state in the durable store. -/
inductive Recorded where
  | queued
  | running
  | succeeded
  | failed
  | uncertain
  deriving DecidableEq, Repr

structure Gateway where
  /-- A supervisor or operator asked the gateway to stop. -/
  requested : Bool
  /-- The dispatch thread recorded a failure. -/
  failure : Bool
  /-- The request in flight, as the store records it. -/
  inFlight : Recorded
  deriving DecidableEq, Repr

inductive Event where
  /-- The stop signal arrives. -/
  | stop
  /-- A store call fails (its worker is gone). -/
  | storeFails
  /-- The dispatch thread records the request's ending in the store. -/
  | record (state : Recorded)
  deriving DecidableEq, Repr

def step (g : Gateway) : Event → Gateway
  | .stop => { g with requested := true }
  | .storeFails => { g with failure := true }
  | .record state => if g.failure then g else { g with inFlight := state }

def run (g : Gateway) (events : List Event) : Gateway := events.foldl step g

/-- The gateway's ending: an error only for a failure nobody asked to stop for. -/
def endsWithError (g : Gateway) : Bool := g.failure && !g.requested

/-- The earlier ending: any recorded failure is an error. -/
def failureAlone (g : Gateway) : Bool := g.failure

/-- An ending that never reports. -/
def alwaysClean (_ : Gateway) : Bool := false

def serving : Gateway := { requested := false, failure := false, inFlight := .running }

theorem requested_stop_is_clean (g : Gateway) (h : g.requested = true) :
    endsWithError g = false := by
  simp [endsWithError, h]

theorem unrequested_failure_is_an_error (g : Gateway)
    (hf : g.failure = true) (hr : g.requested = false) : endsWithError g = true := by
  simp [endsWithError, hf, hr]

theorem step_keeps_request (g : Gateway) (e : Event) (h : g.requested = true) :
    (step g e).requested = true := by
  cases e with
  | stop => rfl
  | storeFails => exact h
  | record state =>
      simp only [step]
      split <;> exact h

/-- Once a stop was requested, nothing later makes the ending an error. -/
theorem request_is_final (g : Gateway) (events : List Event) (h : g.requested = true) :
    endsWithError (run g events) = false := by
  induction events generalizing g with
  | nil => exact requested_stop_is_clean g h
  | cons e rest ih => exact ih (step g e) (step_keeps_request g e h)

/-- The stop that reached the store worker first: the earlier ending calls it
an error, the kept one does not. -/
theorem failure_alone_blames_stop :
    let g := run serving [.stop, .storeFails]
    failureAlone g = true ∧ endsWithError g = false := by
  decide

/-- The same store failure with no stop requested is an error under the kept
rule, and would pass unseen under an ending that never reports. -/
theorem always_clean_hides_failure :
    let g := run serving [.storeFails]
    endsWithError g = true ∧ alwaysClean g = false := by
  decide

/-- The ending decides the exit status only: a request whose recording failed
stays as the store has it. -/
theorem ending_keeps_in_flight :
    (run serving [.stop, .storeFails, .record .uncertain]).inFlight = .running := by
  decide

/-- The next start's recovery: a request still recorded as running did not
record its ending. A started write is uncertain and is not run again; a read
failed. Every other record stands. -/
def recover (write : Bool) : Recorded → Recorded
  | .running => if write then .uncertain else .failed
  | other => other

theorem recover_settles_running (write : Bool) (r : Recorded) :
    recover write r ≠ .running := by
  cases r <;> cases write <;> decide

theorem recover_keeps_settled (write : Bool) (r : Recorded) (h : r ≠ .running) :
    recover write r = r := by
  cases r <;> first | rfl | exact absurd rfl h

end Mettapedia.Protocols.Agents.GatewayRequestedStop
