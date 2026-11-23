/-!
# Stream EOF does not authorize awaiting process completion

This models one owned child. Stream events, process-exit evidence and clock
observations are separate transitions. In particular, closing both streams
does not manufacture a process-exit observation. A synchronous await is admitted
only after an exit has been observed, and only after draining or an interruption.

The earlier EOF-based gate can admit a blocking await before an exit event. A
native runtime reproduction demonstrates the resulting deadline failure; this
model establishes the missing protocol premise, not a C refinement theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.GatewayStreamCompletion

inductive Child where
  | running
  | exited (code : Int)
  deriving DecidableEq, Repr

inductive Reason where
  | deadline
  | cancelled
  | stopped
  deriving DecidableEq, Repr

structure State where
  child : Child := .running
  stdoutEOF : Bool := false
  stderrEOF : Bool := false
  deadline : Nat := 2
  reason : Option Reason := none
  deriving DecidableEq, Repr

inductive Event where
  | stdoutEOF
  | stderrEOF
  | childExit (code : Int)
  | clock (now : Nat)
  | cancel
  | stop
  deriving DecidableEq, Repr

def interrupt (s : State) (why : Reason) : State :=
  { s with reason := s.reason.or (some why) }

def step (s : State) : Event → State
  | .stdoutEOF => { s with stdoutEOF := true }
  | .stderrEOF => { s with stderrEOF := true }
  | .childExit code => { s with child := .exited code }
  | .clock now => if s.deadline ≤ now then interrupt s .deadline else s
  | .cancel => interrupt s .cancelled
  | .stop => interrupt s .stopped

def run (s : State) (events : List Event) : State := events.foldl step s

def isExit : Event → Bool
  | .childExit _ => true
  | _ => false

def terminated (s : State) : Bool :=
  match s.child with
  | .running => false
  | .exited _ => true

def oldMayAwait (s : State) : Bool :=
  (s.stdoutEOF && s.stderrEOF) || (s.reason.isSome && terminated s)

def mayAwait (s : State) : Bool :=
  terminated s && ((s.stdoutEOF && s.stderrEOF) || s.reason.isSome)

theorem step_without_exit_keeps_running (s : State) (e : Event)
    (running : s.child = .running) (noExit : isExit e = false) :
    (step s e).child = .running := by
  cases e <;> simp_all [step, isExit, interrupt]
  split <;> simp_all

theorem trace_without_exit_keeps_running (s : State) (events : List Event)
    (running : s.child = .running) (noExit : ∀ e ∈ events, isExit e = false) :
    (run s events).child = .running := by
  induction events generalizing s with
  | nil => exact running
  | cons e es ih =>
      apply ih (step s e)
      · exact step_without_exit_keeps_running s e running (noExit e (by simp))
      · intro x hx
        exact noExit x (by simp [hx])

theorem cannot_await_without_exit_evidence (s : State) (events : List Event)
    (running : s.child = .running) (noExit : ∀ e ∈ events, isExit e = false) :
    mayAwait (run s events) = false := by
  simp [mayAwait, terminated, trace_without_exit_keeps_running s events running noExit]

theorem old_gate_can_await_a_live_child :
    let closed := run {} [.stdoutEOF, .stderrEOF]
    closed.child = .running ∧ oldMayAwait closed = true ∧ mayAwait closed = false := by
  decide

theorem deadline_is_observed_while_streams_are_closed :
    let waiting := run {} [.stdoutEOF, .stderrEOF, .clock 3]
    waiting.child = .running ∧ waiting.reason = some .deadline ∧ mayAwait waiting = false := by
  decide

theorem first_interruption_is_preserved (s : State) (before after : Reason)
    (h : s.reason = some before) : (interrupt s after).reason = some before := by
  simp [interrupt, h, Option.or]

inductive Settlement where
  | pending
  | succeeded
  | failed
  | cancelled
  | uncertain
  deriving DecidableEq, Repr

def settlement (write : Bool) (s : State) : Settlement :=
  if !mayAwait s then .pending
  else if s.reason.isSome then
    (if write then .uncertain else if s.reason = some .cancelled then .cancelled else .failed)
  else match s.child with
    | .exited 0 => .succeeded
    | _ => if write then .uncertain else .failed

theorem late_successful_exit_cannot_erase_deadline :
    let stopped := run {} [.stdoutEOF, .stderrEOF, .clock 3, .childExit 0]
    settlement false stopped = .failed ∧ settlement true stopped = .uncertain := by
  decide

theorem cancellation_keeps_write_uncertainty :
    let stopped := run {} [.stdoutEOF, .stderrEOF, .cancel, .childExit (-15)]
    settlement false stopped = .cancelled ∧ settlement true stopped = .uncertain := by
  decide

end Mettapedia.Protocols.Agents.GatewayStreamCompletion
