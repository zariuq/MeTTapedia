/-!
# Stopping a coding session: settle by the recorded state, not by a report file

A coding session's worker records its ending in two writes: its report first,
then the state that says the run ended. `work-stop` stops the session's scope,
which can end the worker between those writes, and then settles the ending of
a run that can no longer record it.

The earlier stop settled only when no report file existed. A worker stopped
after its report and before its state therefore left the session recorded as
running with no worker (`report_guard_strands`): nothing would end that run
until a later reap happened to observe it.

The rule kept here settles by the recorded state alone: a run recorded as
running whose worker is gone is marked ended, and nothing else changes. It is
the settlement of the existing coding-session authority contract (mark only a
stale run). After a stop it always ends the recorded run (`stop_then_settle_ends`),
whatever the worker had written; it never marks a run whose worker is alive
(`settle_spares_live`); it is idempotent (`settle_idempotent`); and it keeps a
report the worker saved (`settle_keeps_report`), which the handover then
includes.

These are protocol-level statements about an abstract state, not a refinement
proof of the runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.CodingStopSettlement

structure Session where
  /-- The recorded state says the run is running. -/
  running : Bool
  /-- A report file exists. -/
  report : Bool
  /-- The run's worker is alive. -/
  alive : Bool
  deriving DecidableEq, Repr

inductive Step where
  /-- The worker writes its report (first of its two ending writes). -/
  | writeReport
  /-- The worker records the ending in its state (second write). -/
  | commit
  /-- The scope is stopped: the worker ends, wherever it was. -/
  | stop
  deriving DecidableEq, Repr

def step (s : Session) : Step → Session
  | .writeReport => if s.alive then { s with report := true } else s
  | .commit => if s.alive then { s with running := false } else s
  | .stop => { s with alive := false }

def run (s : Session) (steps : List Step) : Session := steps.foldl step s

/-- Settlement by the recorded state: a running run without a live worker ends. -/
def settle (s : Session) : Session :=
  if s.running && !s.alive then { s with running := false } else s

/-- The earlier stop: settle only when no report file exists. -/
def guardedSettle (s : Session) : Session :=
  if s.report then s else settle s

def started : Session := { running := true, report := false, alive := true }

/-- Stopped between its two ending writes, the guarded stop leaves the session
recorded as running with no worker. -/
theorem report_guard_strands :
    let s := guardedSettle (run started [.writeReport, .stop])
    s.running = true ∧ s.alive = false := by
  decide

/-- Settling after a stop always ends the recorded run. -/
theorem stop_then_settle_ends (s : Session) : (settle (step s .stop)).running = false := by
  cases s with
  | mk running report alive => cases running <;> simp [settle, step]

/-- Whatever the worker wrote before the stop, the stopped session is not left
recorded as running. -/
theorem stopped_session_ends (before : List Step) :
    (settle (run started (before ++ [.stop]))).running = false := by
  simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact stop_then_settle_ends _

/-- Settlement never marks a run whose worker is alive. -/
theorem settle_spares_live (s : Session) (h : s.alive = true) : settle s = s := by
  simp [settle, h]

theorem settle_idempotent (s : Session) : settle (settle s) = settle s := by
  cases s with
  | mk running report alive => cases running <;> cases alive <;> simp [settle]

/-- Settlement keeps the report the worker saved. -/
theorem settle_keeps_report (s : Session) : (settle s).report = s.report := by
  unfold settle; split <;> rfl

end Mettapedia.Protocols.Agents.CodingStopSettlement
