import Mettapedia.Hyperseed.Closure

/-!
# Hyperseed: OpenClaw Bridge

Minimal OpenClaw-facing surface for observation ingestion.

Defines `OpenClawObservation` as a tagged observation envelope and provides
`appendObservation` / `appendObservationTrace` helpers that extend the trace
and fold into WM state.

This is generic — it does not assume a concrete OpenClaw payload format yet.
-/

namespace Mettapedia.Hyperseed

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass

variable {Obs Source Time State Query : Type*}
variable [EvidenceType State] [WorldModel State Query]

/-- An OpenClaw observation is an observation envelope with source and time metadata. -/
abbrev OpenClawObservation (Obs Source Time : Type*) :=
  ObservationEnvelope Obs Source Time

/-- Append a single OpenClaw observation to a trace. -/
def appendObservation
    (trace : ObservationTrace (OpenClawObservation Obs Source Time))
    (obs : OpenClawObservation Obs Source Time) :
    ObservationTrace (OpenClawObservation Obs Source Time) :=
  trace ++ [obs]

/-- Append multiple OpenClaw observations to a trace. -/
def appendObservationTrace
    (trace new : ObservationTrace (OpenClawObservation Obs Source Time)) :
    ObservationTrace (OpenClawObservation Obs Source Time) :=
  trace ++ new

/-- Appending a single observation extends the trace state by one `ingest` step. -/
theorem traceState_appendObservation
    (k : HyperseedKernel (OpenClawObservation Obs Source Time) State Query)
    (trace : ObservationTrace (OpenClawObservation Obs Source Time))
    (obs : OpenClawObservation Obs Source Time)
    (s : State) :
    traceState k (appendObservation trace obs) s =
      k.ingest obs (traceState k trace s) := by
  simp [appendObservation, traceState_append]

/-- Appending a batch of observations composes trace-state folds. -/
theorem traceState_appendObservationTrace
    (k : HyperseedKernel (OpenClawObservation Obs Source Time) State Query)
    (trace new : ObservationTrace (OpenClawObservation Obs Source Time))
    (s : State) :
    traceState k (appendObservationTrace trace new) s =
      traceState k new (traceState k trace s) := by
  simp [appendObservationTrace, traceState_append]

end Mettapedia.Hyperseed
