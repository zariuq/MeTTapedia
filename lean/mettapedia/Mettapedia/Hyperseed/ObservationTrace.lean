import Mettapedia.Hyperseed.Basic

/-!
# Hyperseed: Observation Traces

Defines observation traces as lists of observations and the trace-state fold
that accumulates observations into a WM state via the kernel's `ingest` function.

This is the basic "OpenClaw keeps exploring and appending observations" layer.
-/

namespace Mettapedia.Hyperseed

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass

variable {Obs State Query : Type*}
variable [EvidenceType State] [WorldModel State Query]

/-- An observation trace is a list of observations. -/
abbrev ObservationTrace (Obs : Type*) := List Obs

/-- Fold an observation trace into the WM state by repeatedly applying `ingest`. -/
def traceState (k : HyperseedKernel Obs State Query) :
    ObservationTrace Obs → State → State
  | [], s => s
  | o :: os, s => traceState k os (k.ingest o s)

@[simp]
theorem traceState_nil (k : HyperseedKernel Obs State Query) (s : State) :
    traceState k [] s = s := rfl

@[simp]
theorem traceState_cons (k : HyperseedKernel Obs State Query)
    (o : Obs) (os : ObservationTrace Obs) (s : State) :
    traceState k (o :: os) s = traceState k os (k.ingest o s) := rfl

theorem traceState_append (k : HyperseedKernel Obs State Query)
    (t₁ t₂ : ObservationTrace Obs) (s : State) :
    traceState k (t₁ ++ t₂) s = traceState k t₂ (traceState k t₁ s) := by
  induction t₁ generalizing s with
  | nil => simp
  | cons o os ih => simp [ih]

end Mettapedia.Hyperseed
