import Mettapedia.GSLT.Dynamics.ProofRelevantNeed
import Mettapedia.GSLT.Causality.TraceCostValuation

/-!
# What demand costs

`ProofRelevantNeed` fixes the call-by-need cell protocol: origin inspection,
first evaluation, cached observation, stable and retryable faults, and
resampling, each an occurrence with its own identity. It already *counts*
those events. This module connects the counts to the trace-cost framework,
so demand is accounted in the same currency as every other occurrence.

* `toOccurrencePath` — a protocol trace is an occurrence path of the
  protocol's own interaction presentation, event for event.
* `evaluationWork_onPath` — charging each occurrence by `evaluationCount`, as
  a **site** cost, reproduces the protocol's `Trace.evaluationCount` exactly.
  So evaluation work is a trace invariant under every independence relation
  (`evaluationWork_descends`), not a schedule observation.
* `cached_observation_costs_no_work` — repeated observation of a completed
  cell is charged no evaluation work, whatever the trace.

Concrete controls on a one-cell run separate the channels:

* `force_then_observe_twice` — one evaluation, two observations;
* `retry_is_charged_twice` — a retryable fault reopens the cell and the second
  evaluation is charged again: work performed before the fault is not erased;
* `resample_is_fresh_work` — resampling allocates a distinct cell whose
  evaluation is new work, unlike observing a cached one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.NeedCostAccounting

open Mettapedia.GSLT
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.Mazurkiewicz
open Mettapedia.GSLT.Causality.TraceCostValuation
open Mettapedia.GSLT.Dynamics.ProofRelevantNeed

universe uCell uOrigin uValue uStableFault uRetryableFault

variable {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
  {StableFault : Type uStableFault} {RetryableFault : Type uRetryableFault}

/-- A protocol trace, read as an occurrence path. -/
def toOccurrencePath {cell : Cell} :
    {source target : CellState Origin Value StableFault} →
    ProofRelevantNeed.Trace RetryableFault cell source target →
    OccurrencePath (interactionPresentation (Origin := Origin) (Value := Value)
      (StableFault := StableFault) RetryableFault cell) source target
  | _, _, .refl state => OccurrencePath.refl (P := interactionPresentation (Origin := Origin)
      (Value := Value) (StableFault := StableFault) RetryableFault cell) state
  | _, _, .tail event step rest => .cons ⟨event, step⟩ (toOccurrencePath rest)

/-- Evaluation work, charged by the event kind alone. -/
def evaluationWork (cell : Cell) :
    OccurrenceValuation (interactionPresentation (Origin := Origin) (Value := Value)
      (StableFault := StableFault) RetryableFault cell) ℕ :=
  siteCostValuation _ Event.evaluationCount

/-- **The site cost is the protocol's own count.** -/
theorem evaluationWork_onPath {cell : Cell}
    {source target : CellState Origin Value StableFault}
    (trace : ProofRelevantNeed.Trace RetryableFault cell source target) :
    (evaluationWork (RetryableFault := RetryableFault) cell).onPath
      (toOccurrencePath trace) = trace.evaluationCount := by
  induction trace with
  | refl _ => rfl
  | tail event step rest ih =>
      simp only [toOccurrencePath, OccurrenceValuation.onPath, ih,
        ProofRelevantNeed.Trace.evaluationCount]
      rfl

/-- **Evaluation work is a trace invariant**, for every independence relation
on protocol events. -/
theorem evaluationWork_descends (cell : Cell)
    (indep : SiteIndependence (interactionPresentation (Origin := Origin)
      (Value := Value) (StableFault := StableFault) RetryableFault cell)) :
    Descends indep (evaluationWork (RetryableFault := RetryableFault) cell) :=
  siteCostValuation_descends indep _

/-- **Repeated observation of a completed cell costs no evaluation work.** -/
theorem cached_observation_costs_no_work {cell : Cell} {origin : Origin}
    {value : Value} {target : CellState Origin Value StableFault}
    (trace : ProofRelevantNeed.Trace RetryableFault cell (.cachedValue origin value) target) :
    (evaluationWork (RetryableFault := RetryableFault) cell).onPath
      (toOccurrencePath trace) = 0 := by
  rw [evaluationWork_onPath, ProofRelevantNeed.Trace.from_cachedValue_no_evaluation]

/-! ## Controls on one cell -/

namespace NeedCostControls

/-- Allocate, evaluate, commit `7`, then observe twice. -/
def forceThenObserveTwice :
    ProofRelevantNeed.Trace (Cell := Unit) (Origin := Unit) (Value := ℕ) (StableFault := Empty)
      Empty () .absent (.cachedValue () 7) :=
  .tail _ (.allocate ()) <| .tail _ (.beginEvaluation ()) <|
    .tail _ (.commitValue () 7) <| .tail _ (.observeValue () 7) <|
      .tail _ (.observeValue () 7) <| .refl _

/-- **One evaluation, two observations**: sharing charges the work once. -/
theorem force_then_observe_twice :
    forceThenObserveTwice.evaluationCount = 1 ∧
      forceThenObserveTwice.outcomeObservationCount = 2 := by
  constructor <;> rfl

/-- Evaluate, hit a retryable fault, evaluate again, commit. -/
def retryThenCommit :
    ProofRelevantNeed.Trace (Cell := Unit) (Origin := Unit) (Value := ℕ) (StableFault := Empty)
      Unit () .absent (.cachedValue () 7) :=
  .tail _ (.allocate ()) <| .tail _ (.beginEvaluation ()) <|
    .tail _ (.retry () ()) <| .tail _ (.beginEvaluation ()) <|
      .tail _ (.commitValue () 7) <| .refl _

/-- **A retried evaluation is charged twice**: the fault reopens the cell, and
the work done before it is not erased by the rollback. -/
theorem retry_is_charged_twice : retryThenCommit.evaluationCount = 2 := rfl

/-- Resample from cell `0` into a fresh cell `1`, then evaluate it. -/
def resampleThenEvaluate :
    ProofRelevantNeed.Trace (Cell := Bool) (Origin := Unit) (Value := ℕ) (StableFault := Empty)
      Empty true .absent (.evaluating ()) :=
  .tail _ (.resample false () (by decide)) <| .tail _ (.beginEvaluation ()) <| .refl _

/-- **Resampling is fresh work**, unlike observing a cached cell. -/
theorem resample_is_fresh_work : resampleThenEvaluate.evaluationCount = 1 := rfl

end NeedCostControls

end Mettapedia.GSLT.Dynamics.NeedCostAccounting

#print axioms Mettapedia.GSLT.Dynamics.NeedCostAccounting.evaluationWork_onPath
#print axioms Mettapedia.GSLT.Dynamics.NeedCostAccounting.cached_observation_costs_no_work
