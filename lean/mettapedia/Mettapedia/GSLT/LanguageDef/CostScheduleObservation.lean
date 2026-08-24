import Mettapedia.GSLT.Dynamics.IndexedExecutionObservation
import Mettapedia.GSLT.LanguageDef.CostOneOperationalAdequacy

/-!
# Observation disciplines on proof-relevant Cost schedules

The Cost operational boundary already supplies an indexed execution family:
an `OperationalSchedule` is a chronological path of authorized concurrent
waves.  This module observes that execution without replacing it.

Each event is one complete wave, including its exact endpoints, occurrence
receipt, and `ParallelCostStep` proof.  Work/span is then collected as a
declared value of that retained event history.  The resulting theorem chain
is directional:

```
proof-relevant schedule → wave events → WorkSpan container → readout
```

No converse is asserted.  In particular, equal WorkSpan values do not
construct schedules or parallel-separation evidence.
-/

namespace Mettapedia.GSLT.LanguageDef.CostScheduleObservation

open Mettapedia.Algebra
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.LanguageDef.CostOneOperationalAdequacy
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe uGround

/-- One existentially packaged operational wave.  Unlike a scalar wave cost,
this event retains exact source, target, receipt, and execution evidence. -/
abbrev WaveEvent (Ground : Type uGround) :=
  Σ source target : CostConfig Ground, OperationalStep Ground source target

namespace WaveEvent

/-- Exact funded-occurrence receipt retained by one observed wave. -/
def receipt {Ground : Type uGround} (event : WaveEvent Ground) :
    Multiset (SpendEvent Ground (CostName Ground)) :=
  event.2.2.1

/-- Work/span valuation of one already authorized nonempty wave. -/
def workSpan {Ground : Type uGround} (event : WaveEvent Ground) : WorkSpan :=
  ⟨event.receipt.card, 1⟩

end WaveEvent

namespace Schedule

/-- Retain every chronological wave of an operational schedule as one event. -/
def events {Ground : Type uGround} {source target : CostConfig Ground} :
    CostOneOperationalAdequacy.OperationalSchedule Ground source target →
      List (WaveEvent Ground)
  | .refl _ => []
  | .cons step tail => ⟨_, _, step⟩ :: events tail

@[simp] theorem events_nil {Ground : Type uGround}
    (config : CostConfig Ground) :
    events (CostOneOperationalAdequacy.OperationalSchedule.nil config) = [] :=
  rfl

@[simp] theorem events_cons {Ground : Type uGround}
    {source middle target : CostConfig Ground}
    (step : OperationalStep Ground source middle)
    (tail : CostOneOperationalAdequacy.OperationalSchedule Ground middle target) :
    events (.cons step tail) = ⟨source, middle, step⟩ :: events tail :=
  rfl

/-- Event extraction respects chronological schedule composition. -/
@[simp] theorem events_append {Ground : Type uGround}
    {source middle target : CostConfig Ground}
    (first : CostOneOperationalAdequacy.OperationalSchedule Ground source middle)
    (second : CostOneOperationalAdequacy.OperationalSchedule Ground middle target) :
    events (CostOneOperationalAdequacy.OperationalSchedule.append first second) =
      events first ++ events second := by
  induction first with
  | refl => rfl
  | cons step tail inductionHypothesis =>
      change
        events (.cons step
          (CostOneOperationalAdequacy.OperationalSchedule.append tail second)) =
          _
      simp only [events, List.cons_append]
      rw [inductionHypothesis]

/-- Fold the exact occurrence receipts of a wave-event history. -/
def eventReceipt {Ground : Type uGround} :
    List (WaveEvent Ground) → Multiset (SpendEvent Ground (CostName Ground))
  | [] => 0
  | head :: tail => head.receipt + eventReceipt tail

/-- Extracting wave events preserves the complete occurrence multiset. -/
@[simp] theorem eventReceipt_events {Ground : Type uGround}
    {source target : CostConfig Ground}
    (schedule : CostOneOperationalAdequacy.OperationalSchedule Ground source target) :
    eventReceipt (events schedule) =
      CostOneOperationalAdequacy.OperationalSchedule.receipt schedule := by
  induction schedule with
  | refl => rfl
  | cons step tail inductionHypothesis =>
      rcases step with ⟨receipt, stepProof⟩
      simp only [events, eventReceipt, WaveEvent.receipt,
        CostOneOperationalAdequacy.OperationalSchedule.receipt]
      rw [inductionHypothesis]

/-- Event extraction preserves the exact number of chronological waves. -/
@[simp] theorem events_length {Ground : Type uGround}
    {source target : CostConfig Ground}
    (schedule : CostOneOperationalAdequacy.OperationalSchedule Ground source target) :
    (events schedule).length =
      CostOneOperationalAdequacy.OperationalSchedule.waves schedule := by
  induction schedule with
  | refl => rfl
  | cons step tail inductionHypothesis =>
      simp only [events, List.length_cons,
        CostOneOperationalAdequacy.OperationalSchedule.waves]
      rw [inductionHypothesis]
      omega

/-- The WorkSpan observation discipline for complete operational waves. -/
def discipline (Ground : Type uGround) : ObservationDiscipline (WaveEvent Ground) :=
  WorkSpanObservation.discipline WaveEvent.workSpan

/-- Collecting the extracted wave history computes the schedule's existing
WorkSpan valuation exactly. -/
@[simp] theorem collect_events {Ground : Type uGround}
    {source target : CostConfig Ground}
    (schedule : CostOneOperationalAdequacy.OperationalSchedule Ground source target) :
    (discipline Ground).collection.collect (events schedule) =
      some (CostOneOperationalAdequacy.OperationalSchedule.workSpan schedule) := by
  induction schedule with
  | refl => rfl
  | cons step tail inductionHypothesis =>
      rcases step with ⟨receipt, stepProof⟩
      change
        (WorkSpanObservation.valuation WaveEvent.workSpan).historyGrade
            (⟨_, _, ⟨receipt, stepProof⟩⟩ :: events tail) =
          some (WorkSpan.sequential ⟨receipt.card, 1⟩
            (CostOneOperationalAdequacy.OperationalSchedule.workSpan tail))
      rw [IndexedEventValuation.Valuation.historyGrade_cons]
      change
        (some (⟨receipt.card, 1⟩ : WorkSpan)).bind (fun head =>
          ((discipline Ground).collection.collect (events tail)).bind
            (fun tailValue =>
              WorkSpanObservation.sequentialAlgebra.op head tailValue)) = _
      rw [inductionHypothesis]
      rfl

/-- Operational schedules form an exact indexed execution observation. -/
def observation (Ground : Type uGround) :
    IndexedExecutionObservation (discipline Ground) (CostConfig Ground)
      (CostOneOperationalAdequacy.OperationalSchedule Ground) where
  events := events
  container := CostOneOperationalAdequacy.OperationalSchedule.workSpan
  collects := collect_events

/-- Chronological schedule concatenation is observed by event-list
concatenation. -/
def chronological (Ground : Type uGround) :
    (observation Ground).Chronological where
  append := CostOneOperationalAdequacy.OperationalSchedule.append
  events_append := events_append

@[simp] theorem observed_value {Ground : Type uGround}
    {source target : CostConfig Ground}
    (schedule : CostOneOperationalAdequacy.OperationalSchedule Ground source target) :
    (observation Ground).value schedule =
      CostOneOperationalAdequacy.OperationalSchedule.workSpan schedule :=
  rfl

/-- The generic execution/container bridge recovers chronological WorkSpan
composition from the execution and collector laws. -/
theorem observed_append {Ground : Type uGround}
    {source middle target : CostConfig Ground}
    (first : CostOneOperationalAdequacy.OperationalSchedule Ground source middle)
    (second : CostOneOperationalAdequacy.OperationalSchedule Ground middle target) :
    WorkSpanObservation.sequentialAlgebra.op
        ((observation Ground).container first)
        ((observation Ground).container second) =
      some ((observation Ground).container
        (CostOneOperationalAdequacy.OperationalSchedule.append first second)) :=
  IndexedExecutionObservation.Chronological.container_append
    (observation Ground) (WorkSpanObservation.chronological WaveEvent.workSpan)
    (chronological Ground) first second

/-- An established indexed schedule crosses the observation boundary without
losing its WorkSpan value. -/
@[simp] theorem observed_ofIndexed {Ground : Type uGround}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : ParallelCostSchedule source receipt target count waves) :
    (observation Ground).value
        (CostOneOperationalAdequacy.OperationalSchedule.ofIndexed schedule) =
      schedule.workSpan := by
  rw [observed_value,
    CostOneOperationalAdequacy.OperationalSchedule.workSpan_ofIndexed]

/-- The same crossing preserves the exact occurrence receipt. -/
@[simp] theorem observed_receipt_ofIndexed {Ground : Type uGround}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : ParallelCostSchedule source receipt target count waves) :
    eventReceipt (events
      (CostOneOperationalAdequacy.OperationalSchedule.ofIndexed schedule)) =
        receipt := by
  rw [eventReceipt_events,
    CostOneOperationalAdequacy.OperationalSchedule.receipt_ofIndexed]

/-- The same crossing preserves the exact number of wave events. -/
@[simp] theorem observed_wave_count_ofIndexed {Ground : Type uGround}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : ParallelCostSchedule source receipt target count waves) :
    (events
      (CostOneOperationalAdequacy.OperationalSchedule.ofIndexed schedule)).length =
        waves := by
  rw [events_length,
    CostOneOperationalAdequacy.OperationalSchedule.waves_ofIndexed]

end Schedule

#print axioms Schedule.events_append
#print axioms Schedule.eventReceipt_events
#print axioms Schedule.collect_events
#print axioms Schedule.observed_append
#print axioms Schedule.observed_ofIndexed
#print axioms Schedule.observed_receipt_ofIndexed
#print axioms Schedule.observed_wave_count_ofIndexed

end Mettapedia.GSLT.LanguageDef.CostScheduleObservation
