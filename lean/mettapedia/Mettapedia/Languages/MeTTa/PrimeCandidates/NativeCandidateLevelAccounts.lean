import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCandidateCostInterface
import Mettapedia.GSLT.Distinction.LevelAccounts

/-!
# The candidate cost interface as level-indexed readings

The candidate's operational cost schedules (`NativeCandidateCostInterface`)
retain their exact chronological wave history, with funded-occurrence
receipts, and read `WorkSpan` from it.  In the vocabulary of
`GSLT.Distinction.LevelAccounts` the history is the reference reading and
`WorkSpan` a declared work-and-span reading:

* the work-and-span reading factors through the reference history
  (`workSpan_factors_through_reference`), and composes sequentially across a
  resumed schedule (`workSpan_resumed`);
* the reference history does not factor through it
  (`reference_not_from_workSpan`): two valid schedules of the same two funded
  occurrences, in opposite orders, have the same `WorkSpan` and different
  receipt histories.  Replaying one for the other is qualified for the
  `WorkSpan` reading and not for the reference reading.

The generic layer does not import this module.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCandidateLevelAccounts

open Mettapedia.Algebra
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
open Mettapedia.GSLT.LanguageDef.CostScheduleObservation
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCostLayerReceiptObservation
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeFibredScheduleObservation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe uGround

/-- An operational schedule from a fixed source, with its target. -/
abbrev ScheduleFrom (Ground : Type uGround) (source : CostConfig Ground) :=
  Σ target, OperationalSchedule Ground source target

variable {Ground : Type uGround} {source : CostConfig Ground}

/-- The reference reading: the exact chronological wave history. -/
def referenceReading (schedule : ScheduleFrom Ground source) : List (WaveEvent Ground) :=
  Schedule.events schedule.2

/-- The declared work-and-span reading. -/
def workSpanReading (schedule : ScheduleFrom Ground source) : WorkSpan :=
  schedule.2.workSpan

/-- **The work-and-span reading is read from the reference history.** -/
theorem workSpan_factors_through_reference :
    Factors (referenceReading (Ground := Ground) (source := source)) workSpanReading :=
  ⟨historyWorkSpan, fun schedule => historyWorkSpan_events schedule.2⟩

/-- **A resumed schedule's reading is the sequential composite** of its two
parts. -/
theorem workSpan_resumed {middle target : CostConfig Ground}
    (first : OperationalSchedule Ground source middle)
    (second : OperationalSchedule Ground middle target) :
    (first.append second).workSpan = WorkSpan.sequential first.workSpan second.workSpan :=
  OperationalSchedule.workSpan_append first second

open Examples in
/-- **The reference history is not read from `WorkSpan`**: two valid schedules
of the same funded occurrences in opposite orders. -/
def reference_not_from_workSpan :
    NonTrivialFiber (workSpanReading (source := NativeInteractionFibration.Examples.source))
      referenceReading where
  left := ⟨_, forwardSchedule⟩
  right := ⟨_, reverseSchedule⟩
  sameShadow := by
    have same := two_orders_same_workSpan
    change historyWorkSpan (Schedule.events forwardSchedule) =
      historyWorkSpan (Schedule.events reverseSchedule) at same
    rw [historyWorkSpan_events, historyWorkSpan_events] at same
    exact same
  differentValue := two_orders_distinct_histories

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCandidateLevelAccounts
