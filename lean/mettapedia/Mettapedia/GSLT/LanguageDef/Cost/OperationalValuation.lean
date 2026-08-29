import Mettapedia.GSLT.Core.ControlInfluenceSeparation
import Mettapedia.GSLT.LanguageDef.CostScheduleObservation

/-!
# Declared valuations of proof-relevant Cost execution

The operational Cost layer retains more than a scalar account: an execution is
an endpoint-indexed chronological path of funded waves, and every wave retains
its exact occurrence receipt and execution proof.  This module makes arbitrary
declared valuations maps out of that retained history.

The direction is deliberate:

```text
proof-relevant schedule -> exact wave history -> declared grade/value
```

Valuations compose because schedule histories compose.  Independent
valuations combine by product without identifying their carriers.  Work/span
is one such declared valuation, not the execution, receipt, semantic value, or
truth of the underlying language.

Candidate-local grades are conservative annotations under ordinary occurrence
bag observation.  If an authored language instead interprets a grade as a
semantic filter, that change is explicit and agrees with the existing semantic
filter operation.  Thus control advice does not silently acquire denotational
authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation

open Mettapedia.Algebra
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ControlInfluenceSeparation
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
open Mettapedia.GSLT.LanguageDef.CostScheduleObservation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe uGround uGrade uOtherGrade

/-- A declared valuation of complete proof-relevant Cost wave occurrences. -/
abbrev DeclaredValuation (Ground : Type uGround) :=
  IndexedEventValuation.Valuation (WaveEvent Ground)

/-- Evaluate a declared valuation on the exact chronological history of one
endpoint-indexed operational schedule. -/
def scheduleGrade {Ground : Type uGround}
    (valuation : DeclaredValuation.{uGround, uGrade} Ground)
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    Option valuation.Grade :=
  valuation.historyGrade (Schedule.events schedule)

/-- Declared valuation respects chronological schedule composition. -/
theorem scheduleGrade_append {Ground : Type uGround}
    (valuation : DeclaredValuation.{uGround, uGrade} Ground)
    {source middle target : CostConfig Ground}
    (first : OperationalSchedule Ground source middle)
    (second : OperationalSchedule Ground middle target) :
    scheduleGrade valuation (first.append second) =
      (scheduleGrade valuation first).bind fun left =>
        (scheduleGrade valuation second).bind fun right =>
          valuation.algebra.op left right := by
  unfold scheduleGrade
  rw [Schedule.events_append,
    IndexedEventValuation.Valuation.historyGrade_append]

/-- Work/span is the canonical sequential valuation of already authorized
waves.  It remains a declaration over the exact event history. -/
abbrev workSpanValuation (Ground : Type uGround) :
    DeclaredValuation.{uGround, 0} Ground :=
  WorkSpanObservation.valuation WaveEvent.workSpan

/-- The declared WorkSpan fold agrees exactly with the operational schedule's
existing WorkSpan observation. -/
@[simp] theorem scheduleGrade_workSpan {Ground : Type uGround}
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    scheduleGrade (workSpanValuation Ground) schedule =
      some schedule.workSpan := by
  exact Schedule.collect_events schedule

/-- Exact chronology is itself a total valuation.  It retains each wave,
including endpoints, occurrence receipt, and operational proof. -/
def chronologyValuation (Ground : Type uGround) :
    DeclaredValuation.{uGround, uGround} Ground where
  Grade := List (WaveEvent Ground)
  algebra := chronologicalListPartialMonoid (WaveEvent Ground)
  grade := fun event => some [event]

/-- Folding the chronological valuation returns the exact input history. -/
@[simp] theorem chronology_historyGrade {Ground : Type uGround}
    (events : List (WaveEvent Ground)) :
    (chronologyValuation Ground).historyGrade events = some events := by
  induction events with
  | nil => rfl
  | cons event events inductionHypothesis =>
      simp only [IndexedEventValuation.Valuation.historyGrade_cons]
      change
        (some [event]).bind (fun head : List (WaveEvent Ground) =>
          ((chronologyValuation Ground).historyGrade events).bind
            fun tail : List (WaveEvent Ground) => some (head ++ tail)) =
          some (event :: events)
      rw [inductionHypothesis]
      rfl

/-- Exact chronological valuation of a schedule recovers its complete wave
history, rather than merely its scalar or vector readout. -/
@[simp] theorem scheduleGrade_chronology {Ground : Type uGround}
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    scheduleGrade (chronologyValuation Ground) schedule =
      some (Schedule.events schedule) :=
  chronology_historyGrade (Schedule.events schedule)

/-- Pair WorkSpan with any independently declared valuation.  Product
acceptance is componentwise, so failure on either axis remains visible. -/
def withWorkSpan {Ground : Type uGround}
    (valuation : DeclaredValuation.{uGround, uGrade} Ground) :
    DeclaredValuation Ground where
  Grade := WorkSpan × valuation.Grade
  algebra := (workSpanValuation Ground).algebra.prod valuation.algebra
  grade := fun event =>
    ((workSpanValuation Ground).grade event).bind fun workSpan =>
      (valuation.grade event).bind fun grade => some (workSpan, grade)

/-- The product valuation computes WorkSpan and the additional declared axis
without converting either into the other. -/
theorem scheduleGrade_withWorkSpan {Ground : Type uGround}
    (valuation : DeclaredValuation.{uGround, uGrade} Ground)
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    scheduleGrade (withWorkSpan valuation) schedule =
      (scheduleGrade valuation schedule).bind fun grade =>
        some (schedule.workSpan, grade) := by
  have productGrade :=
    IndexedEventValuation.Valuation.prod_historyGrade
      (workSpanValuation Ground) valuation (Schedule.events schedule)
  change
    scheduleGrade (withWorkSpan valuation) schedule =
      (scheduleGrade valuation schedule).bind fun grade =>
        some (schedule.workSpan, grade)
  change
    (withWorkSpan valuation).historyGrade (Schedule.events schedule) = _
  rw [show
    (withWorkSpan valuation).historyGrade (Schedule.events schedule) =
      ((workSpanValuation Ground).historyGrade
          (Schedule.events schedule)).bind fun workSpan =>
        (valuation.historyGrade (Schedule.events schedule)).bind fun grade =>
          some (workSpan, grade) by
      simpa [withWorkSpan, workSpanValuation,
        WorkSpanObservation.valuation,
        IndexedEventValuation.Valuation.prod] using productGrade]
  have workSpanEquation := scheduleGrade_workSpan schedule
  change
    (workSpanValuation Ground).historyGrade (Schedule.events schedule) =
      some schedule.workSpan at workSpanEquation
  rw [workSpanEquation]
  rfl

/-- If the added coordinate is total, erasing it recovers WorkSpan exactly.
This is an erasure theorem, not a reconstruction theorem in the other
direction. -/
theorem erase_total_coordinate_recovers_workSpan {Ground : Type uGround}
    (valuation : DeclaredValuation.{uGround, uGrade} Ground)
    (total : valuation.IsTotal)
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    Option.map (fun pair : WorkSpan × valuation.Grade => pair.1)
        (scheduleGrade (withWorkSpan valuation) schedule) =
      some schedule.workSpan := by
  rw [scheduleGrade_withWorkSpan]
  obtain ⟨grade, gradeEquation⟩ :=
    total.historyGrade_some (Schedule.events schedule)
  change scheduleGrade valuation schedule = some grade at gradeEquation
  rw [gradeEquation]
  rfl

/-! ## Explicit grade influence boundary -/

/-- Attach one candidate-local grade to every exact wave occurrence without
selecting, filtering, or pruning any occurrence. -/
def annotateSchedule {Ground : Type uGround} {Grade : Type uGrade}
    (grade : WaveEvent Ground → Grade)
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    List (WaveEvent Ground × Grade) :=
  attachGrades grade (Schedule.events schedule)

/-- Under ordinary occurrence-bag observation, attaching grades is
conservative: every wave occurrence and its multiplicity survives. -/
theorem annotateSchedule_erases_to_eventBag
    {Ground : Type uGround} {Grade : Type uGrade}
    (grade : WaveEvent Ground → Grade)
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    (eraseGradeBagObserver (WaveEvent Ground) Grade).observe
        (annotateSchedule grade schedule) =
      (Schedule.events schedule : Multiset (WaveEvent Ground)) := by
  exact eraseGradeBag_attachGrades grade (Schedule.events schedule)

/-- A grade changes the published occurrence denotation only through an
explicitly authored semantic filter.  The equality identifies that authored
operation; no filter is hidden in annotation or scheduling. -/
theorem filterAnnotatedSchedule_eq_authoredSemanticFilter
    {Ground : Type uGround} {Grade : Type uGrade}
    (grade : WaveEvent Ground → Grade) (accept : Grade → Bool)
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    supportByGrade accept (annotateSchedule grade schedule) =
      semanticFilterByGrade grade accept (Schedule.events schedule) := by
  exact supportByGrade_attachGrades grade accept (Schedule.events schedule)

/-! ## Generic non-reconstruction controls -/

/-- Equal WorkSpan together with a distinguished exact history refutes any
claim that WorkSpan universally reconstructs Cost₁ chronology. -/
theorem no_history_recovery_of_workSpan_collision
    {Ground : Type uGround}
    {firstSource firstTarget secondSource secondTarget : CostConfig Ground}
    {first : OperationalSchedule Ground firstSource firstTarget}
    {second : OperationalSchedule Ground secondSource secondTarget}
    (sameWorkSpan : first.workSpan = second.workSpan)
    (differentHistory : Schedule.events first ≠ Schedule.events second) :
    ¬ ∃ recover : WorkSpan → List (WaveEvent Ground),
        recover first.workSpan = Schedule.events first ∧
          recover second.workSpan = Schedule.events second := by
  rintro ⟨recover, recoversFirst, recoversSecond⟩
  apply differentHistory
  rw [← recoversFirst, ← recoversSecond, sameWorkSpan]

/-- Equal exact histories force equal values for every declared readout.
Therefore any value distinction must be backed by a retained history
distinction; it cannot be minted by the observer. -/
theorem readout_eq_of_history_eq
    {Ground : Type uGround} {Value : Type uOtherGrade}
    (readout : List (WaveEvent Ground) → Value)
    {source target : CostConfig Ground}
    {first second : OperationalSchedule Ground source target}
    (sameHistory : Schedule.events first = Schedule.events second) :
    readout (Schedule.events first) = readout (Schedule.events second) :=
  congrArg readout sameHistory

#print axioms scheduleGrade_append
#print axioms scheduleGrade_workSpan
#print axioms chronology_historyGrade
#print axioms scheduleGrade_chronology
#print axioms scheduleGrade_withWorkSpan
#print axioms erase_total_coordinate_recovers_workSpan
#print axioms annotateSchedule_erases_to_eventBag
#print axioms filterAnnotatedSchedule_eq_authoredSemanticFilter
#print axioms no_history_recovery_of_workSpan_collision
#print axioms readout_eq_of_history_eq

end Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation
