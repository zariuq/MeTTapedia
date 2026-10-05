import Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCostLayerOperationalAdequacy
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCostLayerReceiptObservation

/-!
# candidate schedules as paid runs

Every operational schedule, and in particular every schedule the candidate
compiles, determines a run of the funded rho resource system, wave by wave
(`WaveRuns`). Read off that run: the endpoint is the schedule's target, the
payment is the spend of the schedule's receipt, the firings are as many as the
schedule's work, and the receipt is the one read from the schedule's
chronological wave history. Without payment, the same run fires the same
communications in the same order, and its purses differ from the funded run's
exactly by the purses selected and the rests they left. These are theorems
about every schedule, not fields of a realization record.

Payment and work are read off the run; span is not. The compiled one-wave
schedule of two separated events and the two-wave schedule of the same events
are run by the same firings in the same order, between the same
configurations, with the same payment and work, and spans 1 and 2.

Controls:

* two independent paid firings in one wave, and the same two occurrences of one
  event value in one wave with a third;
* two contenders for one purse, each enabled alone: the analysis refuses them,
  no wave of any size fires both, and each alone runs and pays;
* two chronological orders with the same payment and work and different
  firings and histories;
* the compiled step cannot be erased: no schedule between its endpoints has an
  empty receipt.

A firing at price zero that still works is not a rho firing: every rho event
spends a nonempty signature, so a run pays at least one cell per firing
(`length_le_runPayment_card`). The generic control is
`RunControls.zero_price_still_works`.

This module adds to the operational face only: it relates two operational
readings of one execution, the schedule of waves and the run of funded
firings. The bags and their ledgers are the extensional reading of the same
runs. No typing judgment is involved, so the intensional face is absent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCostLayerPaidRuns

open Mettapedia.Algebra
open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)
open Mettapedia.GSLT.Causality.TraceCostValuation (traceFunctor)
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.CostScheduleObservation
open Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
open Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCostLayerOperationalAdequacy
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCostLayerReceiptObservation
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteractionFamilyFibration
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteractionFibration
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe uGround

/-! ## What a schedule determines, read off its run -/

section Schedules

variable {Ground : Type uGround} [DecidableEq Ground]

/-- **A schedule determines a paid run, and the run determines its
observations.** The run ends at the schedule's target, fires exactly the
receipt read from the schedule's chronological history, pays the spend of that
receipt, which is also what the payment account reads off the run's trace, and
fires as many events as the work in the schedule's declared observation. -/
theorem schedule_run {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    ∃ run : PaidRun source target, WaveRuns schedule run ∧
      runReceipt run =
        Schedule.eventReceipt ((operationalObservation Ground).container schedule) ∧
      runPayment run = (schedule.receipt.map SpendEvent.rawSpend).sum ∧
      (paymentTraceAccount Ground).of (source := source) (target := target)
          ((traceFunctor _).map run) =
        Multiplicative.ofAdd (schedule.receipt.map SpendEvent.rawSpend).sum ∧
      ((costResourceSystem Ground).pathEntries run).length =
        ((operationalObservation Ground).value schedule).work := by
  obtain ⟨run, runs⟩ := exists_waveRuns schedule
  refine ⟨run, runs, ?_, runs.payment, (paymentAccount_of run).2.trans
    (congrArg Multiplicative.ofAdd runs.payment), ?_⟩
  · rw [operational_receipt]
    exact runs.receipt
  · rw [operational_value]
    exact runs.work

/-- **Composing schedules composes their runs and everything read off them**:
the chronological histories concatenate, the payments add, and so do the
firings. -/
theorem compose_runs {source middle target : CostConfig Ground}
    {first : OperationalSchedule Ground source middle}
    {second : OperationalSchedule Ground middle target}
    {firstRun : PaidRun source middle} {secondRun : PaidRun middle target}
    (firstRuns : WaveRuns first firstRun) (secondRuns : WaveRuns second secondRun) :
    WaveRuns (first.append second) (firstRun.append secondRun) ∧
      Schedule.events (first.append second) = Schedule.events first ++ Schedule.events second ∧
      runPayment (firstRun.append secondRun) = runPayment firstRun + runPayment secondRun ∧
      (costResourceSystem Ground).pathEntries (firstRun.append secondRun) =
        (costResourceSystem Ground).pathEntries firstRun ++
          (costResourceSystem Ground).pathEntries secondRun :=
  ⟨firstRuns.append secondRuns, Schedule.events_append first second,
    runPayment_append firstRun secondRun, System.pathEntries_append _ firstRun secondRun⟩

/-- **Splitting a schedule splits its run**, and the payments and firings of
the parts add up to those of the whole. -/
theorem split_runs {source middle target : CostConfig Ground}
    (first : OperationalSchedule Ground source middle)
    (second : OperationalSchedule Ground middle target) {run : PaidRun source target}
    (runs : WaveRuns (first.append second) run) :
    ∃ (firstRun : PaidRun source middle) (secondRun : PaidRun middle target),
      WaveRuns first firstRun ∧ WaveRuns second secondRun ∧
      runPayment run = runPayment firstRun + runPayment secondRun ∧
      (costResourceSystem Ground).pathEntries run =
        (costResourceSystem Ground).pathEntries firstRun ++
          (costResourceSystem Ground).pathEntries secondRun := by
  obtain ⟨firstRun, secondRun, rfl, firstRuns, secondRuns⟩ := WaveRuns.split first second runs
  exact ⟨firstRun, secondRun, firstRuns, secondRuns, runPayment_append firstRun secondRun,
    System.pathEntries_append _ firstRun secondRun⟩

end Schedules

/-! ## Controls -/

namespace Examples

open NativeInteractionFibration.Examples
open NativeInteractionFamilyFibration.Examples
open NativeCostLayerReceiptObservation.Examples

/-! ### Two independent paid firings in one wave -/

/-- **The compiled one-wave schedule of two separated events is run by firing
them in order**, and the run pays both seals. -/
theorem compiled_run :
    ∃ run : PaidRun source sameChannelSeparation.target,
      WaveRuns (compiledOperationalSchedule sameChannelSeparation) run ∧
      (costResourceSystem Ground).pathEntries run =
        [leftEvent.resourceEntry, rightEvent.resourceEntry] ∧
      runPayment run = leftSeal + rightSeal ∧
      (compiledOperationalSchedule sameChannelSeparation).workSpan = ⟨2, 1⟩ := by
  obtain ⟨run, runs, entries⟩ := one_wave_run (compiledOperationalSchedule sameChannelSeparation)
    (compiled_waves sameChannelSeparation) sameChannelSeparation.toMatching rfl rfl
    (compiled_receipt sameChannelSeparation).symm
  refine ⟨run, runs, entries, ?_, compiled_workSpan sameChannelSeparation⟩
  rw [runPayment_eq_sum, entries]
  rfl

/-- **Without payment, the compiled run fires the two communications in the
same order**, and the purses it selected are the two events' purses, in
firing order. -/
theorem compiled_run_unpaid :
    ∃ run : PaidRun source sameChannelSeparation.target,
      WaveRuns (compiledOperationalSchedule sameChannelSeparation) run ∧
      ((costResourceSystem Ground).pathEntries run).map
          (fun entry => (CostResourceWave.event entry).chosenPurses) =
        [leftEvent.chosenPurses, rightEvent.chosenPurses] ∧
      ∃ (unpaidTarget : CostConfig Ground)
        (unpaid : OccurrencePath (unpaidResourceSystem Ground).presentation source unpaidTarget),
        ((unpaidResourceSystem Ground).pathEntries unpaid).map (fun entry => entry.2.val) =
          [leftEvent.unpaid, rightEvent.unpaid] ∧
        unpaidTarget.filter (fun term => ¬ term.isPurse) =
          sameChannelSeparation.target.filter (fun term => ¬ term.isPurse) := by
  obtain ⟨run, runs, entries, -, -⟩ := compiled_run
  obtain ⟨unpaidTarget, unpaid, unpaidEntries, ends, -⟩ := unpaid_run run
  refine ⟨run, runs, by rw [entries]; rfl, unpaidTarget, unpaid, ?_, ends⟩
  rw [unpaidEntries, entries]
  rfl

/-! ### Duplicate occurrences -/

/-- **Equal event values are separate firings.** The family of the left event,
the right event and the left event again is one wave; its run fires three
times and pays the left seal twice. -/
theorem repeated_run :
    ∃ run : PaidRun repeatedSource repeatedFamily.target,
      WaveRuns (familyOperationalSchedule repeatedFamily) run ∧
      (costResourceSystem Ground).pathEntries run =
        [leftEvent.resourceEntry, rightEvent.resourceEntry, leftEvent.resourceEntry] ∧
      runPayment run = leftSeal + rightSeal + leftSeal ∧
      (familyOperationalSchedule repeatedFamily).workSpan = ⟨3, 1⟩ := by
  obtain ⟨run, runs, entries⟩ := one_wave_run (familyOperationalSchedule repeatedFamily)
    (OperationalSchedule.waves_ofIndexed _) repeatedFamily.toMatching rfl rfl
    (OperationalSchedule.receipt_ofIndexed _).symm
  refine ⟨run, runs, entries, ?_, family_workSpan repeatedFamily⟩
  rw [runPayment_eq_sum, entries]
  rfl

/-! ### Span is read off the schedule, not off the run -/

/-- The two-wave schedule of the same two events, left first, is run by firing
them in order. -/
theorem forward_run :
    ∃ run : PaidRun source rightAfterLeft.target,
      WaveRuns forwardSchedule run ∧
      (costResourceSystem Ground).pathEntries run =
        [leftEvent.resourceEntry, rightEvent.resourceEntry] ∧
      runPayment run = leftSeal + rightSeal := by
  obtain ⟨first, firstEntries, firstReceipt⟩ :=
    matching_run_at leftSingleton.toMatching (source := source) (target := leftSingleton.target) rfl rfl
  obtain ⟨second, secondEntries, secondReceipt⟩ :=
    matching_run_at rightAfterLeft.toMatching (source := leftSingleton.target) (target := rightAfterLeft.target) rfl rfl
  have entries : (costResourceSystem Ground).pathEntries
      (first.append (second.append (OccurrencePath.refl _))) =
        [leftEvent.resourceEntry, rightEvent.resourceEntry] := by
    rw [System.pathEntries_append, System.pathEntries_append, firstEntries, secondEntries,
      System.pathEntries_refl]
    rfl
  refine ⟨first.append (second.append (OccurrencePath.refl _)),
    .cons firstReceipt (.cons secondReceipt (.nil _)), entries, ?_⟩
  rw [runPayment_eq_sum, entries]
  rfl

/-- The two-wave schedule, right first. -/
theorem reverse_run :
    ∃ run : PaidRun source leftAfterRight.target,
      WaveRuns reverseSchedule run ∧
      (costResourceSystem Ground).pathEntries run =
        [rightEvent.resourceEntry, leftEvent.resourceEntry] ∧
      runPayment run = rightSeal + leftSeal := by
  obtain ⟨first, firstEntries, firstReceipt⟩ :=
    matching_run_at rightSingleton.toMatching (source := source) (target := rightSingleton.target) rfl rfl
  obtain ⟨second, secondEntries, secondReceipt⟩ :=
    matching_run_at leftAfterRight.toMatching (source := rightSingleton.target) (target := leftAfterRight.target) rfl rfl
  have entries : (costResourceSystem Ground).pathEntries
      (first.append (second.append (OccurrencePath.refl _))) =
        [rightEvent.resourceEntry, leftEvent.resourceEntry] := by
    rw [System.pathEntries_append, System.pathEntries_append, firstEntries, secondEntries,
      System.pathEntries_refl]
    rfl
  refine ⟨first.append (second.append (OccurrencePath.refl _)),
    .cons firstReceipt (.cons secondReceipt (.nil _)), entries, ?_⟩
  rw [runPayment_eq_sum, entries]
  rfl

theorem forward_workSpan : forwardSchedule.workSpan = ⟨2, 2⟩ := by
  apply WorkSpan.ext
  · simp [forwardSchedule, OperationalSchedule.workSpan, FamilySeparation.receipt_card]
    rfl
  · simp [forwardSchedule, OperationalSchedule.workSpan]
    rfl

/-- **Span is not read off the run.** The compiled one-wave schedule and the
two-wave schedule of the same events are run by the same firings in the same
order, between the same configurations, with the same payment and the same
work; their spans are 1 and 2. -/
theorem span_is_not_read_off_the_run :
    ∃ (oneWave : PaidRun source sameChannelSeparation.target)
      (twoWaves : PaidRun source rightAfterLeft.target),
      WaveRuns (compiledOperationalSchedule sameChannelSeparation) oneWave ∧
      WaveRuns forwardSchedule twoWaves ∧
      sameChannelSeparation.target = rightAfterLeft.target ∧
      (costResourceSystem Ground).pathEntries oneWave =
        (costResourceSystem Ground).pathEntries twoWaves ∧
      runPayment oneWave = runPayment twoWaves ∧
      (compiledOperationalSchedule sameChannelSeparation).workSpan.work =
        forwardSchedule.workSpan.work ∧
      (compiledOperationalSchedule sameChannelSeparation).workSpan.span = 1 ∧
      forwardSchedule.workSpan.span = 2 := by
  obtain ⟨oneWave, oneRuns, oneEntries, -, oneWorkSpan⟩ := compiled_run
  obtain ⟨twoWaves, twoRuns, twoEntries, -⟩ := forward_run
  obtain ⟨sameEndpoint, samePayment, -⟩ :=
    observations_of_entries oneWave twoWaves (oneEntries.trans twoEntries.symm)
  refine ⟨oneWave, twoWaves, oneRuns, twoRuns, sameEndpoint, oneEntries.trans twoEntries.symm,
    samePayment, ?_, ?_, ?_⟩
  · rw [oneWorkSpan, forward_workSpan]
  · rw [oneWorkSpan]
  · rw [forward_workSpan]

/-! ### Two chronological orders -/

/-- **Two orders, the same payment and work, different evidence.** The forward
and the reverse two-wave schedules pay the same and have the same work and
span; their runs fire in different orders, and their chronological histories
differ. -/
theorem two_orders_same_payment_different_evidence :
    ∃ (forward : PaidRun source rightAfterLeft.target)
      (reverse : PaidRun source leftAfterRight.target),
      WaveRuns forwardSchedule forward ∧ WaveRuns reverseSchedule reverse ∧
      runPayment forward = runPayment reverse ∧
      forwardSchedule.workSpan = reverseSchedule.workSpan ∧
      (costResourceSystem Ground).pathEntries forward ≠
        (costResourceSystem Ground).pathEntries reverse ∧
      forwardHistory ≠ reverseHistory := by
  obtain ⟨forward, forwardRuns, forwardEntries, forwardPayment⟩ := forward_run
  obtain ⟨reverse, reverseRuns, reverseEntries, reversePayment⟩ := reverse_run
  have sameWorkSpan : forwardSchedule.workSpan = reverseSchedule.workSpan := by
    have same := two_orders_same_workSpan
    change historyWorkSpan (Schedule.events forwardSchedule) =
      historyWorkSpan (Schedule.events reverseSchedule) at same
    rwa [historyWorkSpan_events, historyWorkSpan_events] at same
  refine ⟨forward, reverse, forwardRuns, reverseRuns, ?_, sameWorkSpan, ?_,
    two_orders_distinct_histories⟩
  · rw [forwardPayment, reversePayment]
    exact add_comm _ _
  · rw [forwardEntries, reverseEntries]
    intro same
    have spends := congrArg (fun entries => entries.map fun entry => entry.2.val.spend) same
    change [leftSeal, rightSeal] = [rightSeal, leftSeal] at spends
    simp [leftSeal, rightSeal] at spends

/-! ### Two contenders for one purse -/

theorem leftEvent_ne_leftCompetitor : leftEvent ≠ leftCompetitor := by
  intro same
  obtain ⟨-, -, payloads, -⟩ := CostedEvent.wholeRecvSend.inj same
  simp [leftPayload, rightPayload, leftSeal, rightSeal] at payloads

/-- **No wave fires both contenders.** Each of them takes the one purse cell
of the contested source, so no matching from that source lists both, whatever
else it fires. -/
theorem contenders_share_no_wave (matching : CostMatching Ground)
    (fromSource : matching.source = contestedSource)
    (leftIn : leftEvent ∈ matching.events) : leftCompetitor ∉ matching.events := by
  intro competitorIn
  obtain ⟨rest, restEq⟩ :=
    Multiset.exists_cons_of_mem (s := (matching.events : Multiset (CostedEvent Ground)))
      (Multiset.mem_coe.mpr leftIn)
  have competitorInRest : leftCompetitor ∈ rest := by
    have member : leftCompetitor ∈ leftEvent ::ₘ rest := restEq ▸ Multiset.mem_coe.mpr competitorIn
    rcases Multiset.mem_cons.mp member with same | inRest
    · exact absurd same.symm leftEvent_ne_leftCompetitor
    · exact inRest
  obtain ⟨others, othersEq⟩ := Multiset.exists_cons_of_mem competitorInRest
  have sourceEq := matching.source_eq
  rw [fromSource] at sourceEq
  have consumedEq : (matching.events.map CostedEvent.consumed).sum =
      leftEvent.consumed + (leftCompetitor.consumed + (others.map CostedEvent.consumed).sum) := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, restEq, othersEq, Multiset.map_cons,
      Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
  have counts := congrArg (Multiset.count contestedPurse) sourceEq
  rw [costWaveSource, consumedEq, contestedPurse_count] at counts
  simp only [Multiset.count_add] at counts
  have leftCount : 1 ≤ leftEvent.consumed.count contestedPurse :=
    Multiset.count_pos.mpr (Multiset.mem_add.mpr (Or.inr leftEvent_uses_contestedPurse))
  have competitorCount : 1 ≤ leftCompetitor.consumed.count contestedPurse :=
    Multiset.count_pos.mpr (Multiset.mem_add.mpr (Or.inr leftCompetitor_uses_contestedPurse))
  omega

/-- The left event alone, from the contested source. -/
def leftAlone : FamilySeparation Ground [leftEvent] contestedSource where
  frame := leftCompetitor.endpoints
  source_eq := by
    simp only [contestedSource, costWaveSource, CostedEvent.consumed, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ac_rfl
  nonempty := by simp

/-- The competitor alone, from the contested source. -/
def competitorAlone : FamilySeparation Ground [leftCompetitor] contestedSource where
  frame := leftEvent.endpoints
  source_eq := by
    have sameFunding : leftCompetitor.fundingBefore = leftEvent.fundingBefore := rfl
    simp only [contestedSource, costWaveSource, CostedEvent.consumed, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, sameFunding]
    ac_rfl
  nonempty := by simp

/-- **A refused analysis leaves ordinary execution.** The analysis returns no
schedule for the two contenders, and no wave fires both; each alone is a
one-wave schedule whose run fires it and pays its seal. -/
theorem refused_analysis_leaves_execution :
    analyzeOperational? contestedSource leftEvent leftCompetitor = none ∧
      (∀ matching : CostMatching Ground, matching.source = contestedSource →
        leftEvent ∈ matching.events → leftCompetitor ∉ matching.events) ∧
      (∃ run : PaidRun contestedSource leftAlone.target,
        WaveRuns (familyOperationalSchedule leftAlone) run ∧
        (costResourceSystem Ground).pathEntries run = [leftEvent.resourceEntry] ∧
        runPayment run = leftSeal) ∧
      (∃ run : PaidRun contestedSource competitorAlone.target,
        WaveRuns (familyOperationalSchedule competitorAlone) run ∧
        (costResourceSystem Ground).pathEntries run = [leftCompetitor.resourceEntry] ∧
        runPayment run = leftSeal) := by
  refine ⟨Examples.contested_operational_analysis_is_none, contenders_share_no_wave, ?_, ?_⟩
  · obtain ⟨run, runs, entries⟩ := one_wave_run (familyOperationalSchedule leftAlone)
      (OperationalSchedule.waves_ofIndexed _) leftAlone.toMatching rfl rfl
      (OperationalSchedule.receipt_ofIndexed _).symm
    refine ⟨run, runs, entries, ?_⟩
    rw [runPayment_eq_sum, entries]
    rfl
  · obtain ⟨run, runs, entries⟩ := one_wave_run (familyOperationalSchedule competitorAlone)
      (OperationalSchedule.waves_ofIndexed _) competitorAlone.toMatching rfl rfl
      (OperationalSchedule.receipt_ofIndexed _).symm
    refine ⟨run, runs, entries, ?_⟩
    rw [runPayment_eq_sum, entries]
    rfl

/-! ### The compiled step cannot be erased -/

theorem source_ne_compiled_target : source ≠ sameChannelSeparation.target := by
  intro same
  have counts := congrArg (Multiset.count contestedPurse) same
  revert counts
  decide

/-- **No schedule between the compiled step's endpoints is empty.** A schedule
with an empty receipt has no wave and ends where it starts, and the compiled
step does not. So an interpretation that erases the step's events realizes no
schedule between its endpoints. -/
theorem compiled_step_is_not_erased
    (schedule : OperationalSchedule Ground source sameChannelSeparation.target) :
    schedule.receipt ≠ 0 :=
  fun empty => source_ne_compiled_target (eq_of_receipt_eq_zero schedule empty)

end Examples

#print axioms schedule_run
#print axioms compose_runs
#print axioms split_runs
#print axioms Examples.compiled_run
#print axioms Examples.compiled_run_unpaid
#print axioms Examples.repeated_run
#print axioms Examples.span_is_not_read_off_the_run
#print axioms Examples.two_orders_same_payment_different_evidence
#print axioms Examples.contenders_share_no_wave
#print axioms Examples.refused_analysis_leaves_execution
#print axioms Examples.compiled_step_is_not_erased

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCostLayerPaidRuns
