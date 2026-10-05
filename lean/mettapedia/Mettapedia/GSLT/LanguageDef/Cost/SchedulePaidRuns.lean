import Mettapedia.GSLT.Causality.ResourceRuns
import Mettapedia.GSLT.LanguageDef.Cost.ScheduleWriter
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceWave

/-!
# Funded schedules are runs of the funded resource system

An operational schedule of the rho Cost runtime is a chronological path of
parallel waves, each with the receipt of its funded events. The funded
resource system fires one funded event at a time. They are related wave by
wave (`WaveRuns`): a wave's events fired in its listed order form a stretch of
a run, the stretches come in the order of the waves, and the stretch of a wave
fires exactly the events of the wave's receipt, with their multiplicities.

The firings of a run determine where it ends, what it pays and its receipt.
So the run of a schedule pays what the receipts record, fires as many events
as the schedule's work, and obeys the conservation law of resource systems.
Composing schedules composes their runs, and a run of composed schedules
splits. Without payment, a funded run fires the same communications in the same
order, and its purses differ from the funded run's by the purses selected and
the rests they left. Every wave fires an event, so a schedule with an empty
receipt goes nowhere, and every rho event pays, so a run pays at least one cell
per firing.

The span of a schedule is not read off its run: the same firings, in the same
order, run a schedule of one wave of two events and a schedule of two waves of
one event each.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns

open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath OccurrenceValuation OccurrenceCat)
open Mettapedia.GSLT.Causality.TraceCostValuation (pathAccount traceAccount traceFunctor)
open Mettapedia.Effects (RunAccount)
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

variable {Ground : Type u} [DecidableEq Ground]

/-- A run of the funded rho resource system. -/
abbrev PaidRun (source target : CostConfig Ground) :=
  OccurrencePath (costResourceSystem Ground).presentation source target

/-- The receipt of a run: the spend events of its funded events, with their
multiplicities. -/
def runReceipt {source target : CostConfig Ground} (run : PaidRun source target) :
    Multiset (SpendEvent Ground (CostName Ground)) :=
  (((costResourceSystem Ground).pathEntries run).map fun entry =>
    (CostResourceWave.event entry).toSpendEvent : List _)

/-- What a run pays: the spends of its funded events. -/
def runPayment {source target : CostConfig Ground} (run : PaidRun source target) :
    CostSig Ground :=
  ((costResourceSystem Ground).instanceValuation fun event => event.val.spend).onPath run

theorem runReceipt_append {source middle target : CostConfig Ground}
    (first : PaidRun source middle) (second : PaidRun middle target) :
    runReceipt (first.append second) = runReceipt first + runReceipt second := by
  unfold runReceipt
  rw [System.pathEntries_append, List.map_append]
  rfl

/-- **A run pays what its receipt records.** -/
theorem runPayment_eq_receipt {source target : CostConfig Ground} (run : PaidRun source target) :
    runPayment run = ((runReceipt run).map SpendEvent.rawSpend).sum := by
  unfold runPayment runReceipt
  rw [System.instanceValuation_onPath]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_map]
  congr 1
  refine List.map_congr_left fun entry _ => ?_
  exact (CostedEvent.toSpendEvent_rawSpend (CostResourceWave.event entry)).symm

variable (Ground) in
/-- What runs pay, as an account of runs. -/
def paymentAccount :
    RunAccount (OccurrenceCat (costResourceSystem Ground).presentation)
      (Multiplicative (CostSig Ground)) :=
  pathAccount ((costResourceSystem Ground).instanceValuation fun event => event.val.spend)

variable (Ground) in
/-- **What runs pay is an account of their traces**: two concurrent funded
events fired in either order pay the same. -/
def paymentTraceAccount :
    RunAccount (Mettapedia.GSLT.Causality.EventConcurrency.TraceCat
      (costResourceSystem Ground).concurrency.tiles)
      (Multiplicative (CostSig Ground)) :=
  traceAccount _ _ ((costResourceSystem Ground).instanceValuation_descends
    fun event => event.val.spend)

/-- The account of traces restricts to the account of runs. -/
theorem paymentTraceAccount_comap :
    (paymentTraceAccount Ground).comap (traceFunctor _) = paymentAccount Ground :=
  rfl

/-- The account of a run is what the run pays, and so is the account of its
trace. -/
theorem paymentAccount_of {source target : CostConfig Ground} (run : PaidRun source target) :
    (paymentAccount Ground).of (source := source) (target := target) run =
        Multiplicative.ofAdd (runPayment run) ∧
      (paymentTraceAccount Ground).of (source := source) (target := target)
          ((traceFunctor _).map run) =
        Multiplicative.ofAdd (runPayment run) :=
  ⟨rfl, rfl⟩

/-- **A run fires as many events as its receipt holds.** -/
theorem runReceipt_card {source target : CostConfig Ground} (run : PaidRun source target) :
    (runReceipt run).card = ((costResourceSystem Ground).pathEntries run).length := by
  unfold runReceipt
  rw [Multiset.coe_card, List.length_map]

/-- What a run pays, firing by firing. -/
theorem runPayment_eq_sum {source target : CostConfig Ground} (run : PaidRun source target) :
    runPayment run =
      (((costResourceSystem Ground).pathEntries run).map fun entry => entry.2.val.spend).sum :=
  System.instanceValuation_onPath _ _ run

/-- **The firings of a run determine what is read off it**: two runs from one
configuration with the same firings in the same order end in the same
configuration, pay the same and have the same receipt. -/
theorem observations_of_entries {source target target' : CostConfig Ground}
    (first : PaidRun source target) (second : PaidRun source target')
    (same : (costResourceSystem Ground).pathEntries first =
      (costResourceSystem Ground).pathEntries second) :
    target = target' ∧ runPayment first = runPayment second ∧
      runReceipt first = runReceipt second := by
  refine ⟨(costResourceSystem Ground).target_eq_of_pathEntries_eq first second same, ?_, ?_⟩
  · rw [runPayment_eq_sum, runPayment_eq_sum, same]
  · unfold runReceipt
    rw [same]

/-- What a run pays adds along composition. -/
theorem runPayment_append {source middle target : CostConfig Ground}
    (first : PaidRun source middle) (second : PaidRun middle target) :
    runPayment (first.append second) = runPayment first + runPayment second :=
  OccurrenceValuation.onPath_append _ first second

omit [DecidableEq Ground] in
private theorem length_le_card_sum :
    ∀ sigs : List (CostSig Ground), (∀ sig ∈ sigs, sig ≠ 0) → sigs.length ≤ sigs.sum.card
  | [], _ => le_refl 0
  | sig :: rest, valid => by
      rw [List.length_cons, List.sum_cons, Multiset.card_add]
      have head := Multiset.card_pos.mpr (valid sig (by simp))
      have tail := length_le_card_sum rest fun other member => valid other (by simp [member])
      omega

/-- **Every funded rho firing pays.** The signature an event spends is never
empty, so a run pays at least one cell for each firing. This is a property of
rho's prices: a system priced at zero does work without paying
(`RunControls.zero_price_still_works`). -/
theorem length_le_runPayment_card {source target : CostConfig Ground}
    (run : PaidRun source target) :
    ((costResourceSystem Ground).pathEntries run).length ≤ (runPayment run).card := by
  have bound := length_le_card_sum
    (((costResourceSystem Ground).pathEntries run).map fun entry => entry.2.val.spend)
    (by
      intro sig member
      obtain ⟨entry, -, rfl⟩ := List.mem_map.mp member
      exact entry.2.val.spend_valid)
  rw [List.length_map] at bound
  unfold runPayment
  rw [System.instanceValuation_onPath]
  exact bound

/-! ## The ledger law -/

/-- **The ledger law on the funded rho runtime.** The signatures stored in the
purses before a run, with those stored in the purses its contracta release, are
the signatures stored after it with what the run pays. -/
theorem ledger_law {source target : CostConfig Ground} (run : PaidRun source target) :
    (cellBag source.purses).sum +
        ((costResourceSystem Ground).instanceValuation fun event =>
          (cellBag event.val.contractum.purses).sum).onPath run =
      (cellBag target.purses).sum + runPayment run := by
  have summed := congrArg Multiset.sum (costResource_run_cells_taken run)
  rw [Multiset.sum_add, Multiset.sum_add] at summed
  have released := (costResourceSystem Ground).instanceValuation_onPath_map
    Multiset.sumAddMonoidHom (fun event => cellBag event.val.contractum.purses) run
  have taken := (costResourceSystem Ground).instanceValuation_onPath_map
    Multiset.sumAddMonoidHom (fun event => event.val.funding.chosen.map SelectedPurseHead.head) run
  have pays := (costResourceSystem Ground).instanceValuation_congr
    (f := fun event => (event.val.funding.chosen.map SelectedPurseHead.head).sum)
    (g := fun event => event.val.spend) (fun event => CostedEvent.sum_selected_heads event.val) run
  simp only [Multiset.coe_sumAddMonoidHom] at released taken
  rw [released, taken, pays] at summed
  exact summed

/-- **With no purse released, the fuel at the start is the fuel remaining with
the fuel recorded spent**, and what the run pays is recoverable from its two
ends. -/
theorem ledger_law_of_no_release {source target : CostConfig Ground}
    (run : PaidRun source target)
    (none : ∀ entry ∈ (costResourceSystem Ground).pathEntries run,
      entry.2.val.contractum.purses = 0) :
    (cellBag source.purses).sum = (cellBag target.purses).sum + runPayment run ∧
      runPayment run = (cellBag source.purses).sum - (cellBag target.purses).sum := by
  have released : ((costResourceSystem Ground).instanceValuation fun event =>
      (cellBag event.val.contractum.purses).sum).onPath run = 0 := by
    rw [System.instanceValuation_onPath]
    refine List.sum_eq_zero fun cells member => ?_
    obtain ⟨entry, inRun, rfl⟩ := List.mem_map.mp member
    rw [none entry inRun]
    rfl
  have ledger := ledger_law run
  rw [released, add_zero] at ledger
  exact ⟨ledger, by rw [ledger, add_tsub_cancel_left]⟩

/-! ## A funded run is a run of its communications -/

/-- **A funded run is a run of its communications, with a ledger of its
purses.** The communications of the funded events fire in the same order from
the same configuration, without payment. The two runs end with the same
components that are not purses; the run without payment ends with the purses
the funded run selected in place of the rests they left. -/
theorem unpaid_run {source target : CostConfig Ground} (run : PaidRun source target) :
    ∃ (unpaidTarget : CostConfig Ground)
      (unpaid : OccurrencePath (unpaidResourceSystem Ground).presentation source unpaidTarget),
      (unpaidResourceSystem Ground).pathEntries unpaid =
          ((costResourceSystem Ground).pathEntries run).map (fun entry => unpaidEntry entry.2) ∧
        unpaidTarget.filter (fun term => ¬ term.isPurse) =
          target.filter (fun term => ¬ term.isPurse) ∧
        unpaidTarget + ((costResourceSystem Ground).instanceValuation fun event =>
            (purseResourceSystem Ground).produce (purseEntry event).2).onPath run =
          target + ((costResourceSystem Ground).instanceValuation fun event =>
            (purseResourceSystem Ground).consume (purseEntry event).2).onPath run :=
  (unpaidResourceSystem Ground).joint_path_left_parts (purseResourceSystem Ground)
    (@unpaidEntry Ground) (@purseEntry Ground) (fun term => term.isPurse)
    (fun event => unpaid_uses (unpaidEntry event).2)
    (fun event => purse_uses (purseEntry event).2)
    (fun event => purse_produces (purseEntry event).2) run

/-! ## A wave is a stretch of a run -/

/-- **A matching fires its listed events as a run**: from the matching's source
to its target, firing its events in the listed order, with the matching's
receipt. -/
theorem matching_run (matching : CostMatching Ground) :
    ∃ run : PaidRun matching.source matching.target,
      (costResourceSystem Ground).pathEntries run =
          matching.events.map CostedEvent.resourceEntry ∧
        runReceipt run = matching.receipt := by
  have target_eq := matching.resourceTarget
  obtain ⟨run, entries⟩ := (costResourceSystem Ground).exists_path_of_stepEnables
    (matching.events.map CostedEvent.resourceEntry) matching.resourceEnabled
  generalize (costResourceSystem Ground).waveTarget matching.source
    (matching.events.map CostedEvent.resourceEntry) = waveTarget at run entries target_eq
  subst target_eq
  refine ⟨run, entries, ?_⟩
  unfold runReceipt
  rw [entries, List.map_map]
  rfl

/-- `matching_run`, with the run's endpoints named as the caller states them. -/
theorem matching_run_at (matching : CostMatching Ground) {source target : CostConfig Ground}
    (sameSource : matching.source = source) (sameTarget : matching.target = target) :
    ∃ run : PaidRun source target,
      (costResourceSystem Ground).pathEntries run =
          matching.events.map CostedEvent.resourceEntry ∧
        runReceipt run = matching.receipt := by
  subst sameSource sameTarget
  exact matching_run matching

/-- **A wave fires its listed events as a run**: from the wave's source to its
target, firing exactly the events of the wave's receipt. -/
theorem wave_run {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    (step : ParallelCostStep source receipt target) :
    ∃ run : PaidRun source target, runReceipt run = receipt := by
  obtain ⟨matching, rfl, -, rfl, rfl⟩ := step
  obtain ⟨run, -, receipt_eq⟩ := matching_run matching
  exact ⟨run, receipt_eq⟩

omit [DecidableEq Ground] in
/-- A wave fires at least one event. -/
theorem receipt_ne_zero_of_step {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    (step : ParallelCostStep source receipt target) : receipt ≠ 0 := by
  obtain ⟨matching, -, nonempty, rfl, -⟩ := step
  simpa [CostMatching.receipt, costWaveReceipt] using nonempty

omit [DecidableEq Ground] in
/-- **A schedule that fires nothing goes nowhere.** Every wave fires at least
one event, so a schedule with an empty receipt has no wave. -/
theorem eq_of_receipt_eq_zero : ∀ {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target),
    schedule.receipt = 0 → source = target
  | _, _, Route.refl _, _ => rfl
  | _, _, Route.cons ⟨waveReceipt, wave⟩ _, empty => by
      have cards := congrArg Multiset.card empty
      change (waveReceipt + _).card = (0 : Multiset _).card at cards
      rw [Multiset.card_add, Multiset.card_zero] at cards
      exact absurd (Multiset.card_eq_zero.mp (by omega)) (receipt_ne_zero_of_step wave.down)

omit [DecidableEq Ground] in
/-- A schedule of one wave is that wave. -/
theorem exists_one_wave : ∀ {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target), schedule.waves = 1 →
    ∃ (waveReceipt : Multiset (SpendEvent Ground (CostName Ground)))
      (wave : PLift (ParallelCostStep source waveReceipt target)),
      schedule = Route.cons ⟨waveReceipt, wave⟩ (Route.refl target)
  | _, _, Route.refl _, one => by
      simp only [OperationalSchedule.waves] at one
      omega
  | _, _, Route.cons ⟨waveReceipt, wave⟩ (Route.refl _), _ => ⟨waveReceipt, wave, rfl⟩
  | _, _, Route.cons _ (Route.cons _ _), one => by
      simp only [OperationalSchedule.waves] at one
      omega

/-- A schedule and a run agree wave by wave: each wave is a stretch of the run
firing exactly the wave's receipt, and the stretches come in the order of the
waves. -/
inductive WaveRuns : {source target : CostConfig Ground} →
    OperationalSchedule Ground source target → PaidRun source target → Prop where
  | nil (config : CostConfig Ground) :
      WaveRuns (Route.refl config) (OccurrencePath.refl (P := (costResourceSystem Ground).presentation) config)
  | cons {source middle target : CostConfig Ground}
      {waveReceipt : Multiset (SpendEvent Ground (CostName Ground))}
      {wave : PLift (ParallelCostStep source waveReceipt middle)}
      {tail : OperationalSchedule Ground middle target}
      {waveRun : PaidRun source middle} {tailRun : PaidRun middle target} :
      runReceipt waveRun = waveReceipt → WaveRuns tail tailRun →
      WaveRuns (Route.cons ⟨waveReceipt, wave⟩ tail) (waveRun.append tailRun)

/-- **A one-wave schedule is run by any matching of its wave**: from a
matching with the schedule's source, target and receipt, the matching's events
fired in their listed order are a run of the schedule. -/
theorem one_wave_run {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) (one : schedule.waves = 1)
    (matching : CostMatching Ground) (sameSource : matching.source = source)
    (sameTarget : matching.target = target) (sameReceipt : matching.receipt = schedule.receipt) :
    ∃ run : PaidRun source target, WaveRuns schedule run ∧
      (costResourceSystem Ground).pathEntries run =
        matching.events.map CostedEvent.resourceEntry := by
  subst sameSource sameTarget
  obtain ⟨waveReceipt, wave, shape⟩ := exists_one_wave schedule one
  subst shape
  obtain ⟨run, entries, receipt_eq⟩ := matching_run matching
  refine ⟨run.append (OccurrencePath.refl _), .cons ?_ (.nil _), ?_⟩
  · exact receipt_eq.trans (sameReceipt.trans (add_zero waveReceipt))
  · rw [System.pathEntries_append, entries, System.pathEntries_refl, List.append_nil]

/-- **Every funded schedule determines a run**, wave by wave. -/
theorem exists_waveRuns : ∀ {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target),
    ∃ run : PaidRun source target, WaveRuns schedule run
  | _, _, Route.refl config => ⟨_, .nil config⟩
  | _, _, Route.cons ⟨waveReceipt, wave⟩ tail => by
      obtain ⟨waveRun, waveReceipt_eq⟩ := wave_run wave.down
      obtain ⟨tailRun, tailRuns⟩ := exists_waveRuns tail
      exact ⟨waveRun.append tailRun, .cons waveReceipt_eq tailRuns⟩

/-- **The run of a schedule fires exactly the schedule's receipt.** -/
theorem WaveRuns.receipt {source target : CostConfig Ground}
    {schedule : OperationalSchedule Ground source target} {run : PaidRun source target}
    (runs : WaveRuns schedule run) : runReceipt run = schedule.receipt := by
  induction runs with
  | nil config => rfl
  | cons waveReceipt_eq _ tailReceipt =>
      rw [runReceipt_append, waveReceipt_eq, tailReceipt]
      rfl

/-- **The run of a schedule pays what the schedule's receipt records.** -/
theorem WaveRuns.payment {source target : CostConfig Ground}
    {schedule : OperationalSchedule Ground source target} {run : PaidRun source target}
    (runs : WaveRuns schedule run) :
    runPayment run = (schedule.receipt.map SpendEvent.rawSpend).sum := by
  rw [runPayment_eq_receipt, runs.receipt]

/-- **The run of a schedule does the schedule's work**: it fires as many
events as the schedule. -/
theorem WaveRuns.work {source target : CostConfig Ground}
    {schedule : OperationalSchedule Ground source target} {run : PaidRun source target}
    (runs : WaveRuns schedule run) :
    ((costResourceSystem Ground).pathEntries run).length = schedule.workSpan.work := by
  rw [← runReceipt_card, runs.receipt, OperationalSchedule.work_eq_receipt_card]

/-- **The run of a schedule obeys the conservation law**: the configuration
before, with all its events produce, is the configuration after, with all
they consume. -/
theorem WaveRuns.balance {source target : CostConfig Ground}
    {schedule : OperationalSchedule Ground source target} {run : PaidRun source target}
    (_runs : WaveRuns schedule run) :
    source + (costResourceSystem Ground).producedValuation.onPath run =
      target + (costResourceSystem Ground).consumedValuation.onPath run :=
  (costResourceSystem Ground).balance run

/-- **Composing schedules composes their runs.** -/
theorem WaveRuns.append {source middle target : CostConfig Ground}
    {first : OperationalSchedule Ground source middle}
    {second : OperationalSchedule Ground middle target}
    {firstRun : PaidRun source middle} {secondRun : PaidRun middle target}
    (firstRuns : WaveRuns first firstRun) (secondRuns : WaveRuns second secondRun) :
    WaveRuns (first.append second) (firstRun.append secondRun) := by
  induction firstRuns with
  | nil config => exact secondRuns
  | @cons _ _ _ _ wave _ waveRun tailRun waveReceipt_eq _ tailRuns =>
      have composed := WaveRuns.cons (wave := wave) waveReceipt_eq (tailRuns secondRuns)
      convert composed using 1
      · rfl
      · exact OccurrencePath.append_assoc waveRun tailRun secondRun

/-- **A run of composed schedules splits** into runs of the two schedules. -/
theorem WaveRuns.split : ∀ {source middle target : CostConfig Ground}
    (first : OperationalSchedule Ground source middle)
    (second : OperationalSchedule Ground middle target) {run : PaidRun source target},
    WaveRuns (first.append second) run →
      ∃ (firstRun : PaidRun source middle) (secondRun : PaidRun middle target),
        run = firstRun.append secondRun ∧ WaveRuns first firstRun ∧ WaveRuns second secondRun
  | _, _, _, Route.refl config, _, run, runs =>
      ⟨OccurrencePath.refl (P := (costResourceSystem Ground).presentation) config, run, rfl,
        .nil config, runs⟩
  | _, _, _, Route.cons ⟨waveReceipt, wave⟩ tail, second, _, runs => by
      change WaveRuns (Route.cons ⟨waveReceipt, wave⟩ (tail.append second)) _ at runs
      cases runs with
      | cons waveReceipt_eq tailRuns =>
          obtain ⟨tailFirst, secondRun, rfl, tailFirstRuns, secondRuns⟩ :=
            WaveRuns.split tail second tailRuns
          exact ⟨_, secondRun, (OccurrencePath.append_assoc _ _ _).symm,
            .cons waveReceipt_eq tailFirstRuns, secondRuns⟩

/-- **Composing schedules adds what their runs pay and the work they do.** -/
theorem WaveRuns.append_payment_work {source middle target : CostConfig Ground}
    {first : OperationalSchedule Ground source middle}
    {second : OperationalSchedule Ground middle target}
    {firstRun : PaidRun source middle} {secondRun : PaidRun middle target}
    (firstRuns : WaveRuns first firstRun) (secondRuns : WaveRuns second secondRun) :
    runPayment (firstRun.append secondRun) = runPayment firstRun + runPayment secondRun ∧
      ((costResourceSystem Ground).pathEntries (firstRun.append secondRun)).length =
        (first.append second).workSpan.work := by
  refine ⟨runPayment_append firstRun secondRun, ?_⟩
  exact (firstRuns.append secondRuns).work

end Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns
