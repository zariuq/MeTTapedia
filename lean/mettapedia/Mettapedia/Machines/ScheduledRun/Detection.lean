import Mettapedia.Machines.ScheduledRun.Monitor
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Eventual detection by the period-reset prefix procedure

An infinite run visiting finitely many states eventually encounters every
arity it will ever encounter. The learned period then equals their LCM and
stops growing. The record is complete for visits after that stable epoch;
pigeonhole on state/phase configurations forces a report. Neither fairness
nor an assumed eventual loop is an input to this argument.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun

universe u
variable {S : Type u}

theorem prefixPeriod_dvd_visited (next : S → List S) (initial : S)
    (finite : (visited next rotating initial).Finite) (turn : Nat) :
    prefixPeriod next .rotating (run next rotating initial) turn ∣ visitedPeriod next rotating initial finite :=
  prefixPeriod_dvd_common next _ _ turn
    (fun before _ _state present _ => visited_arity_dvd next rotating initial finite ⟨before, present⟩)

theorem rotating_period_stabilizes (next : S → List S) (initial : S)
    (finite : (visited next rotating initial).Finite) (infinite : Nonterminating next rotating initial) :
    ∃ cutoff, ∀ turn, cutoff ≤ turn →
      prefixPeriod next .rotating (run next rotating initial) turn = visitedPeriod next rotating initial finite := by
  classical
  let states := finite.toFinset
  have witness : ∀ state : {state // state ∈ states},
      ∃ turn, run next rotating initial turn = some state.val :=
    fun state => finite.mem_toFinset.mp state.property
  let chosen := fun state : {state // state ∈ states} => Classical.choose (witness state)
  let cutoff := states.attach.sup (fun state => chosen state + 1)
  have covers : ∀ state ∈ states,
      (next state).length ∣ prefixPeriod next .rotating (run next rotating initial) cutoff := by
    intro state member
    let entry : {state // state ∈ states} := ⟨state, member⟩
    have bound : chosen entry + 1 ≤ cutoff :=
      Finset.le_sup (f := fun state => chosen state + 1) (Finset.mem_attach states entry)
    have present := Classical.choose_spec (witness entry)
    exact arity_dvd_prefixPeriod next _ (by omega : chosen entry < cutoff) present
      (nonterminal_on_infinite next rotating initial infinite present)
  have common : visitedPeriod next rotating initial finite ∣
      prefixPeriod next .rotating (run next rotating initial) cutoff := Finset.lcm_dvd covers
  have atCutoff := Nat.dvd_antisymm (prefixPeriod_dvd_visited next initial finite cutoff) common
  refine ⟨cutoff, fun turn later => Nat.dvd_antisymm (prefixPeriod_dvd_visited next initial finite turn) ?_⟩
  rw [← atCutoff]
  exact prefixPeriod_dvd_of_le next .rotating _ later

theorem mode_period_stabilizes (next : S → List S) (mode : Mode) (initial : S)
    (finite : (visited next mode.schedule initial).Finite)
    (infinite : Nonterminating next mode.schedule initial) :
    ∃ cutoff period, 0 < period ∧ ∀ turn, cutoff ≤ turn →
      prefixPeriod next mode (run next mode.schedule initial) turn = period := by
  cases mode with
  | canonical => exact ⟨0, 1, Nat.zero_lt_one, fun turn _ => canonical_prefixPeriod next _ turn⟩
  | rotating =>
    obtain ⟨cutoff, stable⟩ := rotating_period_stabilizes next initial finite infinite
    exact ⟨cutoff, visitedPeriod next rotating initial finite,
      visitedPeriod_pos next rotating initial finite infinite, stable⟩

variable [DecidableEq S]

theorem recordStep_seen_mono (next : S → List S) (mode : Mode) (turn : Nat)
    (observation : Option S) (record : VisitRecord S)
    (same : (recordStep next mode turn observation record).period = record.period) :
    record.seen ⊆ (recordStep next mode turn observation record).seen := by
  cases observation with
  | none => exact Finset.Subset.refl _
  | some state =>
    by_cases unchanged : updatePeriod mode record.period (next state).length = record.period
    · simpa only [recordStep, if_pos unchanged] using
        (Finset.subset_insert (state, turn % record.period) record.seen)
    · simp [recordStep, unchanged] at same

theorem recordStep_records (next : S → List S) (mode : Mode) (turn : Nat)
    (state : S) (record : VisitRecord S)
    (same : (recordStep next mode turn (some state) record).period = record.period) :
    (state, turn % record.period) ∈ (recordStep next mode turn (some state) record).seen := by
  by_cases unchanged : updatePeriod mode record.period (next state).length = record.period
  · simp [recordStep, unchanged]
  · simp [recordStep, unchanged] at same

theorem stable_seen_mono (next : S → List S) (mode : Mode) (trace : Nat → Option S)
    (cutoff period : Nat)
    (stable : ∀ turn, cutoff ≤ turn → (recordPrefix next mode trace turn).period = period)
    {early late : Nat} (past : cutoff ≤ early) (order : early ≤ late) :
    (recordPrefix next mode trace early).seen ⊆ (recordPrefix next mode trace late).seen := by
  have oneStep : ∀ turn, cutoff ≤ turn →
      (recordPrefix next mode trace turn).seen ⊆ (recordPrefix next mode trace (turn + 1)).seen := by
    intro turn after
    apply recordStep_seen_mono
    change (recordPrefix next mode trace (turn + 1)).period = (recordPrefix next mode trace turn).period
    rw [stable (turn + 1) (by omega), stable turn after]
  have chain : ∀ offset, (recordPrefix next mode trace early).seen ⊆
      (recordPrefix next mode trace (early + offset)).seen := by
    intro offset
    induction offset with
    | zero => exact Finset.Subset.refl _
    | succ offset ih => exact ih.trans (oneStep (early + offset) (by omega))
  simpa only [Nat.add_sub_of_le order] using chain (late - early)

theorem stable_record_covers (next : S → List S) (mode : Mode) (trace : Nat → Option S)
    (cutoff period : Nat)
    (stable : ∀ turn, cutoff ≤ turn → (recordPrefix next mode trace turn).period = period)
    {first last : Nat} {state : S} (past : cutoff ≤ first) (order : first < last)
    (present : trace first = some state) :
    (state, first % period) ∈ (recordPrefix next mode trace last).seen := by
  have same : (recordStep next mode first (some state) (recordPrefix next mode trace first)).period =
      (recordPrefix next mode trace first).period := by
    rw [← present]
    change (recordPrefix next mode trace (first + 1)).period = (recordPrefix next mode trace first).period
    rw [stable (first + 1) (by omega), stable first past]
  have recorded := recordStep_records next mode first state (recordPrefix next mode trace first) same
  rw [stable first past, ← present] at recorded
  change (state, first % period) ∈ (recordPrefix next mode trace (first + 1)).seen at recorded
  exact stable_seen_mono next mode trace cutoff period stable (early := first + 1) (late := last)
    (by omega) (by omega) recorded

theorem finite_monitor_reports_iff (next : S → List S) (mode : Mode) (initial : S)
    (finite : (visited next mode.schedule initial).Finite) :
    (∃ turn, claimsAt next mode (run next mode.schedule initial) turn = true) ↔
      Nonterminating next mode.schedule initial := by
  constructor
  · rintro ⟨turn, claim⟩
    exact claimsAt_sound next mode initial turn claim
  · intro infinite
    obtain ⟨cutoff, period, positive, stable⟩ := mode_period_stabilizes next mode initial finite infinite
    have recordsStable : ∀ turn, cutoff ≤ turn →
        (recordPrefix next mode (run next mode.schedule initial) turn).period = period := by
      intro turn after
      rw [recordPrefix_period]
      exact stable turn after
    obtain ⟨first, last, state, past, order, previous, current, phase⟩ :=
      finite_phase_return_after next mode.schedule initial finite infinite period cutoff positive
    refine ⟨last, (claimsAt_iff next mode _ last).mpr ⟨state, current, ?_⟩⟩
    rw [recordsStable last (by omega), ← phase]
    exact stable_record_covers next mode _ cutoff period recordsStable past order previous

def reportedBy (next : S → List S) (mode : Mode) (trace : Nat → Option S) (horizon : Nat) : Bool :=
  (List.range horizon).any (claimsAt next mode trace)

theorem reportedBy_iff (next : S → List S) (mode : Mode) (trace : Nat → Option S) (horizon : Nat) :
    reportedBy next mode trace horizon = true ↔ ∃ turn, turn < horizon ∧ claimsAt next mode trace turn = true := by
  simp only [reportedBy, List.any_eq_true, List.mem_range]

theorem finite_eventually_reports_iff (next : S → List S) (mode : Mode) (initial : S)
    (finite : (visited next mode.schedule initial).Finite) :
    (∃ horizon, reportedBy next mode (run next mode.schedule initial) horizon = true) ↔
      Nonterminating next mode.schedule initial := by
  rw [← finite_monitor_reports_iff next mode initial finite]
  constructor
  · rintro ⟨horizon, report⟩
    obtain ⟨turn, _, claim⟩ := (reportedBy_iff next mode _ horizon).mp report
    exact ⟨turn, claim⟩
  · rintro ⟨turn, claim⟩
    exact ⟨turn + 1, (reportedBy_iff next mode _ _).mpr ⟨turn, Nat.lt_succ_self _, claim⟩⟩

end Mettapedia.Machines.ScheduledRun
