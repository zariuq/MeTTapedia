import Mettapedia.GSLT.Core.AgeProtectedSchedule
import Mettapedia.GSLT.Core.BranchingTemporal
import Mettapedia.GSLT.Core.ObservationDemandControl

/-!
# Bounded selection

A demand for `k` answers is a finite-prefix readout.  One bounded run stops
for exactly one of three reasons:

* `k` answers have been emitted (established);
* the frontier closes with fewer than `k` answers (saturation);
* the budget is spent while the frontier is still live (incomplete).

Saturation is a complete count.  An incomplete run does not say how many
answers exist.  Emitted answers are occurrence prefixes of a completed run
whenever a finite descent certificate supplies that completed bag.  A fair
schedule emits `k` answers whenever `k` emitting nodes are generated.
An age-protected portfolio does the same for emitting roots.
Depth-first scheduling on a recursive-first generator emits none.
-/

namespace Mettapedia.GSLT.Core.BoundedSelection

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.WeightedOccurrenceControl
open Mettapedia.GSLT.Core.AgeProtectedSchedule
open Mettapedia.GSLT.Core.ObservationDemandControl

universe uNode uAnswer

/-- The three ways a demand for `k` answers can stop. -/
inductive SelectOutcome where
  | established
  | saturated
  | incomplete
deriving DecidableEq, Repr

/-- Classify an occurrence count and an independently supplied closure
readout. A caller with parked obligations must include them in that readout;
an empty runnable queue alone is insufficient evidence of closure. -/
def outcomeFromCounts (requested completed : Nat) (closed : Bool) : SelectOutcome :=
  if requested ≤ completed then .established
  else if closed then .saturated
  else .incomplete

theorem outcomeFromCounts_established_iff (requested completed : Nat) (closed : Bool) :
    outcomeFromCounts requested completed closed = .established ↔ requested ≤ completed := by
  by_cases enough : requested ≤ completed <;>
    cases closed <;> simp [outcomeFromCounts, enough]

theorem outcomeFromCounts_saturated_iff (requested completed : Nat) (closed : Bool) :
    outcomeFromCounts requested completed closed = .saturated ↔
      completed < requested ∧ closed = true := by
  by_cases enough : requested ≤ completed <;>
    cases closed <;> simp [outcomeFromCounts, enough, Nat.lt_of_not_ge, Nat.not_lt.mpr]

theorem outcomeFromCounts_incomplete_iff (requested completed : Nat) (closed : Bool) :
    outcomeFromCounts requested completed closed = .incomplete ↔
      completed < requested ∧ closed = false := by
  by_cases enough : requested ≤ completed <;>
    cases closed <;> simp [outcomeFromCounts, enough, Nat.lt_of_not_ge, Nat.not_lt.mpr]

/-- Classify a snapshot against a demand `k`. Finding `k` takes precedence
over closure, so a frontier that closes with exactly `k` answers is
established. Saturation is closure with strictly fewer. -/
def outcome {Node : Type uNode} {Answer : Type uAnswer}
    (k : Nat) (snapshot : Snapshot Node Answer) : SelectOutcome :=
  outcomeFromCounts k snapshot.events.length snapshot.frontier.isEmpty

/-- Continue while fewer than `k` answers have been emitted and work remains. -/
def stillOpen {Node : Type uNode} {Answer : Type uAnswer}
    (k : Nat) (snapshot : Snapshot Node Answer) : Bool :=
  decide (snapshot.events.length < k) && !snapshot.frontier.isEmpty

theorem stillOpen_iff {Node : Type uNode} {Answer : Type uAnswer}
    (k : Nat) (snapshot : Snapshot Node Answer) :
    stillOpen k snapshot = true ↔
      snapshot.events.length < k ∧ snapshot.frontier ≠ [] := by
  cases hfrontier : snapshot.frontier with
  | nil => simp [stillOpen, hfrontier]
  | cons head tail => simp [stillOpen, hfrontier, decide_eq_true_eq]

theorem stillOpen_false_iff {Node : Type uNode} {Answer : Type uAnswer}
    (k : Nat) (snapshot : Snapshot Node Answer) :
    stillOpen k snapshot = false ↔
      k ≤ snapshot.events.length ∨ snapshot.frontier = [] := by
  cases hfrontier : snapshot.frontier with
  | nil => simp [stillOpen, hfrontier]
  | cons head tail =>
      simp [stillOpen, hfrontier, decide_eq_false_iff_not]

private theorem eq_false_of_ne_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp_all

/-- One scheduler step appends no event, or exactly the selected emission. -/
theorem tick_events {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (snapshot : Snapshot Node Answer) :
    (tick system scheduler snapshot).events =
      snapshot.events ++
        match scheduler.reorder snapshot.frontier with
        | [] => []
        | node :: _ =>
            match system.emit node with
            | none => []
            | some answer => [⟨node, answer⟩] := by
  cases h : scheduler.reorder snapshot.frontier with
  | nil => simp [tick, h]
  | cons node pending =>
      cases e : system.emit node with
      | none =>
          simp [tick, h, e]
          rfl
      | some answer =>
          simp [tick, h, e]
          rfl

theorem tick_events_length_le {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (snapshot : Snapshot Node Answer) :
    (tick system scheduler snapshot).events.length ≤
      snapshot.events.length + 1 := by
  rw [tick_events]
  cases h : scheduler.reorder snapshot.frontier with
  | nil => simp
  | cons node pending =>
      cases e : system.emit node with
      | none => simp [e]
      | some answer => simp [e, List.length_append]

/-- Observe at most `fuel` scheduler steps, stopping at `k` answers or at
an empty frontier. -/
def boundedRun {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (k : Nat) : Nat → Snapshot Node Answer → Snapshot Node Answer
  | 0, snapshot => snapshot
  | fuel + 1, snapshot =>
      let stepped := boundedRun system scheduler k fuel snapshot
      if stillOpen k stepped then tick system scheduler stepped else stepped

theorem boundedRun_zero {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (k : Nat) (snapshot : Snapshot Node Answer) :
    boundedRun system scheduler k 0 snapshot = snapshot := rfl

theorem boundedRun_succ {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (k fuel : Nat) (snapshot : Snapshot Node Answer) :
    boundedRun system scheduler k (fuel + 1) snapshot =
      let stepped := boundedRun system scheduler k fuel snapshot
      if stillOpen k stepped then tick system scheduler stepped else stepped := rfl

/-! ## The three outcomes partition every snapshot -/

theorem outcome_established_iff {Node : Type uNode} {Answer : Type uAnswer}
    (k : Nat) (snapshot : Snapshot Node Answer) :
    outcome k snapshot = .established ↔ k ≤ snapshot.events.length := by
  unfold outcome outcomeFromCounts
  by_cases hk : k ≤ snapshot.events.length
  · simp [hk]
  · simp [hk]
    cases snapshot.frontier <;> simp

theorem outcome_saturated_iff {Node : Type uNode} {Answer : Type uAnswer}
    (k : Nat) (snapshot : Snapshot Node Answer) :
    outcome k snapshot = .saturated ↔
      snapshot.events.length < k ∧ snapshot.frontier = [] := by
  unfold outcome outcomeFromCounts
  by_cases hk : k ≤ snapshot.events.length
  · simp [hk, Nat.not_lt.mpr hk]
  · simp [hk, Nat.lt_of_not_ge hk]

theorem outcome_incomplete_iff {Node : Type uNode} {Answer : Type uAnswer}
    (k : Nat) (snapshot : Snapshot Node Answer) :
    outcome k snapshot = .incomplete ↔
      snapshot.events.length < k ∧ snapshot.frontier ≠ [] := by
  unfold outcome outcomeFromCounts
  by_cases hk : k ≤ snapshot.events.length
  · simp [hk, Nat.not_lt.mpr hk]
  · simp [hk, Nat.lt_of_not_ge hk]

/-- The established, saturated, and incomplete readings are exhaustive. -/
theorem outcomes_exhaustive {Node : Type uNode} {Answer : Type uAnswer}
    (k : Nat) (snapshot : Snapshot Node Answer) :
    outcome k snapshot = .established ∨
      outcome k snapshot = .saturated ∨
        outcome k snapshot = .incomplete := by
  by_cases hk : k ≤ snapshot.events.length
  · exact Or.inl ((outcome_established_iff k snapshot).mpr hk)
  · by_cases hempty : snapshot.frontier = []
    · exact Or.inr <| Or.inl <|
        (outcome_saturated_iff k snapshot).mpr ⟨Nat.lt_of_not_ge hk, hempty⟩
    · exact Or.inr <| Or.inr <|
        (outcome_incomplete_iff k snapshot).mpr ⟨Nat.lt_of_not_ge hk, hempty⟩

/-- No snapshot carries two of the three outcomes. -/
theorem outcomes_mutually_exclusive {Node : Type uNode} {Answer : Type uAnswer}
    (k : Nat) (snapshot : Snapshot Node Answer) :
    ¬ (outcome k snapshot = .established ∧ outcome k snapshot = .saturated) ∧
      ¬ (outcome k snapshot = .established ∧ outcome k snapshot = .incomplete) ∧
        ¬ (outcome k snapshot = .saturated ∧ outcome k snapshot = .incomplete) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨he, hs⟩
    have hle := (outcome_established_iff k snapshot).mp he
    have ⟨hlt, _⟩ := (outcome_saturated_iff k snapshot).mp hs
    exact Nat.not_lt.mpr hle hlt
  · rintro ⟨he, hi⟩
    have hle := (outcome_established_iff k snapshot).mp he
    have ⟨hlt, _⟩ := (outcome_incomplete_iff k snapshot).mp hi
    exact Nat.not_lt.mpr hle hlt
  · rintro ⟨hs, hi⟩
    have ⟨_, hempty⟩ := (outcome_saturated_iff k snapshot).mp hs
    have ⟨_, hne⟩ := (outcome_incomplete_iff k snapshot).mp hi
    exact hne hempty

/-- A bounded run that is still accepting work has taken every step of the
unbounded run. -/
theorem bounded_eq_run_while_open {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (k fuel : Nat) (snapshot : Snapshot Node Answer)
    (hop : stillOpen k (boundedRun system scheduler k fuel snapshot) = true) :
    boundedRun system scheduler k fuel snapshot =
      run system scheduler fuel snapshot := by
  induction fuel generalizing snapshot with
  | zero => rfl
  | succ fuel ih =>
      have hprev : stillOpen k (boundedRun system scheduler k fuel snapshot) = true := by
        by_contra hnot
        have hf := eq_false_of_ne_true hnot
        have hstuck :
            boundedRun system scheduler k (fuel + 1) snapshot =
              boundedRun system scheduler k fuel snapshot := by
          simp only [boundedRun_succ, hf, if_neg Bool.false_ne_true]
        rw [hstuck] at hop
        exact Bool.false_ne_true (hf.symm.trans hop)
      have heq := ih snapshot hprev
      have hopenRun : stillOpen k (run system scheduler fuel snapshot) = true := by
        simpa [heq] using hprev
      simp only [boundedRun_succ, run, heq, hopenRun, ite_true]

theorem bounded_events_prefix_run {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (k fuel : Nat) (snapshot : Snapshot Node Answer) :
    (boundedRun system scheduler k fuel snapshot).events.IsPrefix
      (run system scheduler fuel snapshot).events := by
  induction fuel generalizing snapshot with
  | zero => simp [boundedRun, run]
  | succ fuel ih =>
      by_cases hop : stillOpen k (boundedRun system scheduler k fuel snapshot) = true
      · have heq := bounded_eq_run_while_open system scheduler k fuel snapshot hop
        have hopenRun : stillOpen k (run system scheduler fuel snapshot) = true := by
          simpa [heq] using hop
        simp only [boundedRun_succ, run, heq, hopenRun, ite_true]
        exact List.prefix_rfl
      · have hf := eq_false_of_ne_true hop
        simp only [boundedRun_succ, run, hf]
        exact (ih snapshot).trans
          (events_prefix_tick system scheduler (run system scheduler fuel snapshot))

theorem bounded_length_le {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (k fuel : Nat) (snapshot : Snapshot Node Answer)
    (hstart : snapshot.events.length ≤ k) :
    (boundedRun system scheduler k fuel snapshot).events.length ≤ k := by
  induction fuel generalizing snapshot with
  | zero => simpa [boundedRun] using hstart
  | succ fuel ih =>
      by_cases hop : stillOpen k (boundedRun system scheduler k fuel snapshot) = true
      · have hlt : (boundedRun system scheduler k fuel snapshot).events.length < k :=
          (stillOpen_iff k _).mp hop |>.1
        simp only [boundedRun_succ, hop, ite_true]
        exact (tick_events_length_le system scheduler _).trans (Nat.succ_le_of_lt hlt)
      · have hf := eq_false_of_ne_true hop
        simp only [boundedRun_succ, hf]
        exact ih snapshot hstart

theorem bounded_eq_run_of_short {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (k fuel : Nat) (snapshot : Snapshot Node Answer)
    (hshort : (run system scheduler fuel snapshot).events.length < k) :
    boundedRun system scheduler k fuel snapshot = run system scheduler fuel snapshot := by
  induction fuel generalizing snapshot with
  | zero => rfl
  | succ fuel ih =>
      have hprefix :
          (run system scheduler fuel snapshot).events.IsPrefix
            (run system scheduler (fuel + 1) snapshot).events := by
        rw [run]
        exact events_prefix_tick system scheduler _
      have hprev : (run system scheduler fuel snapshot).events.length < k :=
        Nat.lt_of_le_of_lt hprefix.length_le hshort
      have heq := ih snapshot hprev
      rw [run, boundedRun_succ, heq]
      by_cases hempty : (run system scheduler fuel snapshot).frontier = []
      · have hclosed :
            tick system scheduler (run system scheduler fuel snapshot) =
              run system scheduler fuel snapshot :=
          tick_eq_self_of_frontier_nil system scheduler _ hempty
        have hnot : stillOpen k (run system scheduler fuel snapshot) = false := by
          rw [stillOpen_false_iff]
          exact Or.inr hempty
        simp [hnot, hclosed]
      · have hopen : stillOpen k (run system scheduler fuel snapshot) = true :=
          (stillOpen_iff k _).mpr ⟨hprev, hempty⟩
        simp [hopen]

/-- Once an unbounded run has emitted `k` answers, the bounded run has too. -/
theorem bounded_reaches_count {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (k fuel : Nat) (snapshot : Snapshot Node Answer)
    (hk : k ≤ (run system scheduler fuel snapshot).events.length) :
    k ≤ (boundedRun system scheduler k fuel snapshot).events.length := by
  induction fuel generalizing snapshot with
  | zero => simpa [run, boundedRun] using hk
  | succ fuel ih =>
      by_cases hshort : (run system scheduler fuel snapshot).events.length < k
      · have heq := bounded_eq_run_of_short system scheduler k fuel snapshot hshort
        have hgrew :
            (run system scheduler fuel snapshot).events.length <
              (run system scheduler (fuel + 1) snapshot).events.length :=
          Nat.lt_of_lt_of_le hshort hk
        have hempty : (run system scheduler fuel snapshot).frontier ≠ [] := by
          intro hempty
          have hstuck := tick_eq_self_of_frontier_nil system scheduler
            (run system scheduler fuel snapshot) hempty
          have hsame : run system scheduler (fuel + 1) snapshot =
              run system scheduler fuel snapshot := by
            rw [run, hstuck]
          rw [hsame] at hgrew
          exact Nat.lt_irrefl _ hgrew
        have hopen : stillOpen k (run system scheduler fuel snapshot) = true :=
          (stillOpen_iff k _).mpr ⟨hshort, hempty⟩
        simp only [boundedRun_succ, heq, hopen, ite_true]
        exact hk
      · have hkPrev : k ≤ (run system scheduler fuel snapshot).events.length :=
          Nat.le_of_not_lt hshort
        by_cases hop : stillOpen k (boundedRun system scheduler k fuel snapshot) = true
        · simp only [boundedRun_succ, hop, ite_true]
          exact le_trans (ih snapshot hkPrev)
            (events_prefix_tick system scheduler _).length_le
        · have hf := eq_false_of_ne_true hop
          simp only [boundedRun_succ, hf]
          exact ih snapshot hkPrev

/-! ## Soundness against a completed occurrence bag -/

theorem bounded_sound {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (roots : List Node) (k fuel : Nat) :
    (boundedRun system scheduler k fuel (initial roots)).Sound system roots := by
  induction fuel with
  | zero => simpa [boundedRun, initial] using initial_sound system roots
  | succ fuel ih =>
      by_cases hop : stillOpen k (boundedRun system scheduler k fuel (initial roots)) = true
      · simp only [boundedRun_succ, hop, ite_true]
        exact sound_tick system scheduler ih
      · have hf := eq_false_of_ne_true hop
        simp only [boundedRun_succ, hf]
        exact ih

theorem run_events_prefix_add {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (left right : Nat) (snapshot : Snapshot Node Answer) :
    (run system scheduler left snapshot).events.IsPrefix
      (run system scheduler (left + right) snapshot).events := by
  rw [run_add]
  exact events_prefix_run system scheduler right _

theorem bounded_events_prefix_completed {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (certificate : DescentCertificate system) (roots : List Node)
    (k fuel : Nat) :
    (boundedRun system scheduler k fuel (initial roots)).events.IsPrefix
      (run system scheduler (foldRanks certificate.rank roots) (initial roots)).events := by
  let completionFuel := foldRanks certificate.rank roots
  have hcomplete :
      (run system scheduler completionFuel (initial roots)).frontier = [] :=
    run_completes_at_rank system scheduler certificate (initial roots)
  by_cases hle : fuel ≤ completionFuel
  · obtain ⟨extra, heq⟩ := Nat.le.dest hle
    have hprefix :=
      (bounded_events_prefix_run system scheduler k fuel (initial roots)).trans
        (run_events_prefix_add system scheduler fuel extra (initial roots))
    simpa [heq] using hprefix
  · have hge : completionFuel ≤ fuel := Nat.le_of_not_ge hle
    obtain ⟨extra, heq⟩ := Nat.le.dest hge
    have hprefix := bounded_events_prefix_run system scheduler k fuel (initial roots)
    have hrun :
        run system scheduler fuel (initial roots) =
          run system scheduler completionFuel (initial roots) := by
      rw [← heq, run_add]
      exact run_eq_self_of_frontier_nil system scheduler _ hcomplete extra
    simpa [hrun] using hprefix

theorem emissionList_sub_of_prefix {Node : Type uNode} {Answer : Type uAnswer}
    {left right : List (Emission Node Answer)} (h : left.IsPrefix right) :
    (left : Multiset (Emission Node Answer)) ≤ right := by
  obtain ⟨suffix, hsuffix⟩ := h
  rw [← hsuffix]
  exact (Multiset.coe_le).mpr (List.sublist_append_left left suffix).subperm

/-- Emitted answers are an occurrence sub-bag of the completed run. -/
theorem emitted_occurrence_sub_bag {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (certificate : DescentCertificate system) (roots : List Node)
    (k fuel : Nat) :
    ((boundedRun system scheduler k fuel (initial roots)).events :
        Multiset (Emission Node Answer)) ≤
      (run system scheduler (foldRanks certificate.rank roots) (initial roots)).events :=
  emissionList_sub_of_prefix
    (bounded_events_prefix_completed system scheduler certificate roots k fuel)

theorem eventBag_card {Node : Type uNode} {Answer : Type uAnswer}
    (events : List (Emission Node Answer)) :
    (eventBag events).card = events.length := by
  simp [eventBag, Multiset.coe_card, List.length_map]

theorem account_bounded {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (denotation : AdditiveDenotation system) (k fuel : Nat)
    (snapshot : Snapshot Node Answer) :
    account denotation (boundedRun system scheduler k fuel snapshot) =
      account denotation snapshot := by
  induction fuel generalizing snapshot with
  | zero => rfl
  | succ fuel ih =>
      by_cases hop : stillOpen k (boundedRun system scheduler k fuel snapshot) = true
      · simp only [boundedRun_succ, hop, ite_true]
        exact (account_tick system scheduler denotation _).trans (ih snapshot)
      · have hf := eq_false_of_ne_true hop
        simp only [boundedRun_succ, hf]
        exact ih snapshot

/-- Closure, with or without having reached `k`, equates the emitted
occurrence count with the additive denotation. -/
theorem closure_counts {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (denotation : AdditiveDenotation system) (roots : List Node)
    (k fuel : Nat)
    (closed : (boundedRun system scheduler k fuel (initial roots)).frontier = []) :
    (foldValues denotation.value roots).card =
      (boundedRun system scheduler k fuel (initial roots)).events.length := by
  have preserved := account_bounded system scheduler denotation k fuel (initial roots)
  change (boundedRun system scheduler k fuel
      ({ events := [], frontier := roots } : Snapshot Node Answer)).frontier = [] at closed
  simp only [account, initial] at preserved
  rw [closed] at preserved
  have sameBag :
      foldValues denotation.value roots =
        eventBag (boundedRun system scheduler k fuel
          ({ events := [], frontier := roots } : Snapshot Node Answer)).events := by
    simpa [foldValues, eventBag] using preserved.symm
  simpa [eventBag_card, initial] using congrArg Multiset.card sameBag

/-- Saturation certifies that the complete bag has exactly the emitted count. -/
theorem saturation_exact {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (denotation : AdditiveDenotation system) (roots : List Node)
    (k fuel : Nat)
    (saturated :
      outcome k (boundedRun system scheduler k fuel (initial roots)) = .saturated) :
    (boundedRun system scheduler k fuel (initial roots)).events.length < k ∧
      (foldValues denotation.value roots).card =
        (boundedRun system scheduler k fuel (initial roots)).events.length := by
  have ⟨hlt, hempty⟩ := (outcome_saturated_iff k _).mp saturated
  exact ⟨hlt, closure_counts system scheduler denotation roots k fuel hempty⟩

theorem established_exact {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (k fuel : Nat) (snapshot : Snapshot Node Answer)
    (hstart : snapshot.events.length ≤ k)
    (established : outcome k (boundedRun system scheduler k fuel snapshot) = .established) :
    (boundedRun system scheduler k fuel snapshot).events.length = k := by
  have hle := bounded_length_le system scheduler k fuel snapshot hstart
  have hge := (outcome_established_iff k _).mp established
  omega

/-! ## Fair schedules emit k -/

private theorem exists_mem_split {α : Type _} {a : α} {l : List α} (h : a ∈ l) :
    ∃ s t, l = s ++ a :: t := by
  induction l with
  | nil => cases h
  | cons head tail ih =>
      cases h with
      | head => exact ⟨[], tail, rfl⟩
      | tail _ htail =>
          obtain ⟨s, t, rfl⟩ := ih htail
          exact ⟨head :: s, t, rfl⟩

private theorem distinct_origins_length {Node : Type uNode} {Answer : Type uAnswer}
    (events : List (Emission Node Answer)) (answers : List Node)
    (nodup : answers.Nodup)
    (witness : ∀ node ∈ answers, ∃ answer,
      (⟨node, answer⟩ : Emission Node Answer) ∈ events) :
    answers.length ≤ events.length := by
  induction answers generalizing events with
  | nil => simp
  | cons node rest ih =>
      obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp nodup
      obtain ⟨answer, hmem⟩ := witness node (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨s, t, rfl⟩ := exists_mem_split hmem
      have witnessRest : ∀ x ∈ rest, ∃ ans,
          (⟨x, ans⟩ : Emission Node Answer) ∈ s ++ t := by
        intro x hx
        obtain ⟨ans, hitem⟩ := witness x (List.mem_cons.mpr (Or.inr hx))
        have xne : x ≠ node := by
          intro heq
          exact hnot (heq ▸ hx)
        rcases List.mem_append.mp hitem with hs | ht
        · exact ⟨ans, List.mem_append_left _ hs⟩
        · rcases List.mem_cons.mp ht with heq | ht
          · exact absurd (congrArg Emission.origin heq) xne
          · exact ⟨ans, List.mem_append_right _ ht⟩
      have ihlen := ih (s ++ t) hrest witnessRest
      simp only [List.length_cons, List.length_append] at ihlen ⊢
      omega

private theorem gathered_emissions {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (roots : List Node) (answers : List Node)
    (each : ∀ node ∈ answers, ∃ answer fuel,
      (⟨node, answer⟩ : Emission Node Answer) ∈
        (run system scheduler fuel (initial roots)).events) :
    ∃ fuel, ∀ node ∈ answers, ∃ answer,
      (⟨node, answer⟩ : Emission Node Answer) ∈
        (run system scheduler fuel (initial roots)).events := by
  induction answers with
  | nil => exact ⟨0, by simp⟩
  | cons node rest ih =>
      obtain ⟨answer, fuelNode, hnode⟩ := each node (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨fuelRest, hrest⟩ := ih fun item member =>
        each item (List.mem_cons.mpr (Or.inr member))
      obtain ⟨extraNode, heqNode⟩ := Nat.le.dest (Nat.le_max_left fuelNode fuelRest)
      obtain ⟨extraRest, heqRest⟩ := Nat.le.dest (Nat.le_max_right fuelNode fuelRest)
      refine ⟨max fuelNode fuelRest, ?_⟩
      intro item hitem
      rcases List.mem_cons.mp hitem with rfl | hitem
      · refine ⟨answer, ?_⟩
        have hmem := List.IsPrefix.mem hnode
          (run_events_prefix_add system scheduler fuelNode extraNode (initial roots))
        simpa [heqNode] using hmem
      · obtain ⟨ans, hmem0⟩ := hrest item hitem
        have hmem := List.IsPrefix.mem hmem0
          (run_events_prefix_add system scheduler fuelRest extraRest (initial roots))
        exact ⟨ans, by simpa [heqRest] using hmem⟩

/-- A fair scheduler eventually emits `k` answers whenever `k` distinct
emitting nodes are generated.  Breadth-first traversal is the age lane, so
this is the liveness law of that lane. -/
theorem fair_bounded_emits {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (roots : List Node) (fair : FairFrom system scheduler roots)
    (answers : List Node) (k : Nat)
    (hk : k ≤ answers.length) (nodup : answers.Nodup)
    (generated : ∀ node ∈ answers, Generated system roots node)
    (emits : ∀ node ∈ answers, ∃ answer, system.emit node = some answer) :
    ∃ fuel,
      k ≤ (boundedRun system scheduler k fuel (initial roots)).events.length := by
  have each : ∀ node ∈ answers, ∃ answer fuel,
      (⟨node, answer⟩ : Emission Node Answer) ∈
        (run system scheduler fuel (initial roots)).events := by
    intro node member
    obtain ⟨answer, hemits⟩ := emits node member
    obtain ⟨fuel, hmem⟩ :=
      fair_emits_reachable system scheduler roots fair (generated node member) hemits
    exact ⟨answer, fuel, hmem⟩
  obtain ⟨fuel, hall⟩ := gathered_emissions system scheduler roots answers each
  have hcount : answers.length ≤
      (run system scheduler fuel (initial roots)).events.length :=
    distinct_origins_length _ answers nodup fun node member => hall node member
  exact ⟨fuel, bounded_reaches_count system scheduler k fuel (initial roots)
    (Nat.le_trans hk hcount)⟩

/-- The breadth-first age lane is fair, so the bounded run emits `k`. -/
theorem breadthFirst_bounded_emits {Node : Type uNode} {Answer : Type uAnswer}
    [DecidableEq Node]
    (system : BranchingSystem Node Answer) (roots : List Node)
    (answers : List Node) (k : Nat)
    (hk : k ≤ answers.length) (nodup : answers.Nodup)
    (generated : ∀ node ∈ answers, Generated system roots node)
    (emits : ∀ node ∈ answers, ∃ answer, system.emit node = some answer) :
    ∃ fuel,
      k ≤ (boundedRun system Scheduler.breadthFirst k fuel (initial roots)).events.length :=
  fair_bounded_emits system Scheduler.breadthFirst roots
    (breadthFirst_fair system roots) answers k hk nodup generated emits

/-! ## Age-protected portfolios emit their roots -/

/-- Continue a portfolio while fewer than `k` answers have been emitted and
some occurrence is still live. -/
def scheduledStillOpen {Node Answer : Type*} {count : Nat}
    (k : Nat) (snapshot : PortfolioSnapshot Node Answer count) : Bool :=
  decide (snapshot.events.length < k) && !snapshot.frontier.live.isEmpty

theorem scheduledStillOpen_iff {Node Answer : Type*} {count : Nat}
    (k : Nat) (snapshot : PortfolioSnapshot Node Answer count) :
    scheduledStillOpen k snapshot = true ↔
      snapshot.events.length < k ∧ snapshot.frontier.live ≠ [] := by
  cases hlive : snapshot.frontier.live with
  | nil => simp [scheduledStillOpen, hlive]
  | cons head tail => simp [scheduledStillOpen, hlive, decide_eq_true_eq]

theorem scheduledStillOpen_false_iff {Node Answer : Type*} {count : Nat}
    (k : Nat) (snapshot : PortfolioSnapshot Node Answer count) :
    scheduledStillOpen k snapshot = false ↔
      k ≤ snapshot.events.length ∨ snapshot.frontier.live = [] := by
  cases hlive : snapshot.frontier.live with
  | nil => simp [scheduledStillOpen, hlive]
  | cons head tail =>
      simp [scheduledStillOpen, hlive, decide_eq_false_iff_not]

theorem tick_self_of_live_nil {Node Answer : Type*} {count : Nat}
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : PortfolioSnapshot Node Answer count)
    (hempty : snapshot.frontier.live = []) :
    PortfolioSnapshot.tick system disciplines snapshot = snapshot := by
  have hlen := (snapshot.frontier.queue_complete snapshot.cursor).length_eq
  have hqueue : snapshot.frontier.queues snapshot.cursor = [] :=
    List.length_eq_zero_iff.mp (by simpa [hempty] using hlen)
  simp [PortfolioSnapshot.tick, PortfolioFrontier.selected, hqueue]

/-- Observe at most `fuel` portfolio steps, stopping at `k` answers or at an
empty live store. -/
def demandRun {Node Answer : Type*} {count : Nat} [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node) (k : Nat) :
    Nat → PortfolioSnapshot Node Answer count → PortfolioSnapshot Node Answer count
  | 0, snapshot => snapshot
  | fuel + 1, snapshot =>
      let stepped := demandRun system disciplines k fuel snapshot
      if scheduledStillOpen k stepped then
        PortfolioSnapshot.tick system disciplines stepped
      else stepped

theorem demandRun_succ {Node Answer : Type*} {count : Nat}
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (k fuel : Nat) (snapshot : PortfolioSnapshot Node Answer count) :
    demandRun system disciplines k (fuel + 1) snapshot =
      let stepped := demandRun system disciplines k fuel snapshot
      if scheduledStillOpen k stepped then
        PortfolioSnapshot.tick system disciplines stepped
      else stepped := rfl

theorem demand_eq_run_while_open {Node Answer : Type*} {count : Nat}
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (k fuel : Nat) (snapshot : PortfolioSnapshot Node Answer count)
    (hop : scheduledStillOpen k (demandRun system disciplines k fuel snapshot) = true) :
    demandRun system disciplines k fuel snapshot =
      PortfolioSnapshot.run system disciplines fuel snapshot := by
  induction fuel generalizing snapshot with
  | zero => rfl
  | succ fuel ih =>
      cases hprev : scheduledStillOpen k (demandRun system disciplines k fuel snapshot) with
      | false =>
          have hstuck :
              demandRun system disciplines k (fuel + 1) snapshot =
                demandRun system disciplines k fuel snapshot := by
            simp only [demandRun_succ, hprev, if_neg Bool.false_ne_true]
          rw [hstuck] at hop
          exact False.elim (Bool.false_ne_true (hprev.symm.trans hop))
      | true =>
          have heq := ih snapshot hprev
          have hopenRun :
              scheduledStillOpen k
                (PortfolioSnapshot.run system disciplines fuel snapshot) = true := by
            simpa [heq] using hprev
          simp only [demandRun_succ, PortfolioSnapshot.run, heq, hopenRun, ite_true]

theorem demand_eq_run_of_short {Node Answer : Type*} {count : Nat}
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (k fuel : Nat) (snapshot : PortfolioSnapshot Node Answer count)
    (hshort :
      (PortfolioSnapshot.run system disciplines fuel snapshot).events.length < k) :
    demandRun system disciplines k fuel snapshot =
      PortfolioSnapshot.run system disciplines fuel snapshot := by
  induction fuel generalizing snapshot with
  | zero => rfl
  | succ fuel ih =>
      have hprefix :
          (PortfolioSnapshot.run system disciplines fuel snapshot).events.IsPrefix
            (PortfolioSnapshot.run system disciplines (fuel + 1) snapshot).events := by
        rw [PortfolioSnapshot.run]
        exact PortfolioSnapshot.events_prefix_tick system disciplines _
      have hprev :
          (PortfolioSnapshot.run system disciplines fuel snapshot).events.length < k :=
        Nat.lt_of_le_of_lt hprefix.length_le hshort
      have heq := ih snapshot hprev
      rw [PortfolioSnapshot.run, demandRun_succ, heq]
      by_cases hempty :
          (PortfolioSnapshot.run system disciplines fuel snapshot).frontier.live = []
      · have hclosed :
            PortfolioSnapshot.tick system disciplines
              (PortfolioSnapshot.run system disciplines fuel snapshot) =
            PortfolioSnapshot.run system disciplines fuel snapshot :=
          tick_self_of_live_nil system disciplines _ hempty
        have hnot :
            scheduledStillOpen k
              (PortfolioSnapshot.run system disciplines fuel snapshot) = false := by
          rw [scheduledStillOpen_false_iff]
          exact Or.inr hempty
        simp [hnot, hclosed]
      · have hopen :
            scheduledStillOpen k
              (PortfolioSnapshot.run system disciplines fuel snapshot) = true :=
          (scheduledStillOpen_iff k _).mpr ⟨hprev, hempty⟩
        simp [hopen]

/-- Once an unbounded portfolio run has emitted `k` answers, the bounded
portfolio run has too. -/
theorem demand_reaches_count {Node Answer : Type*} {count : Nat}
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (k fuel : Nat) (snapshot : PortfolioSnapshot Node Answer count)
    (hk : k ≤ (PortfolioSnapshot.run system disciplines fuel snapshot).events.length) :
    k ≤ (demandRun system disciplines k fuel snapshot).events.length := by
  induction fuel generalizing snapshot with
  | zero => simpa [PortfolioSnapshot.run, demandRun] using hk
  | succ fuel ih =>
      by_cases hshort :
          (PortfolioSnapshot.run system disciplines fuel snapshot).events.length < k
      · have heq := demand_eq_run_of_short system disciplines k fuel snapshot hshort
        have hgrew :
            (PortfolioSnapshot.run system disciplines fuel snapshot).events.length <
              (PortfolioSnapshot.run system disciplines (fuel + 1) snapshot).events.length :=
          Nat.lt_of_lt_of_le hshort hk
        have hempty :
            (PortfolioSnapshot.run system disciplines fuel snapshot).frontier.live ≠ [] := by
          intro hempty
          have hstuck := tick_self_of_live_nil system disciplines
            (PortfolioSnapshot.run system disciplines fuel snapshot) hempty
          have hsame :
              PortfolioSnapshot.run system disciplines (fuel + 1) snapshot =
                PortfolioSnapshot.run system disciplines fuel snapshot := by
            rw [PortfolioSnapshot.run, hstuck]
          rw [hsame] at hgrew
          exact Nat.lt_irrefl _ hgrew
        have hopen :
            scheduledStillOpen k
              (PortfolioSnapshot.run system disciplines fuel snapshot) = true :=
          (scheduledStillOpen_iff k _).mpr ⟨hshort, hempty⟩
        simp only [demandRun_succ, heq, hopen, ite_true]
        exact hk
      · have hkPrev :
            k ≤ (PortfolioSnapshot.run system disciplines fuel snapshot).events.length :=
          Nat.le_of_not_lt hshort
        by_cases hop :
            scheduledStillOpen k (demandRun system disciplines k fuel snapshot) = true
        · simp only [demandRun_succ, hop, ite_true]
          exact le_trans (ih snapshot hkPrev)
            (PortfolioSnapshot.events_prefix_tick system disciplines _).length_le
        · have hf := eq_false_of_ne_true hop
          simp only [demandRun_succ, hf]
          exact ih snapshot hkPrev

private theorem portfolio_events_prefix_run {Node Answer : Type*} {count : Nat}
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (fuel : Nat) (snapshot : PortfolioSnapshot Node Answer count) :
    snapshot.events.IsPrefix
      (PortfolioSnapshot.run system disciplines fuel snapshot).events := by
  induction fuel with
  | zero => simp [PortfolioSnapshot.run]
  | succ fuel ih =>
      simp only [PortfolioSnapshot.run]
      exact ih.trans (PortfolioSnapshot.events_prefix_tick system disciplines _)

private theorem portfolio_events_prefix_add {Node Answer : Type*} {count : Nat}
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (left right : Nat) (snapshot : PortfolioSnapshot Node Answer count) :
    (PortfolioSnapshot.run system disciplines left snapshot).events.IsPrefix
      (PortfolioSnapshot.run system disciplines (left + right) snapshot).events := by
  rw [PortfolioSnapshot.run_add]
  exact portfolio_events_prefix_run system disciplines right _

private theorem portfolio_tick_emit {Node Answer : Type*} {count : Nat}
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : PortfolioSnapshot Node Answer count) (node : Node) (answer : Answer)
    (hsel : snapshot.frontier.selected snapshot.cursor = some node)
    (hemits : system.emit node = some answer) :
    (PortfolioSnapshot.tick system disciplines snapshot).events =
      snapshot.events ++ [⟨node, answer⟩] := by
  simp [PortfolioSnapshot.tick, hsel, hemits]
  rfl

private theorem selected_emission_recorded {Node Answer : Type*} {count : Nat}
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (roots : List Node) (start : Fin count) (fuel : Nat) {node : Node} {answer : Answer}
    (hemits : system.emit node = some answer)
    (hsel : node ∈ (PortfolioSnapshot.run system disciplines fuel
      (PortfolioSnapshot.initial disciplines roots start)).selections) :
    (⟨node, answer⟩ : Emission Node Answer) ∈
      (PortfolioSnapshot.run system disciplines fuel
        (PortfolioSnapshot.initial disciplines roots start)).events := by
  induction fuel with
  | zero => simp [PortfolioSnapshot.run, PortfolioSnapshot.initial] at hsel
  | succ fuel ih =>
      simp only [PortfolioSnapshot.run] at hsel ⊢
      cases hstep : (PortfolioSnapshot.run system disciplines fuel
          (PortfolioSnapshot.initial disciplines roots start)).frontier.selected
          (PortfolioSnapshot.run system disciplines fuel
            (PortfolioSnapshot.initial disciplines roots start)).cursor with
      | none =>
          have htick :
              PortfolioSnapshot.tick system disciplines
                (PortfolioSnapshot.run system disciplines fuel
                  (PortfolioSnapshot.initial disciplines roots start)) =
                PortfolioSnapshot.run system disciplines fuel
                  (PortfolioSnapshot.initial disciplines roots start) := by
            simp [PortfolioSnapshot.tick, hstep]
          rw [htick] at hsel ⊢
          exact ih hsel
      | some chosen =>
          have hreceipt := PortfolioSnapshot.selection_receipt_tick system disciplines
            (PortfolioSnapshot.run system disciplines fuel
              (PortfolioSnapshot.initial disciplines roots start)) hstep
          rw [hreceipt] at hsel
          rcases List.mem_append.mp hsel with hprev | hnow
          · exact List.IsPrefix.mem (ih hprev)
              (PortfolioSnapshot.events_prefix_tick system disciplines _)
          · simp only [List.mem_singleton] at hnow
            subst hnow
            rw [portfolio_tick_emit system disciplines _ node answer hstep hemits]
            exact List.mem_append_right _ (by simp)

private theorem gathered_root_emissions {Node Answer : Type*} {count : Nat}
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (roots : List Node) (start : Fin count) (answers : List Node)
    (each : ∀ node ∈ answers, ∃ answer fuel,
      (⟨node, answer⟩ : Emission Node Answer) ∈
        (PortfolioSnapshot.run system disciplines fuel
          (PortfolioSnapshot.initial disciplines roots start)).events) :
    ∃ fuel, ∀ node ∈ answers, ∃ answer,
      (⟨node, answer⟩ : Emission Node Answer) ∈
        (PortfolioSnapshot.run system disciplines fuel
          (PortfolioSnapshot.initial disciplines roots start)).events := by
  induction answers with
  | nil => exact ⟨0, by simp⟩
  | cons node rest ih =>
      obtain ⟨answer, fuelNode, hnode⟩ := each node (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨fuelRest, hrest⟩ := ih fun item member =>
        each item (List.mem_cons.mpr (Or.inr member))
      obtain ⟨extraNode, heqNode⟩ := Nat.le.dest (Nat.le_max_left fuelNode fuelRest)
      obtain ⟨extraRest, heqRest⟩ := Nat.le.dest (Nat.le_max_right fuelNode fuelRest)
      refine ⟨max fuelNode fuelRest, ?_⟩
      intro item hitem
      rcases List.mem_cons.mp hitem with rfl | hitem
      · refine ⟨answer, ?_⟩
        have hmem := List.IsPrefix.mem hnode
          (portfolio_events_prefix_add system disciplines fuelNode extraNode _)
        simpa [heqNode] using hmem
      · obtain ⟨ans, hmem0⟩ := hrest item hitem
        have hmem := List.IsPrefix.mem hmem0
          (portfolio_events_prefix_add system disciplines fuelRest extraRest _)
        exact ⟨ans, by simpa [heqRest] using hmem⟩

/-- An age-protected schedule eventually emits `k` answers whenever `k`
distinct emitting roots are present.  The age lane is what supplies the
selection; the other lanes are not assumed fair. -/
theorem age_protected_bounded_emits {Node Answer : Type*} {count : Nat}
    [DecidableEq Node] [NeZero count]
    (schedule : Spec Node count) (system : BranchingSystem Node Answer)
    (roots : List Node) (start : Fin count) (answers : List Node) (k : Nat)
    (hk : k ≤ answers.length) (nodup : answers.Nodup)
    (rooted : ∀ node ∈ answers, node ∈ roots)
    (emits : ∀ node ∈ answers, ∃ answer, system.emit node = some answer) :
    ∃ fuel,
      k ≤ (demandRun system schedule.disciplines k fuel
        (schedule.initial (Answer := Answer) roots start)).events.length := by
  have each : ∀ node ∈ answers, ∃ answer fuel,
      (⟨node, answer⟩ : Emission Node Answer) ∈
        (PortfolioSnapshot.run system schedule.disciplines fuel
          (schedule.initial (Answer := Answer) roots start)).events := by
    intro node member
    obtain ⟨answer, hemits⟩ := emits node member
    obtain ⟨fuel, hsel⟩ := schedule.eventually_selects_root system roots start
      (rooted node member)
    exact ⟨answer, fuel, selected_emission_recorded system schedule.disciplines roots
      start fuel hemits hsel⟩
  obtain ⟨fuel, hall⟩ := gathered_root_emissions system schedule.disciplines roots
    start answers each
  have hcount : answers.length ≤
      (PortfolioSnapshot.run system schedule.disciplines fuel
        (schedule.initial (Answer := Answer) roots start)).events.length :=
    distinct_origins_length _ answers nodup fun node member => hall node member
  exact ⟨fuel, demand_reaches_count system schedule.disciplines k fuel _
    (Nat.le_trans hk hcount)⟩

/-- The age lane of a depth-biased portfolio emits the answer that pure
depth-first scheduling never reaches. -/
theorem age_lane_emits_starved_answer :
    ∃ fuel,
      1 ≤ (demandRun Starvation.system
        (depthBiased (Node := Starvation.Node) 1).disciplines 1 fuel
        ((depthBiased (Node := Starvation.Node) 1).initial
          (Answer := Nat) Starvation.roots 0)).events.length :=
  age_protected_bounded_emits
    (depthBiased (Node := Starvation.Node) 1) Starvation.system Starvation.roots 0
    [Starvation.Node.answer] 1 (by simp) (by simp) (by simp [Starvation.roots])
    (by
      intro node hmem
      simp only [List.mem_singleton] at hmem
      subst hmem
      exact ⟨42, by simp [Starvation.system]⟩)

/-- Pure depth-first scheduling emits nothing from the same roots. -/
theorem depth_first_bounded_misses_starved (fuel : Nat) :
    (boundedRun Starvation.system Scheduler.depthFirst 1 fuel
      (initial Starvation.roots)).events = [] := by
  have hfix := Starvation.depthFirst_run_fixed fuel
  have hpre := bounded_events_prefix_run Starvation.system Scheduler.depthFirst 1 fuel
    (initial Starvation.roots)
  have hlen := hpre.length_le
  rw [hfix] at hlen
  have hempty : (initial (Answer := Nat) Starvation.roots).events = [] := by
    simp [initial]
  rw [hempty] at hlen
  exact List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)

/-! ## A demand for `k` is a finite-prefix readout -/

/-- A positive finite-prefix demand is exactly the bound observed by a bounded
run: the readout is that count, and the activation stays controlled. -/
theorem finite_prefix_is_bounded_readout {Guard : Type _}
    (guard : Option Guard) (k : Nat) (hk : k ≠ 0) (batch : BatchAuthority) :
    dispatch ⟨.finitePrefix k, guard⟩ .general batch =
      { readout := .finitePrefix k, activation := .controlled } := by
  cases k with
  | zero => exact absurd rfl hk
  | succ _ => rfl

/-- A zero prefix does not start a bounded search. -/
theorem zero_prefix_does_not_search {Guard : Type _}
    (guard : Option Guard) (batch : BatchAuthority) :
    dispatch ⟨.finitePrefix 0, guard⟩ .general batch =
      { readout := .finitePrefix 0, activation := .none } := by
  rfl

/-! ## Recursive-first depth-first starvation -/

namespace RecFirst

inductive Node where
  | recur
  | base
deriving DecidableEq, Repr

def system : BranchingSystem Node Nat where
  emit
    | .recur => none
    | .base => some 1
  successors
    | .recur => [.recur, .base]
    | .base => []

def roots : List Node := [.recur]

theorem depthFirst_silent (fuel : Nat) :
    (run system Scheduler.depthFirst fuel (initial roots)).events = [] ∧
      ∃ tail, (run system Scheduler.depthFirst fuel (initial roots)).frontier =
        .recur :: tail := by
  induction fuel with
  | zero =>
      refine ⟨?_, [], ?_⟩
      · simp [run, initial]
      · simp [run, initial, roots]
  | succ fuel ih =>
      obtain ⟨hev, tail, hfront⟩ := ih
      have hsnap :
          run system Scheduler.depthFirst fuel (initial roots) =
            ⟨[], .recur :: tail⟩ := by
        cases hrun : run system Scheduler.depthFirst fuel (initial roots) with
        | mk ev fr =>
            have hev' : ev = [] := by simpa [hrun] using hev
            have hfr' : fr = .recur :: tail := by simpa [hrun] using hfront
            simp [hev', hfr']
      refine ⟨?_, .base :: tail, ?_⟩
      · rw [run, hsnap]
        rfl
      · rw [run, hsnap]
        rfl

theorem depthFirst_bounded_silent (k fuel : Nat) :
    (boundedRun system Scheduler.depthFirst k fuel (initial roots)).events = [] := by
  cases k with
  | zero =>
      induction fuel with
      | zero => rfl
      | succ fuel ih =>
          have hf : stillOpen 0
              (boundedRun system Scheduler.depthFirst 0 fuel (initial roots)) = false := by
            simp [stillOpen]
          simp only [boundedRun_succ, hf]
          exact ih
  | succ k =>
      have hshort :
          (run system Scheduler.depthFirst fuel (initial roots)).events.length < k + 1 := by
        simp [(depthFirst_silent fuel).1]
      simp [bounded_eq_run_of_short system Scheduler.depthFirst (k + 1) fuel
          (initial roots) hshort, (depthFirst_silent fuel).1]

/-- Depth-first scheduling keeps the recursive equation at the head, so the
base answer is never emitted. -/
theorem depthFirst_starves (k fuel : Nat) :
    (⟨.base, 1⟩ : Emission Node Nat) ∉
      (boundedRun system Scheduler.depthFirst k fuel (initial roots)).events := by
  simp [depthFirst_bounded_silent]

theorem base_generated : Generated system roots .base := by
  refine Generated.successor (parent := .recur) ?_ ?_
  · exact Generated.root (by simp [roots])
  · simp [system]

theorem breadthFirst_emits_base :
    (⟨.base, 1⟩ : Emission Node Nat) ∈
      (run system Scheduler.breadthFirst 3 (initial roots)).events := by
  decide

theorem breadthFirst_bounded_establishes :
    outcome 1 (boundedRun system Scheduler.breadthFirst 1 3 (initial roots)) =
      .established := by
  decide

end RecFirst

/-! ## Concrete controls for the three outcomes -/

namespace Controls

theorem budget_is_incomplete :
    let snap := boundedRun FiniteSearch.system Scheduler.breadthFirst 2 0
      (initial [FiniteSearch.twoAnswers])
    outcome 2 snap = .incomplete ∧
      snap.events.length = 0 ∧
      (FiniteSearch.denote FiniteSearch.twoAnswers).card = 2 := by
  refine ⟨?_, rfl, ?_⟩
  · decide
  · simp [FiniteSearch.twoAnswers, FiniteSearch.denote, Multiset.card_singleton]

theorem two_answers_saturate :
    outcome 3 (boundedRun FiniteSearch.system Scheduler.breadthFirst 3
        (FiniteSearch.nodeCount FiniteSearch.twoAnswers)
        (initial [FiniteSearch.twoAnswers])) = .saturated ∧
      (boundedRun FiniteSearch.system Scheduler.breadthFirst 3
        (FiniteSearch.nodeCount FiniteSearch.twoAnswers)
        (initial [FiniteSearch.twoAnswers])).events.length = 2 := by
  have hcomplete :=
    FiniteSearch.every_scheduler_completes Scheduler.breadthFirst FiniteSearch.twoAnswers
  have hdenote :=
    FiniteSearch.every_scheduler_emits_denotation Scheduler.breadthFirst
      FiniteSearch.twoAnswers
  have hcard : (FiniteSearch.denote FiniteSearch.twoAnswers).card = 2 := by
    simp [FiniteSearch.twoAnswers, FiniteSearch.denote, Multiset.card_singleton]
  have hlen :
      (run FiniteSearch.system Scheduler.breadthFirst
        (FiniteSearch.nodeCount FiniteSearch.twoAnswers)
        (initial [FiniteSearch.twoAnswers])).events.length = 2 := by
    have hc := congrArg Multiset.card hdenote
    simpa [eventBag_card, hcard] using hc
  have hshort :
      (run FiniteSearch.system Scheduler.breadthFirst
        (FiniteSearch.nodeCount FiniteSearch.twoAnswers)
        (initial [FiniteSearch.twoAnswers])).events.length < 3 := by
    omega
  have heq := bounded_eq_run_of_short FiniteSearch.system Scheduler.breadthFirst 3
    (FiniteSearch.nodeCount FiniteSearch.twoAnswers)
    (initial [FiniteSearch.twoAnswers]) hshort
  refine ⟨(outcome_saturated_iff 3 _).mpr ⟨by simpa [heq] using hshort,
      by simpa [heq] using hcomplete⟩, by simpa [heq] using hlen⟩

/-- Finding one answer does not say that the complete bag has only one. -/
theorem established_leaves_a_larger_bag :
    let snap := boundedRun FiniteSearch.system Scheduler.breadthFirst 1 2
      (initial [FiniteSearch.twoAnswers])
    outcome 1 snap = .established ∧
      snap.events.length = 1 ∧
      (FiniteSearch.denote FiniteSearch.twoAnswers).card = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · simp [FiniteSearch.twoAnswers, FiniteSearch.denote, Multiset.card_singleton]

end Controls
