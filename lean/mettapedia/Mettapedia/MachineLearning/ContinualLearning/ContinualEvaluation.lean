import Mathlib

/-!
# Continual evaluation and the stability gap

This file formalizes the finite metric core of De Lange, van de Ven, and
Tuytelaars, *Continual Evaluation for Lifelong Learning: Identifying the
Stability Gap* (ICLR 2023, arXiv:2205.13452).

The source's central methodological point is that evaluation only at task
boundaries can miss a transient loss of previously acquired performance.  We
make that boundary exact:

* enlarging an evaluation window can only decrease its minimum accuracy;
* enlarging an evaluation window can only increase its maximal observed drop;
* worst-case accuracy is bounded above by endpoint average accuracy when every
  historical minimum is bounded by the corresponding endpoint value;
* a finite trace can agree perfectly at both sampled endpoints while having a
  strict interior stability gap.

The definitions are independent of a particular learner or data set.  They can
therefore be used as trace obligations for predictive-coding, backpropagation,
or any other continual learner.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace ContinualEvaluation

noncomputable section

section Extrema

variable {Time : Type*}

/-- Minimum observed accuracy of one evaluation task on a nonempty finite
window. -/
def minimumAccuracy
    (accuracy : Time → ℝ) (window : Finset Time) (hne : window.Nonempty) : ℝ :=
  window.inf' hne accuracy

/-- Ordered pairs of observations in a linearly ordered evaluation window. -/
def orderedPairs [LinearOrder Time] (window : Finset Time) :
    Finset (Time × Time) :=
  (window ×ˢ window).filter fun pair => pair.1 < pair.2

/-- The maximal accuracy decrease between two ordered observations in a
nonempty set of ordered pairs. -/
def maximalDrop
    [LinearOrder Time]
    (accuracy : Time → ℝ)
    (window : Finset Time)
    (hne : (orderedPairs window).Nonempty) : ℝ :=
  (orderedPairs window).sup' hne fun pair =>
    accuracy pair.1 - accuracy pair.2

/-- The maximal accuracy increase between two ordered observations.  This is
the finite-window plasticity counterpart of `maximalDrop`. -/
def maximalIncrease
    [LinearOrder Time]
    (accuracy : Time → ℝ)
    (window : Finset Time)
    (hne : (orderedPairs window).Nonempty) : ℝ :=
  (orderedPairs window).sup' hne fun pair =>
    accuracy pair.2 - accuracy pair.1

theorem minimumAccuracy_le_observation
    (accuracy : Time → ℝ)
    (window : Finset Time)
    (hne : window.Nonempty)
    {time : Time}
    (htime : time ∈ window) :
    minimumAccuracy accuracy window hne ≤ accuracy time := by
  exact Finset.inf'_le accuracy htime

theorem minimumAccuracy_antitone
    (accuracy : Time → ℝ)
    {sampled full : Finset Time}
    (hsubset : sampled ⊆ full)
    (hsampled : sampled.Nonempty) :
    minimumAccuracy accuracy full (hsampled.mono hsubset) ≤
      minimumAccuracy accuracy sampled hsampled := by
  exact Finset.inf'_mono accuracy hsubset hsampled

theorem orderedPairs_mono
    [LinearOrder Time]
    {sampled full : Finset Time}
    (hsubset : sampled ⊆ full) :
    orderedPairs sampled ⊆ orderedPairs full := by
  intro pair hpair
  simp only [orderedPairs, Finset.mem_filter, Finset.mem_product] at hpair ⊢
  exact ⟨⟨hsubset hpair.1.1, hsubset hpair.1.2⟩, hpair.2⟩

theorem maximalDrop_mono
    [LinearOrder Time]
    (accuracy : Time → ℝ)
    {sampled full : Finset Time}
    (hsubset : sampled ⊆ full)
    (hsampled : (orderedPairs sampled).Nonempty) :
    maximalDrop accuracy sampled hsampled ≤
      maximalDrop accuracy full (hsampled.mono (orderedPairs_mono hsubset)) := by
  exact Finset.sup'_mono
    (fun pair => accuracy pair.1 - accuracy pair.2)
    (orderedPairs_mono hsubset) hsampled

theorem maximalIncrease_mono
    [LinearOrder Time]
    (accuracy : Time → ℝ)
    {sampled full : Finset Time}
    (hsubset : sampled ⊆ full)
    (hsampled : (orderedPairs sampled).Nonempty) :
    maximalIncrease accuracy sampled hsampled ≤
      maximalIncrease accuracy full
        (hsampled.mono (orderedPairs_mono hsubset)) := by
  exact Finset.sup'_mono
    (fun pair => accuracy pair.2 - accuracy pair.1)
    (orderedPairs_mono hsubset) hsampled

end Extrema

section WorstCaseAccuracy

variable {Task : Type*}

/-- Endpoint average accuracy for one current task and a finite set of previous
tasks.  The denominator is the total number of tasks. -/
def endpointAverageAccuracy
    (previous : Finset Task)
    (currentAccuracy : ℝ)
    (previousEndpointAccuracy : Task → ℝ) : ℝ :=
  (currentAccuracy + ∑ task ∈ previous, previousEndpointAccuracy task) /
    (previous.card + 1 : ℝ)

/-- Worst-case accuracy for one current task and a finite set of previous
tasks, using each previous task's historical minimum.  This is algebraically
the source's WC-ACC definition. -/
def worstCaseAccuracy
    (previous : Finset Task)
    (currentAccuracy : ℝ)
    (previousMinimumAccuracy : Task → ℝ) : ℝ :=
  (currentAccuracy + ∑ task ∈ previous, previousMinimumAccuracy task) /
    (previous.card + 1 : ℝ)

theorem worstCaseAccuracy_le_endpointAverageAccuracy
    (previous : Finset Task)
    (currentAccuracy : ℝ)
    (previousMinimumAccuracy previousEndpointAccuracy : Task → ℝ)
    (hminimum :
      ∀ task ∈ previous,
        previousMinimumAccuracy task ≤ previousEndpointAccuracy task) :
    worstCaseAccuracy previous currentAccuracy previousMinimumAccuracy ≤
      endpointAverageAccuracy previous currentAccuracy
        previousEndpointAccuracy := by
  unfold worstCaseAccuracy endpointAverageAccuracy
  apply div_le_div_of_nonneg_right
  · exact add_le_add_right (Finset.sum_le_sum hminimum) currentAccuracy
  · positivity

theorem worstCaseAccuracy_strict_lt_endpointAverageAccuracy
    (previous : Finset Task)
    (currentAccuracy : ℝ)
    (previousMinimumAccuracy previousEndpointAccuracy : Task → ℝ)
    (hminimum :
      ∀ task ∈ previous,
        previousMinimumAccuracy task ≤ previousEndpointAccuracy task)
    {witness : Task}
    (hwitness : witness ∈ previous)
    (hstrict :
      previousMinimumAccuracy witness < previousEndpointAccuracy witness) :
    worstCaseAccuracy previous currentAccuracy previousMinimumAccuracy <
      endpointAverageAccuracy previous currentAccuracy
        previousEndpointAccuracy := by
  unfold worstCaseAccuracy endpointAverageAccuracy
  apply div_lt_div_of_pos_right
  · apply add_lt_add_right
    exact Finset.sum_lt_sum hminimum ⟨witness, hwitness, hstrict⟩
  · positivity

end WorstCaseAccuracy

section SamplingCompleteness

variable {Time : Type*} [DecidableEq Time]

/-- A trace that is high at every sampled observation and low everywhere
else.  This supplies a general witness for the information lost by a strict
finite sampling window. -/
def hiddenGapTrace
    (sampled : Finset Time) (low high : ℝ) (time : Time) : ℝ :=
  if time ∈ sampled then high else low

theorem hiddenGapTrace_minimum_sampled
    (sampled : Finset Time)
    (hsampled : sampled.Nonempty)
    (low high : ℝ) :
    minimumAccuracy (hiddenGapTrace sampled low high)
        sampled hsampled = high := by
  apply le_antisymm
  · let time := hsampled.choose
    have htime : time ∈ sampled := hsampled.choose_spec
    simpa [hiddenGapTrace, htime] using
      minimumAccuracy_le_observation
        (hiddenGapTrace sampled low high) sampled hsampled htime
  · unfold minimumAccuracy
    apply Finset.le_inf' hsampled
    intro time htime
    simp [hiddenGapTrace, htime]

theorem hiddenGapTrace_minimum_full
    {sampled full : Finset Time}
    (hsubset : sampled ⊆ full)
    (hsampled : sampled.Nonempty)
    {missed : Time}
    (hmissed_full : missed ∈ full)
    (hmissed_sampled : missed ∉ sampled)
    {low high : ℝ}
    (hlow_high : low ≤ high) :
    minimumAccuracy (hiddenGapTrace sampled low high)
        full (hsampled.mono hsubset) = low := by
  apply le_antisymm
  · simpa [hiddenGapTrace, hmissed_sampled] using
      minimumAccuracy_le_observation
        (hiddenGapTrace sampled low high) full
        (hsampled.mono hsubset) hmissed_full
  · unfold minimumAccuracy
    apply Finset.le_inf' (hsampled.mono hsubset)
    intro time _
    by_cases htime : time ∈ sampled
    · simpa [hiddenGapTrace, htime] using hlow_high
    · simp [hiddenGapTrace, htime]

/-- Every strict finite sampling omission can hide any prescribed positive
gap.  The result is about observational sufficiency, not about how likely a
learner is to realize the witness trace. -/
theorem strict_sampling_can_hide_prescribed_gap
    {sampled full : Finset Time}
    (hsubset : sampled ⊆ full)
    (hsampled : sampled.Nonempty)
    {missed : Time}
    (hmissed_full : missed ∈ full)
    (hmissed_sampled : missed ∉ sampled)
    {low high : ℝ}
    (hlow_high : low < high) :
    minimumAccuracy (hiddenGapTrace sampled low high)
        full (hsampled.mono hsubset) <
      minimumAccuracy (hiddenGapTrace sampled low high)
        sampled hsampled := by
  rw [hiddenGapTrace_minimum_full hsubset hsampled hmissed_full
      hmissed_sampled hlow_high.le,
    hiddenGapTrace_minimum_sampled]
  exact hlow_high

omit [DecidableEq Time] in
/-- Negative boundary: a complete finite sample has no omitted observation
on which the hidden-gap construction could place its low value. -/
theorem complete_sampling_has_no_missed_observation
    {sampled full : Finset Time}
    (hcomplete : sampled = full) :
    ¬ ∃ missed, missed ∈ full ∧ missed ∉ sampled := by
  rintro ⟨missed, hmissed_full, hmissed_sampled⟩
  exact hmissed_sampled (hcomplete ▸ hmissed_full)

end SamplingCompleteness

section Fixtures

/-- A minimal stability-gap trace: perfect at both task-boundary samples, but
zero at the unobserved interior update. -/
def stabilityGapTrace : Fin 3 → ℝ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1

def endpointWindow : Finset (Fin 3) := {0, 2}

def continualWindow : Finset (Fin 3) := Finset.univ

theorem endpointWindow_nonempty : endpointWindow.Nonempty := by
  simp [endpointWindow]

theorem continualWindow_nonempty : continualWindow.Nonempty := by
  simp [continualWindow]

theorem endpointWindow_subset_continualWindow :
    endpointWindow ⊆ continualWindow := by
  simp [endpointWindow, continualWindow]

theorem endpoint_sampling_reports_perfect_minimum :
    minimumAccuracy stabilityGapTrace endpointWindow endpointWindow_nonempty =
      1 := by
  apply le_antisymm
  · exact minimumAccuracy_le_observation stabilityGapTrace endpointWindow
      endpointWindow_nonempty (by simp [endpointWindow] : (0 : Fin 3) ∈ endpointWindow)
  · unfold minimumAccuracy
    apply Finset.le_inf' endpointWindow_nonempty
    intro time htime
    have hcases : time = 0 ∨ time = 2 := by
      simpa [endpointWindow] using htime
    rcases hcases with rfl | rfl <;> norm_num [stabilityGapTrace]

theorem continual_sampling_exposes_zero_minimum :
    minimumAccuracy stabilityGapTrace continualWindow
      continualWindow_nonempty = 0 := by
  apply le_antisymm
  · exact minimumAccuracy_le_observation stabilityGapTrace continualWindow
      continualWindow_nonempty (by simp [continualWindow] : (1 : Fin 3) ∈ continualWindow)
  · unfold minimumAccuracy
    apply Finset.le_inf' continualWindow_nonempty
    intro time _
    fin_cases time <;> norm_num [stabilityGapTrace]

theorem endpoint_sampling_strictly_misses_stability_gap :
    minimumAccuracy stabilityGapTrace continualWindow
        continualWindow_nonempty <
      minimumAccuracy stabilityGapTrace endpointWindow
        endpointWindow_nonempty := by
  rw [continual_sampling_exposes_zero_minimum,
    endpoint_sampling_reports_perfect_minimum]
  norm_num

theorem endpointWindow_orderedPairs_nonempty :
    (orderedPairs endpointWindow).Nonempty := by
  refine ⟨((0 : Fin 3), (2 : Fin 3)), ?_⟩
  simp only [orderedPairs, Finset.mem_filter, Finset.mem_product]
  exact ⟨by simp [endpointWindow], by decide⟩

theorem continualWindow_orderedPairs_nonempty :
    (orderedPairs continualWindow).Nonempty := by
  refine ⟨((0 : Fin 3), (1 : Fin 3)), ?_⟩
  simp only [orderedPairs, Finset.mem_filter, Finset.mem_product]
  exact ⟨by simp [continualWindow], by decide⟩

theorem endpoint_sampling_reports_no_drop :
    maximalDrop stabilityGapTrace endpointWindow
      endpointWindow_orderedPairs_nonempty = 0 := by
  apply le_antisymm
  · unfold maximalDrop
    apply Finset.sup'_le endpointWindow_orderedPairs_nonempty
    rintro ⟨earlier, later⟩ hpair
    fin_cases earlier <;> fin_cases later <;>
      simp_all [orderedPairs, endpointWindow, stabilityGapTrace]
  · unfold maximalDrop
    have hmem :
        ((0 : Fin 3), (2 : Fin 3)) ∈ orderedPairs endpointWindow := by
      simp only [orderedPairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨by simp [endpointWindow], by decide⟩
    have hle := Finset.le_sup'
      (s := orderedPairs endpointWindow)
      (fun pair => stabilityGapTrace pair.1 - stabilityGapTrace pair.2)
      hmem
    simpa [stabilityGapTrace] using hle

theorem continual_sampling_exposes_unit_drop :
    maximalDrop stabilityGapTrace continualWindow
      continualWindow_orderedPairs_nonempty = 1 := by
  apply le_antisymm
  · unfold maximalDrop
    apply Finset.sup'_le continualWindow_orderedPairs_nonempty
    rintro ⟨earlier, later⟩ hpair
    fin_cases earlier <;> fin_cases later <;>
      simp_all [orderedPairs, continualWindow, stabilityGapTrace]
  · unfold maximalDrop
    have hmem :
        ((0 : Fin 3), (1 : Fin 3)) ∈ orderedPairs continualWindow := by
      simp only [orderedPairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨by simp [continualWindow], by decide⟩
    have hle := Finset.le_sup'
      (s := orderedPairs continualWindow)
      (fun pair => stabilityGapTrace pair.1 - stabilityGapTrace pair.2)
      hmem
    simpa [stabilityGapTrace] using hle

theorem coarser_sampling_can_hide_all_observed_forgetting :
    maximalDrop stabilityGapTrace endpointWindow
        endpointWindow_orderedPairs_nonempty <
      maximalDrop stabilityGapTrace continualWindow
        continualWindow_orderedPairs_nonempty := by
  rw [endpoint_sampling_reports_no_drop,
    continual_sampling_exposes_unit_drop]
  norm_num

/-- One strictly worse historical minimum makes WC-ACC strictly smaller than
endpoint ACC even when current-task performance is unchanged. -/
theorem strict_wcAcc :
    worstCaseAccuracy ({0} : Finset (Fin 1)) 1 (fun _ => 0) <
      endpointAverageAccuracy ({0} : Finset (Fin 1)) 1 (fun _ => 1) := by
  norm_num [worstCaseAccuracy, endpointAverageAccuracy]

#print axioms minimumAccuracy_antitone
#print axioms maximalDrop_mono
#print axioms worstCaseAccuracy_le_endpointAverageAccuracy
#print axioms strict_sampling_can_hide_prescribed_gap
#print axioms endpoint_sampling_strictly_misses_stability_gap
#print axioms coarser_sampling_can_hide_all_observed_forgetting

end Fixtures

end

end ContinualEvaluation

end Mettapedia.MachineLearning.ContinualLearning
