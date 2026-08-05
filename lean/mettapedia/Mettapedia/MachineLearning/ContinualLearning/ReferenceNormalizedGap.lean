import Mathlib

/-!
# Reference-normalized continual-learning gaps

This file formalizes the metric algebra in Harun and Kanan,
*Overcoming the Stability Gap in Continual Learning*
(TMLR 2024, arXiv:2306.01904), Section 3.2.

Their stability, plasticity, and continual-knowledge gaps share one form:
one minus the mean ratio between a learner's per-update accuracy and a
positive reference accuracy.  The reference changes with the metric, while
the algebra does not.  We isolate that common core and make its boundaries
explicit:

* matching the reference at every sampled update gives zero gap;
* pointwise better accuracy can only decrease the gap;
* performance everywhere below the reference gives a nonnegative gap;
* performance everywhere at least as good, and strictly better somewhere,
  gives a strictly negative gap;
* reference positivity is load-bearing, because Lean's totalized division
  otherwise makes a zero-over-zero trace report a unit gap.

The results concern the finite metric itself.  They do not validate any
particular continual-learning method or empirical upper bound.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace ReferenceNormalizedGap

noncomputable section

variable {Sample : Type*}

/-- One minus the mean learner/reference ratio on a nonempty finite sample.
Taking `Sample` to be session-update pairs recovers the equally weighted
double average used by the source. -/
def normalizedGap
    (samples : Finset Sample)
    (actual reference : Sample → ℝ) : ℝ :=
  1 - (∑ sample ∈ samples, actual sample / reference sample) /
    (samples.card : ℝ)

theorem normalizedGap_antitone_actual
    (samples : Finset Sample)
    (actual₁ actual₂ reference : Sample → ℝ)
    (hactual :
      ∀ sample ∈ samples, actual₁ sample ≤ actual₂ sample)
    (hreference :
      ∀ sample ∈ samples, 0 < reference sample) :
    normalizedGap samples actual₂ reference ≤
      normalizedGap samples actual₁ reference := by
  unfold normalizedGap
  gcongr with sample hsample
  exact le_of_lt (hreference sample hsample)
  exact hactual sample hsample

theorem normalizedGap_eq_zero_of_matches_reference
    (samples : Finset Sample)
    (hne : samples.Nonempty)
    (actual reference : Sample → ℝ)
    (hactual :
      ∀ sample ∈ samples, actual sample = reference sample)
    (hreference :
      ∀ sample ∈ samples, reference sample ≠ 0) :
    normalizedGap samples actual reference = 0 := by
  have hcard : (samples.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  unfold normalizedGap
  have hsum :
      (∑ sample ∈ samples, actual sample / reference sample) =
        (samples.card : ℝ) := by
    calc
      (∑ sample ∈ samples, actual sample / reference sample) =
          ∑ _sample ∈ samples, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro sample hsample
        rw [hactual sample hsample]
        exact div_self (hreference sample hsample)
      _ = (samples.card : ℝ) := by simp
  rw [hsum, div_self hcard]
  norm_num

theorem normalizedGap_nonneg_of_below_reference
    (samples : Finset Sample)
    (hne : samples.Nonempty)
    (actual reference : Sample → ℝ)
    (hactual :
      ∀ sample ∈ samples, actual sample ≤ reference sample)
    (hreference :
      ∀ sample ∈ samples, 0 < reference sample) :
    0 ≤ normalizedGap samples actual reference := by
  have hzero :=
    normalizedGap_eq_zero_of_matches_reference
      samples hne reference reference
        (fun _ _ => rfl)
        (fun sample hsample => ne_of_gt (hreference sample hsample))
  have hmono :=
    normalizedGap_antitone_actual
      samples actual reference reference hactual hreference
  rw [hzero] at hmono
  exact hmono

theorem normalizedGap_nonpos_of_above_reference
    (samples : Finset Sample)
    (hne : samples.Nonempty)
    (actual reference : Sample → ℝ)
    (hactual :
      ∀ sample ∈ samples, reference sample ≤ actual sample)
    (hreference :
      ∀ sample ∈ samples, 0 < reference sample) :
    normalizedGap samples actual reference ≤ 0 := by
  have hzero :=
    normalizedGap_eq_zero_of_matches_reference
      samples hne reference reference
        (fun _ _ => rfl)
        (fun sample hsample => ne_of_gt (hreference sample hsample))
  have hmono :=
    normalizedGap_antitone_actual
      samples reference actual reference hactual hreference
  rw [hzero] at hmono
  exact hmono

theorem normalizedGap_strictly_negative_of_transfer
    [DecidableEq Sample]
    (samples : Finset Sample)
    (actual reference : Sample → ℝ)
    (hactual :
      ∀ sample ∈ samples, reference sample ≤ actual sample)
    (hreference :
      ∀ sample ∈ samples, 0 < reference sample)
    {witness : Sample}
    (hwitness : witness ∈ samples)
    (hstrict : reference witness < actual witness) :
    normalizedGap samples actual reference < 0 := by
  have hcard : 0 < (samples.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨witness, hwitness⟩
  have hsum :
      (samples.card : ℝ) <
        ∑ sample ∈ samples, actual sample / reference sample := by
    calc
      (samples.card : ℝ) =
          ∑ _sample ∈ samples, (1 : ℝ) := by simp
      _ < ∑ sample ∈ samples, actual sample / reference sample := by
        apply Finset.sum_lt_sum
        · intro sample hsample
          simpa only [one_mul] using
            (le_div_iff₀ (hreference sample hsample)).2
              (by simpa only [one_mul] using hactual sample hsample)
        · exact
            ⟨witness, hwitness,
              (by
                simpa only [one_mul] using
                  (lt_div_iff₀ (hreference witness hwitness)).2
                    (by simpa only [one_mul] using hstrict))⟩
  unfold normalizedGap
  have :
      1 <
        (∑ sample ∈ samples, actual sample / reference sample) /
          (samples.card : ℝ) := by
    exact (lt_div_iff₀ hcard).2 (by simpa using hsum)
  linarith

/-! ## Exact finite fixtures -/

theorem matched_positive_reference_has_zero_gap :
    normalizedGap (Finset.univ : Finset (Fin 2))
      (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) = 0 := by
  norm_num [normalizedGap]

theorem strict_transfer_has_negative_gap :
    normalizedGap ({0} : Finset (Fin 1))
      (fun _ => (3 : ℝ) / 2) (fun _ => (1 : ℝ)) = -(1 / 2 : ℝ) := by
  norm_num [normalizedGap]

/-- Positive references are essential: with totalized division, matching
zero-valued actual and reference traces do not yield a zero gap. -/
theorem zero_reference_breaks_match_recovery :
    normalizedGap ({0} : Finset (Fin 1))
      (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) = 1 := by
  norm_num [normalizedGap]

#print axioms normalizedGap_antitone_actual
#print axioms normalizedGap_eq_zero_of_matches_reference
#print axioms normalizedGap_nonneg_of_below_reference
#print axioms normalizedGap_strictly_negative_of_transfer
#print axioms zero_reference_breaks_match_recovery

end

end ReferenceNormalizedGap

end Mettapedia.MachineLearning.ContinualLearning
