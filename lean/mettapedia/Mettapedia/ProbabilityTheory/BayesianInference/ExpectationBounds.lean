import Mettapedia.InformationTheory.Pinsker
import Mettapedia.ProbabilityTheory.BayesianInference.PriorReduction
import Mettapedia.ProbabilityTheory.BayesianInference.Variational

/-!
# Expectation error from a variational posterior gap

If a score is bounded by `M`, Pinsker turns the divergence between a trial
distribution `q` and the posterior into an expectation error. The variational
identity writes that divergence as `F(q) + log evidence`.

The evidence ratio of a supported prior change is the old posterior's
expectation of the prior ratio. A bounded ratio therefore inherits the same
estimate. Comparing logarithms needs a positive lower bound on both the
estimate and the ratio: `Real.log 0 = 0` identifies a zero estimate with the
logarithm of a unit ratio.
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference

open Finset Real
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV

variable {S : Type*} [Fintype S]

theorem klSum_posterior_eq_freeEnergy_add_log_evidence (prior q : Prob S)
    (likelihood : S → ℝ) (nonneg : ∀ s, 0 ≤ likelihood s)
    (possible : 0 < evidence prior likelihood)
    (support : SupportedBy q (fun s => prior.1 s * likelihood s)) :
    klSum q.1 (posterior prior likelihood nonneg possible).1 =
      variationalFreeEnergy prior likelihood q +
        Real.log (evidence prior likelihood) := by
  have h := variationalFreeEnergy_eq prior q likelihood nonneg possible support
  linarith

/-- `|E_q[f] - E_posterior[f]| ≤ M √(2 (F(q) + log evidence))` when `|f| ≤ M`. -/
theorem abs_variational_expectation_sub_le (prior q : Prob S) (likelihood : S → ℝ)
    (score : S → ℝ) (nonneg : ∀ s, 0 ≤ likelihood s)
    (possible : 0 < evidence prior likelihood)
    (support : SupportedBy q (fun s => prior.1 s * likelihood s))
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ s, |score s| ≤ M) :
    |∑ s, q.1 s * score s -
        ∑ s, (posterior prior likelihood nonneg possible).1 s * score s| ≤
      M * sqrt (2 * (variationalFreeEnergy prior likelihood q +
        Real.log (evidence prior likelihood))) := by
  have hsupport := supportedBy_posterior prior q likelihood nonneg possible support
  have hbound := abs_expectation_sub_le q (posterior prior likelihood nonneg possible)
    score hM hf hsupport
  rwa [klSum_posterior_eq_freeEnergy_add_log_evidence prior q likelihood nonneg possible
    support] at hbound

/-- On `(0, ∞)`, a common positive lower bound makes `log` Lipschitz. -/
theorem abs_log_sub_le_of_lower {x y δ : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) (hy : δ ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / δ := by
  have hside {a b : ℝ} (ha : δ ≤ a) (hb : δ ≤ b) :
      Real.log a - Real.log b ≤ |a - b| / δ := by
    have ha0 : 0 < a := lt_of_lt_of_le hδ ha
    have hb0 : 0 < b := lt_of_lt_of_le hδ hb
    have hlog := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    rw [Real.log_div ha0.ne' hb0.ne'] at hlog
    have hrewrite : a / b - 1 = (a - b) / b := by
      calc
        a / b - 1 = a / b - b / b := by rw [div_self hb0.ne']
        _ = (a - b) / b := by rw [← sub_div]
    rw [hrewrite] at hlog
    have hden : (a - b) / b ≤ |a - b| / b :=
      div_le_div_of_nonneg_right (le_abs_self (a - b)) hb0.le
    have habs : |a - b| / b ≤ |a - b| / δ :=
      div_le_div_of_nonneg_left (abs_nonneg (a - b)) hδ hb
    exact hlog.trans (hden.trans habs)
  refine abs_le.mpr ⟨?_, hside hx hy⟩
  have hother := hside hy hx
  rw [abs_sub_comm] at hother
  linarith

/-- Replacing the old posterior by a supported trial distribution changes a
bounded prior-ratio estimate by at most the variational Pinsker bound. -/
theorem abs_evidence_ratio_sub_le (old new q : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence old likelihood)
    (newSupport : ∀ s, 0 < new.1 s → 0 < old.1 s)
    (qSupport : SupportedBy q (fun s => old.1 s * likelihood s))
    {M : ℝ} (hM : 0 ≤ M) (hweight : ∀ s, priorRatio old new s ≤ M) :
    |∑ s, q.1 s * priorRatio old new s -
        evidence new likelihood / evidence old likelihood| ≤
      M * sqrt (2 * (variationalFreeEnergy old likelihood q +
        Real.log (evidence old likelihood))) := by
  have hweightAbs : ∀ s, |priorRatio old new s| ≤ M := fun s => by
    rw [abs_of_nonneg (priorRatio_nonneg old new s)]
    exact hweight s
  have hbound := abs_variational_expectation_sub_le old q likelihood (priorRatio old new)
    nonneg possible qSupport hM hweightAbs
  rw [← evidence_ratio_eq_posterior_expectation old new likelihood nonneg possible newSupport]
  simpa [evidence] using hbound

/-- The same replacement controls the logarithm once both the estimate and the
evidence ratio are bounded below by a positive `δ`. -/
theorem abs_log_evidence_ratio_sub_le (old new q : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence old likelihood)
    (newSupport : ∀ s, 0 < new.1 s → 0 < old.1 s)
    (qSupport : SupportedBy q (fun s => old.1 s * likelihood s))
    {M : ℝ} (hM : 0 ≤ M) (hweight : ∀ s, priorRatio old new s ≤ M)
    {δ : ℝ} (hδ : 0 < δ)
    (hestimate : δ ≤ ∑ s, q.1 s * priorRatio old new s)
    (htrue : δ ≤ evidence new likelihood / evidence old likelihood) :
    |Real.log (∑ s, q.1 s * priorRatio old new s) -
        Real.log (evidence new likelihood / evidence old likelihood)| ≤
      (M / δ) * sqrt (2 * (variationalFreeEnergy old likelihood q +
        Real.log (evidence old likelihood))) := by
  have herr := abs_evidence_ratio_sub_le old new q likelihood nonneg possible newSupport
    qSupport hM hweight
  have hlog := abs_log_sub_le_of_lower hδ hestimate htrue
  calc
    |Real.log (∑ s, q.1 s * priorRatio old new s) -
        Real.log (evidence new likelihood / evidence old likelihood)|
        ≤ |∑ s, q.1 s * priorRatio old new s -
            evidence new likelihood / evidence old likelihood| / δ := hlog
    _ ≤ (M * sqrt (2 * (variationalFreeEnergy old likelihood q +
          Real.log (evidence old likelihood)))) / δ :=
      div_le_div_of_nonneg_right herr hδ.le
    _ = (M / δ) * sqrt (2 * (variationalFreeEnergy old likelihood q +
          Real.log (evidence old likelihood))) := by
      rw [mul_div_right_comm]

/-! ## Controls -/

/-- A zero estimate and a unit ratio have the same real logarithm. -/
theorem log_zero_hides_a_unit_gap :
    ¬ (|Real.log (0 : ℝ) - Real.log (1 : ℝ)| = |(0 : ℝ) - 1|) := by
  simp [Real.log_zero, Real.log_one]

noncomputable def ratioOld : Prob (Fin 2) :=
  binaryDist (1 / 2) (by norm_num) (by norm_num)

noncomputable def ratioNew : Prob (Fin 2) :=
  binaryDist (1 / 4) (by norm_num) (by norm_num)

noncomputable def ratioTrial : Prob (Fin 2) :=
  binaryDist (3 / 4) (by norm_num) (by norm_num)

private theorem ratioOld_possible : 0 < evidence ratioOld (fun _ => (1 : ℝ)) := by
  rw [evidence_one]
  norm_num

private theorem ratio_weight_le (i : Fin 2) : priorRatio ratioOld ratioNew i ≤ 3 / 2 := by
  fin_cases i <;>
    norm_num [priorRatio, ratioOld, ratioNew, binaryDist, Matrix.cons_val_zero,
      Matrix.cons_val_one]

private theorem ratio_new_supported (i : Fin 2) (hi : 0 < ratioNew.1 i) : 0 < ratioOld.1 i := by
  fin_cases i <;>
    norm_num [ratioOld, ratioNew, binaryDist, Matrix.cons_val_zero, Matrix.cons_val_one] at hi ⊢

private theorem ratio_trial_supported :
    SupportedBy ratioTrial (fun s => ratioOld.1 s * (1 : ℝ)) := by
  intro s hs
  fin_cases s <;>
    norm_num [ratioTrial, ratioOld, binaryDist, Matrix.cons_val_zero, Matrix.cons_val_one] at hs ⊢

private theorem ratio_estimate_eq :
    ∑ i, ratioTrial.1 i * priorRatio ratioOld ratioNew i = 3 / 4 := by
  norm_num [ratioTrial, ratioOld, ratioNew, priorRatio, binaryDist, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem ratio_true_eq :
    evidence ratioNew (fun _ => (1 : ℝ)) / evidence ratioOld (fun _ => (1 : ℝ)) = 1 := by
  simp [evidence_one]

theorem twoState_evidence_ratio_gap_pos :
    0 < |∑ i, ratioTrial.1 i * priorRatio ratioOld ratioNew i -
        evidence ratioNew (fun _ => (1 : ℝ)) / evidence ratioOld (fun _ => (1 : ℝ))| := by
  rw [ratio_estimate_eq, ratio_true_eq]
  norm_num

theorem twoState_evidence_ratio_bound :
    |∑ i, ratioTrial.1 i * priorRatio ratioOld ratioNew i -
        evidence ratioNew (fun _ => (1 : ℝ)) / evidence ratioOld (fun _ => (1 : ℝ))| ≤
      (3 / 2) * sqrt (2 * (variationalFreeEnergy ratioOld (fun _ => (1 : ℝ)) ratioTrial +
        Real.log (evidence ratioOld (fun _ => (1 : ℝ))))) :=
  abs_evidence_ratio_sub_le ratioOld ratioNew ratioTrial (fun _ => 1) (fun _ => by norm_num)
    ratioOld_possible ratio_new_supported ratio_trial_supported (by norm_num) ratio_weight_le

theorem twoState_log_evidence_ratio_gap_pos :
    0 < |Real.log (∑ i, ratioTrial.1 i * priorRatio ratioOld ratioNew i) -
        Real.log (evidence ratioNew (fun _ => (1 : ℝ)) /
          evidence ratioOld (fun _ => (1 : ℝ)))| := by
  rw [ratio_estimate_eq, ratio_true_eq, Real.log_one, sub_zero]
  exact abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))

theorem twoState_log_evidence_ratio_bound :
    |Real.log (∑ i, ratioTrial.1 i * priorRatio ratioOld ratioNew i) -
        Real.log (evidence ratioNew (fun _ => (1 : ℝ)) /
          evidence ratioOld (fun _ => (1 : ℝ)))| ≤
      ((3 / 2) / (1 / 2)) * sqrt (2 * (variationalFreeEnergy ratioOld (fun _ => (1 : ℝ))
        ratioTrial + Real.log (evidence ratioOld (fun _ => (1 : ℝ))))) := by
  refine abs_log_evidence_ratio_sub_le ratioOld ratioNew ratioTrial (fun _ => 1)
    (fun _ => by norm_num) ratioOld_possible ratio_new_supported ratio_trial_supported
    (by norm_num) ratio_weight_le (by norm_num) ?_ ?_
  · rw [ratio_estimate_eq]
    norm_num
  · rw [ratio_true_eq]
    norm_num

end Mettapedia.ProbabilityTheory.BayesianInference
