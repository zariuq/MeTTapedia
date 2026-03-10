import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Basic
import Mettapedia.Logic.EvidenceWeightedNormalGamma
import Mettapedia.Logic.WeightedNormalGammaSurface

/-!
# Finite Gaussian-Mixture E/M Layer over Weighted WM Evidence

This file adds a first honest finite Gaussian-mixture E/M layer on top of the
weighted Normal-Gamma evidence carrier.

The connection to the existing WM/PLN calculus is direct:

- the E-step produces fractional responsibilities
- the M-step aggregates those responsibilities through
  `weightedGaussianStatistic`
- each component posterior is updated by the weighted conjugate posterior

This is a finite one-step E/M layer, not a convergence development.
-/

namespace Mettapedia.Logic.PLNGaussianEM

open scoped BigOperators
open Mettapedia.Logic.SufficientStatisticSurface

abbrev NGPrior := Mettapedia.Logic.EvidenceNormalGamma.NormalGammaPrior
abbrev WNGE := Mettapedia.Logic.EvidenceWeightedNormalGamma.WeightedNormalGammaEvidence

@[simp] theorem WNGE_zero_weight : (0 : WNGE).weight = 0 := rfl

@[simp] theorem WNGE_single_weight (w : NNReal) (x : ℝ) :
    (Mettapedia.Logic.EvidenceWeightedNormalGamma.WeightedNormalGammaEvidence.single w x).weight = w := rfl

/-- Finite Gaussian-mixture state for one-step EM.

`basePrior` is the fixed M-step prior. `estimate` is the current component
parameter estimate used by the E-step. -/
structure GaussianMixtureState (ι : Type*) where
  basePrior : ι → NGPrior
  estimate : ι → NGPrior
  mixingWeight : ι → NNReal
  mixingWeight_sum : ∀ [Fintype ι], ∑ i, mixingWeight i = 1

namespace GaussianMixtureState

variable {ι : Type*}

/-- Posterior-mean precision estimate `E[τ | data] = α / β`. -/
noncomputable def componentPrecisionMean (S : GaussianMixtureState ι) (i : ι) : ℝ :=
  (S.estimate i).α₀ / (S.estimate i).β₀

theorem componentPrecisionMean_pos (S : GaussianMixtureState ι) (i : ι) :
    0 < S.componentPrecisionMean i := by
  unfold componentPrecisionMean
  exact div_pos (S.estimate i).α₀_pos (S.estimate i).β₀_pos

/-- Unnormalized Gaussian E-step score using the current posterior-mean
precision estimate. The common `1 / sqrt(2π)` factor is omitted. -/
noncomputable def gaussianScore (S : GaussianMixtureState ι) (i : ι) (x : ℝ) : ℝ :=
  (S.mixingWeight i : ℝ) *
    Real.sqrt (S.componentPrecisionMean i) *
    Real.exp (-(S.componentPrecisionMean i) * (x - (S.estimate i).μ₀) ^ 2 / 2)

theorem gaussianScore_nonneg (S : GaussianMixtureState ι) (i : ι) (x : ℝ) :
    0 ≤ S.gaussianScore i x := by
  unfold gaussianScore
  apply mul_nonneg
  · apply mul_nonneg
    · exact (S.mixingWeight i).2
    · exact Real.sqrt_nonneg _
  · exact le_of_lt (Real.exp_pos _)

section Finite

variable [Fintype ι]

theorem exists_positive_mixingWeight (S : GaussianMixtureState ι) :
    ∃ i, 0 < S.mixingWeight i := by
  classical
  by_contra h
  have hzero : ∀ i, S.mixingWeight i = 0 := by
    intro i
    by_cases hi : S.mixingWeight i = 0
    · exact hi
    · exfalso
      exact h ⟨i, lt_of_le_of_ne (S.mixingWeight i).2 (Ne.symm hi)⟩
  have hsum : (∑ i, S.mixingWeight i) = 0 := by
    simp [hzero]
  rw [S.mixingWeight_sum] at hsum
  norm_num at hsum

omit [Fintype ι] in
theorem gaussianScore_pos_of_weight_pos (S : GaussianMixtureState ι)
    (i : ι) (x : ℝ) (hw : 0 < S.mixingWeight i) :
    0 < S.gaussianScore i x := by
  unfold gaussianScore
  have hw' : 0 < (S.mixingWeight i : ℝ) := by exact_mod_cast hw
  have hτ : 0 < S.componentPrecisionMean i := S.componentPrecisionMean_pos i
  have hsqrt : 0 < Real.sqrt (S.componentPrecisionMean i) := Real.sqrt_pos.mpr hτ
  have hexp :
      0 <
        Real.exp (-(S.componentPrecisionMean i) * (x - (S.estimate i).μ₀) ^ 2 / 2) :=
    Real.exp_pos _
  exact mul_pos (mul_pos hw' hsqrt) hexp

/-- Total unnormalized score for one observation. -/
noncomputable def totalScore (S : GaussianMixtureState ι) (x : ℝ) : ℝ :=
  ∑ i, S.gaussianScore i x

theorem totalScore_pos (S : GaussianMixtureState ι) (x : ℝ) :
    0 < S.totalScore x := by
  classical
  rcases S.exists_positive_mixingWeight with ⟨i, hi⟩
  have hs : 0 < S.gaussianScore i x := S.gaussianScore_pos_of_weight_pos i x hi
  have hle : S.gaussianScore i x ≤ S.totalScore x := by
    unfold totalScore
    exact Finset.single_le_sum (fun j _ => S.gaussianScore_nonneg j x) (by simp)
  exact lt_of_lt_of_le hs hle

/-- Soft assignment / responsibility from the normalized Gaussian E-step score. -/
noncomputable def responsibility (S : GaussianMixtureState ι) (x : ℝ) (i : ι) : ℝ :=
  S.gaussianScore i x / S.totalScore x

theorem responsibility_nonneg (S : GaussianMixtureState ι) (x : ℝ) (i : ι) :
    0 ≤ S.responsibility x i := by
  unfold responsibility
  exact div_nonneg (S.gaussianScore_nonneg i x) (le_of_lt (S.totalScore_pos x))

theorem responsibility_le_one (S : GaussianMixtureState ι) (x : ℝ) (i : ι) :
    S.responsibility x i ≤ 1 := by
  have hscore_le : S.gaussianScore i x ≤ S.totalScore x := by
    classical
    unfold totalScore
    exact Finset.single_le_sum (fun j _ => S.gaussianScore_nonneg j x) (by simp)
  have htotal_pos : 0 < S.totalScore x := S.totalScore_pos x
  unfold responsibility
  rw [div_le_one htotal_pos]
  exact hscore_le

theorem responsibility_sum (S : GaussianMixtureState ι) (x : ℝ) :
    ∑ i, S.responsibility x i = 1 := by
  have htot : S.totalScore x ≠ 0 := ne_of_gt (S.totalScore_pos x)
  calc
    ∑ i, S.responsibility x i
        = (∑ i, S.gaussianScore i x) / S.totalScore x := by
            simp [responsibility, Finset.sum_div]
    _ = 1 := by
          rw [show (∑ i, S.gaussianScore i x) = S.totalScore x by rfl]
          exact div_self htot

/-- Responsibilities as `NNReal`, suitable for weighted sufficient-statistic
aggregation. -/
noncomputable def responsibilityNNReal (S : GaussianMixtureState ι) (x : ℝ) (i : ι) : NNReal :=
  ⟨S.responsibility x i, S.responsibility_nonneg x i⟩

theorem responsibilityNNReal_sum_coe (S : GaussianMixtureState ι) (x : ℝ) :
    ∑ i, (S.responsibilityNNReal x i : ℝ) = 1 := by
  simp [responsibilityNNReal, responsibility_sum]

/-- The weighted sufficient-statistic surface induced by the E-step. -/
noncomputable def mStepSurface (S : GaussianMixtureState ι) :
    Mettapedia.Logic.SufficientStatisticSurface ℝ ι WNGE :=
  weightedGaussianStatistic (fun x i => S.responsibilityNNReal x i) (fun x _ => x)

/-- Component evidence accumulated in the M-step. -/
noncomputable def mStepEvidence (S : GaussianMixtureState ι) (σ : Multiset ℝ) (i : ι) : WNGE :=
  aggregate (S.mStepSurface) σ i

/-- The M-step evidence count is exactly the aggregated responsibility mass for
the component. This is the direct WM/sufficient-statistics connection. -/
theorem mStepEvidence_observationCount (S : GaussianMixtureState ι)
    (σ : Multiset ℝ) (i : ι) :
    Mettapedia.Logic.ConjugateEvidenceSurface.ConjugateEvidence.observationCount
        (S.mStepEvidence σ i) =
      Mettapedia.Logic.PLNWorldModelAdditive.genAdditiveExtension
        (Ev := ENNReal)
        (fun x j => (S.responsibilityNNReal x j : ENNReal)) σ i := by
  simpa [mStepEvidence, mStepSurface] using
    (Mettapedia.Logic.SufficientStatisticSurface.weightedGaussianStatistic_aggregate_observationCount
      (responsibility := fun x j => S.responsibilityNNReal x j)
      (value := fun x _ => x)
      (σ := σ) (q := i))

/-- Component posterior update in the M-step, using the fixed base prior. -/
noncomputable def mStepPosterior (S : GaussianMixtureState ι) (σ : Multiset ℝ) (i : ι) :
    NGPrior :=
  Mettapedia.Logic.EvidenceWeightedNormalGamma.WeightedNormalGammaEvidence.posterior
    (S.basePrior i) (S.mStepEvidence σ i)

@[simp] theorem mStepEvidence_zero (S : GaussianMixtureState ι) (i : ι) :
    S.mStepEvidence (0 : Multiset ℝ) i = 0 := by
  unfold mStepEvidence
  exact
    (Mettapedia.Logic.SufficientStatisticSurface.aggregate_zero (S := S.mStepSurface) i)

theorem mStepEvidence_cons (S : GaussianMixtureState ι) (x : ℝ) (σ : Multiset ℝ) (i : ι) :
    S.mStepEvidence (x ::ₘ σ) i = S.mStepSurface.observe x i + S.mStepEvidence σ i := by
  unfold mStepEvidence
  exact
    (Mettapedia.Logic.SufficientStatisticSurface.aggregate_cons (S := S.mStepSurface) x σ i)

theorem mStepEvidence_weight_sum_card (S : GaussianMixtureState ι) (σ : Multiset ℝ) :
    ∑ i, (S.mStepEvidence σ i).weight = σ.card := by
  classical
  induction σ using Multiset.induction_on with
  | empty =>
      simp
  | cons x σ ih =>
      simp_rw [S.mStepEvidence_cons x σ]
      calc
        ∑ i, ((S.mStepSurface.observe x i) + S.mStepEvidence σ i).weight
            = ∑ i, (S.mStepSurface.observe x i).weight + ∑ i, (S.mStepEvidence σ i).weight := by
                simp [Mettapedia.Logic.EvidenceWeightedNormalGamma.WeightedNormalGammaEvidence.hplus_weight,
                  Finset.sum_add_distrib]
        _ = ∑ i, (S.responsibilityNNReal x i : ℝ) + σ.card := by
              simp [mStepSurface, ih,
                Mettapedia.Logic.SufficientStatisticSurface.weightedGaussianStatistic]
        _ = 1 + σ.card := by rw [S.responsibilityNNReal_sum_coe x]
        _ = (x ::ₘ σ).card := by
              norm_num [Multiset.card_cons, Nat.cast_add, add_comm, add_left_comm, add_assoc]

theorem mixingWeight_sum_coe (S : GaussianMixtureState ι) :
    ∑ i, (S.mixingWeight i : ℝ) = 1 := by
  exact_mod_cast S.mixingWeight_sum

/-- Updated mixture weights from the M-step for a nonempty dataset. -/
noncomputable def mStepMixingWeightOfNonempty
    (S : GaussianMixtureState ι) (σ : Multiset ℝ) (_hσ : σ.card ≠ 0) (i : ι) : ℝ :=
  (S.mStepEvidence σ i).weight / σ.card

theorem mStepMixingWeightOfNonempty_nonneg (S : GaussianMixtureState ι)
    (σ : Multiset ℝ) (hσ : σ.card ≠ 0) (i : ι) :
    0 ≤ S.mStepMixingWeightOfNonempty σ hσ i := by
  unfold mStepMixingWeightOfNonempty
  exact div_nonneg (S.mStepEvidence σ i).weight_nonneg (Nat.cast_nonneg _)

theorem mStepMixingWeightOfNonempty_sum (S : GaussianMixtureState ι)
    (σ : Multiset ℝ) (hσ : σ.card ≠ 0) :
    ∑ i, S.mStepMixingWeightOfNonempty σ hσ i = 1 := by
  have hcard_ne : (σ.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hσ
  calc
    ∑ i, S.mStepMixingWeightOfNonempty σ hσ i
        = (∑ i, (S.mStepEvidence σ i).weight) / σ.card := by
            simp [mStepMixingWeightOfNonempty, Finset.sum_div]
    _ = (σ.card : ℝ) / σ.card := by rw [S.mStepEvidence_weight_sum_card]
    _ = 1 := by field_simp [hcard_ne]

/-- One-step M-update packaged as posteriors plus normalized real-valued
mixture weights. -/
structure MStepResult (ι : Type*) where
  posterior : ι → NGPrior
  mixingWeight : ι → ℝ

/-- The M-step result for a nonempty dataset. -/
noncomputable def mStepResult
    (S : GaussianMixtureState ι) (σ : Multiset ℝ) (hσ : σ.card ≠ 0) : MStepResult ι where
  posterior := S.mStepPosterior σ
  mixingWeight := S.mStepMixingWeightOfNonempty σ hσ

theorem mStepResult_mixingWeight_nonneg (S : GaussianMixtureState ι)
    (σ : Multiset ℝ) (hσ : σ.card ≠ 0) (i : ι) :
    0 ≤ (mStepResult S σ hσ).mixingWeight i := by
  exact S.mStepMixingWeightOfNonempty_nonneg σ hσ i

theorem mStepResult_mixingWeight_sum (S : GaussianMixtureState ι)
    (σ : Multiset ℝ) (hσ : σ.card ≠ 0) :
    ∑ i, (mStepResult S σ hσ).mixingWeight i = 1 := by
  exact S.mStepMixingWeightOfNonempty_sum σ hσ

section HardLabelReduction

theorem mixingWeight_unit_eq_one (S : GaussianMixtureState Unit) :
    S.mixingWeight () = 1 := by
  simpa using S.mixingWeight_sum

theorem responsibility_unit (S : GaussianMixtureState Unit) (x : ℝ) :
    S.responsibility x () = 1 := by
  have hw : 0 < S.mixingWeight () := by
    rw [S.mixingWeight_unit_eq_one]
    norm_num
  have hscore_pos : 0 < S.gaussianScore () x :=
    S.gaussianScore_pos_of_weight_pos () x hw
  have hscore_ne : S.gaussianScore () x ≠ 0 := ne_of_gt hscore_pos
  unfold GaussianMixtureState.responsibility GaussianMixtureState.totalScore
  simp [hscore_ne]

theorem responsibilityNNReal_unit_eq_one (S : GaussianMixtureState Unit) (x : ℝ) :
    S.responsibilityNNReal x () = 1 := by
  ext
  simp [GaussianMixtureState.responsibilityNNReal, S.responsibility_unit x]

/-- Hard-label reduction at the E/M layer: for a one-component mixture, the
M-step posterior is exactly the ordinary unweighted Gaussian posterior. -/
theorem mStepPosterior_unit_eq_gaussian
    (S : GaussianMixtureState Unit) (σ : Multiset ℝ) :
    S.mStepPosterior σ () =
      Mettapedia.Logic.EvidenceNormalGamma.posterior
        (S.basePrior ()) (aggregate (gaussianStatistic (fun x (_ : Unit) => x)) σ ()) := by
  unfold GaussianMixtureState.mStepPosterior GaussianMixtureState.mStepEvidence
    GaussianMixtureState.mStepSurface
  have hagg :
      aggregate
        (weightedGaussianStatistic
          (fun x (_ : Unit) => S.responsibilityNNReal x ())
          (fun x _ => x)) σ () =
      aggregate
        (weightedGaussianStatistic (fun _ (_ : Unit) => (1 : NNReal)) (fun x _ => x)) σ () := by
    induction σ using Multiset.induction_on with
    | empty =>
        simp
    | @cons x σ ih =>
        rw [SufficientStatisticSurface.aggregate_cons,
          SufficientStatisticSurface.aggregate_cons, ih]
        congr 1
        change
          Mettapedia.Logic.EvidenceWeightedNormalGamma.WeightedNormalGammaEvidence.single
              (S.responsibilityNNReal x ()) x =
            Mettapedia.Logic.EvidenceWeightedNormalGamma.WeightedNormalGammaEvidence.single
              (1 : NNReal) x
        congr
        exact S.responsibilityNNReal_unit_eq_one x
  rw [hagg]
  simpa using
    (weightedGaussianStatistic_one_posterior_eq_gaussian
      (prior := S.basePrior ())
      (value := fun x (_ : Unit) => x)
      (σ := σ) (q := ()))

end HardLabelReduction

end Finite

end GaussianMixtureState

end Mettapedia.Logic.PLNGaussianEM
