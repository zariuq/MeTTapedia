import Mettapedia.ProbabilityTheory.Moments.HausdorffMoment
import Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection

/-!
# Hausdorff Bridge for Categorical de Finetti

This file exposes the Hausdorff moment uniqueness theorem in the categorical/de Finetti layer:
equality of all moments on the subtype parameter space `Theta = [0,1]` implies equality of the
latent mixing measure on `Theta`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory

open MeasureTheory
open Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti
open Mettapedia.ProbabilityTheory.Exchangeability
open Mettapedia.ProbabilityTheory.HigherOrderProbability

/-- Helper: the count of `false` values in an all-`true` `Fin k → Bool` tuple is `0`. -/
private lemma countFalse_const_true (k : ℕ) :
    countFalse (fun _ : Fin k => true) = 0 := by
  have hpart := count_partition (n := k) (fun _ : Fin k => true)
  have htrue : countTrue (fun _ : Fin k => true) = k := countTrue_const_true k
  have : k + countFalse (fun _ : Fin k => true) = k := by simpa [htrue] using hpart
  exact Nat.add_left_cancel this

/-- The all-`true` prefix probability of a Bernoulli mixture equals its `k`-th latent moment
on `Theta = [0,1]`. -/
private lemma prob_allTrue_eq_moment_on_Theta
    (M : BernoulliMixture) (k : ℕ) :
    M.prob (fun _ : Fin k => true)
      = ∫ θ : DeFinettiConnection.Theta, (θ : ℝ) ^ k ∂DeFinettiConnection.mixingMeasureTheta M := by
  have hsub :=
    (MeasureTheory.integral_subtype_comap (μ := M.mixingMeasure)
      (s := Set.Icc (0 : ℝ) 1) (hs := DeFinettiConnection.measurableSet_Icc)
      (f := fun t : ℝ => t ^ k))
  have hfalse : countFalse (fun _ : Fin k => true) = 0 := countFalse_const_true k
  calc
    M.prob (fun _ : Fin k => true)
        = ∫ (x : ℝ) in Set.Icc (0 : ℝ) 1, x ^ k ∂M.mixingMeasure := by
            simp [BernoulliMixture.prob, bernoulliProductPMF_eq_power, hfalse]
    _ = ∫ θ : DeFinettiConnection.Theta, (θ : ℝ) ^ k ∂DeFinettiConnection.mixingMeasureTheta M := by
            simpa [DeFinettiConnection.mixingMeasureTheta] using hsub.symm

/-- The all-`true` prefix probability of a Bernoulli mixture is nonnegative. -/
private lemma prob_allTrue_nonneg
    (M : BernoulliMixture) (k : ℕ) :
    0 ≤ M.prob (fun _ : Fin k => true) := by
  rw [prob_allTrue_eq_moment_on_Theta M k]
  exact MeasureTheory.integral_nonneg (fun θ : DeFinettiConnection.Theta => pow_nonneg θ.2.1 k)

/-- Equality of all finite-prefix laws for two Bernoulli-mixture representations implies
equality of all latent moments on `Theta = [0,1]`. -/
theorem moments_eq_on_Theta_of_represents
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (M1 M2 : BernoulliMixture)
    (hrep1 : Represents M1 X μ)
    (hrep2 : Represents M2 X μ) :
    ∀ k : ℕ,
      ∫ θ : DeFinettiConnection.Theta, (θ : ℝ) ^ k ∂DeFinettiConnection.mixingMeasureTheta M1
        = ∫ θ : DeFinettiConnection.Theta, (θ : ℝ) ^ k ∂DeFinettiConnection.mixingMeasureTheta M2 := by
  intro k
  let xsTrue : Fin k → Bool := fun _ => true
  have hrepEq :
      ENNReal.ofReal (M1.prob xsTrue) = ENNReal.ofReal (M2.prob xsTrue) := by
    calc
      ENNReal.ofReal (M1.prob xsTrue)
          = μ {ω | ∀ i : Fin k, X i.val ω = xsTrue i} := by
              simpa [Represents, xsTrue] using (hrep1 k xsTrue).symm
      _ = ENNReal.ofReal (M2.prob xsTrue) := by
              simpa [Represents, xsTrue] using (hrep2 k xsTrue)
  have hnonneg1 : 0 ≤ M1.prob xsTrue := by
    simpa [xsTrue] using (prob_allTrue_nonneg M1 k)
  have hnonneg2 : 0 ≤ M2.prob xsTrue := by
    simpa [xsTrue] using (prob_allTrue_nonneg M2 k)
  have hprobEq : M1.prob xsTrue = M2.prob xsTrue :=
    (ENNReal.ofReal_eq_ofReal_iff hnonneg1 hnonneg2).1 hrepEq
  calc
    ∫ θ : DeFinettiConnection.Theta, (θ : ℝ) ^ k ∂DeFinettiConnection.mixingMeasureTheta M1
        = M1.prob xsTrue := by
            simpa [xsTrue] using (prob_allTrue_eq_moment_on_Theta M1 k).symm
    _ = M2.prob xsTrue := hprobEq
    _ = ∫ θ : DeFinettiConnection.Theta, (θ : ℝ) ^ k ∂DeFinettiConnection.mixingMeasureTheta M2 := by
            simpa [xsTrue] using (prob_allTrue_eq_moment_on_Theta M2 k)

/-- If two Bernoulli-mixture latent laws on `Theta = [0,1]` have the same moments,
then their `Theta`-pulled mixing measures are equal. -/
theorem mixingMeasureTheta_eq_of_moments_eq
    (M1 M2 : BernoulliMixture)
    (hmom :
      ∀ k : ℕ,
        ∫ θ : DeFinettiConnection.Theta, (θ : ℝ) ^ k ∂DeFinettiConnection.mixingMeasureTheta M1
          = ∫ θ : DeFinettiConnection.Theta, (θ : ℝ) ^ k ∂DeFinettiConnection.mixingMeasureTheta M2) :
    DeFinettiConnection.mixingMeasureTheta M1 = DeFinettiConnection.mixingMeasureTheta M2 := by
  exact Mettapedia.ProbabilityTheory.Moments.HausdorffMoment.probMeasure_unitInterval_eq_of_moments_eq
    (μ := DeFinettiConnection.mixingMeasureTheta M1)
    (ν := DeFinettiConnection.mixingMeasureTheta M2)
    hmom

/-- If two Bernoulli-mixture objects represent the same process law, then their latent
mixing measures on `Theta = [0,1]` are equal. -/
theorem mixingMeasureTheta_eq_of_represents
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (M1 M2 : BernoulliMixture)
    (hrep1 : Represents M1 X μ)
    (hrep2 : Represents M2 X μ) :
    DeFinettiConnection.mixingMeasureTheta M1 = DeFinettiConnection.mixingMeasureTheta M2 := by
  apply mixingMeasureTheta_eq_of_moments_eq
  exact moments_eq_on_Theta_of_represents (X := X) (μ := μ) (M1 := M1) (M2 := M2) hrep1 hrep2

/-- Representation-level uniqueness: if two Bernoulli-mixture objects represent
the same process law, they are equal. -/
theorem bernoulliMixture_eq_of_represents
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (M1 M2 : BernoulliMixture)
    (hrep1 : Represents M1 X μ)
    (hrep2 : Represents M2 X μ) :
    M1 = M2 := by
  have hΘ :
      DeFinettiConnection.mixingMeasureTheta M1 =
        DeFinettiConnection.mixingMeasureTheta M2 :=
    mixingMeasureTheta_eq_of_represents (X := X) (μ := μ) (M1 := M1) (M2 := M2) hrep1 hrep2
  exact DeFinettiConnection.bernoulliMixture_ext_of_mixingMeasureTheta_eq M1 M2 hΘ

/-- Universal-property style corollary (qualitative):
for an exchangeable binary process law, the representing Bernoulli mixture exists and is unique. -/
theorem existsUnique_bernoulliMixture_of_exchangeable
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    ∃! M : BernoulliMixture, Represents M X μ := by
  obtain ⟨M, hrep⟩ := deFinetti_infinite X μ hX hexch
  refine ⟨M, hrep, ?_⟩
  intro M' hrep'
  exact (bernoulliMixture_eq_of_represents (X := X) (μ := μ) (M1 := M') (M2 := M) hrep' hrep)

/-- Measure-level latent interface:
`ν : Measure Theta` is a valid latent representation for `μ` along `X`
if it is the pulled mixing measure of some Bernoulli-mixture representation. -/
def RepresentsLatentTheta
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (ν : Measure DeFinettiConnection.Theta) : Prop :=
  ∃ M : BernoulliMixture,
    Represents M X μ ∧ ν = DeFinettiConnection.mixingMeasureTheta M

/-- Qualitative universal-property form on the canonical latent object `Measure Theta`:
for an exchangeable binary process law, the latent `Theta` measure exists and is unique. -/
theorem existsUnique_latentThetaMeasure_of_exchangeable
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    ∃! ν : Measure DeFinettiConnection.Theta, RepresentsLatentTheta X μ ν := by
  obtain ⟨M, hrep⟩ := deFinetti_infinite X μ hX hexch
  refine ⟨DeFinettiConnection.mixingMeasureTheta M, ?_, ?_⟩
  · exact ⟨M, hrep, rfl⟩
  · intro ν hν
    rcases hν with ⟨M', hrep', hν'⟩
    calc
      ν = DeFinettiConnection.mixingMeasureTheta M' := hν'
      _ = DeFinettiConnection.mixingMeasureTheta M :=
        mixingMeasureTheta_eq_of_represents (X := X) (μ := μ) (M1 := M') (M2 := M) hrep' hrep

end Mettapedia.CategoryTheory
