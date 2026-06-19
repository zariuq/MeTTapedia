import Mettapedia.Logic.EvidenceDirichlet
import Mettapedia.Logic.PLNTruthTower
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# PLN Information-Geometric Coordinates

This module records the small binary/Beta and categorical/Dirichlet slices of
the information-geometric story used by the PLN truth tower.

The load-bearing coordinates for finite binary evidence are:

* a mean / strength coordinate;
* a concentration / total-evidence coordinate.

A displayed confidence is then a separate link function applied to the
concentration coordinate.  Different valid links can be applied to the same
mean/concentration point, so the confidence display is not determined until a
link law is chosen.
-/

namespace Mettapedia.Logic.PLNInformationGeometry

open Mettapedia.Logic.PLNTruthTower
open Mettapedia.Logic.PLNConfidenceWeight
open Mettapedia.Logic.PLNConfidenceWeight.EvidenceWeightCoordinate

/-! ## Mean/concentration coordinates -/

/-- Binary simplex-scale coordinates: a direction in the unit interval together
with a positive total evidence scale. -/
structure BinarySimplexScale where
  strength : ℝ
  total : ℝ
  strength_nonneg : 0 ≤ strength
  strength_le_one : strength ≤ 1
  total_pos : 0 < total

/-- Decode simplex-scale coordinates back to positive/negative binary counts. -/
noncomputable def binarySimplexScaleToCounts (z : BinarySimplexScale) :
    BinaryCounts where
  nPlus := z.strength * z.total
  nMinus := (1 - z.strength) * z.total
  nPlus_nonneg := mul_nonneg z.strength_nonneg (le_of_lt z.total_pos)
  nMinus_nonneg :=
    mul_nonneg (sub_nonneg.mpr z.strength_le_one) (le_of_lt z.total_pos)

@[simp] theorem binarySimplexScaleToCounts_total (z : BinarySimplexScale) :
    (binarySimplexScaleToCounts z).total = z.total := by
  unfold binarySimplexScaleToCounts BinaryCounts.total
  ring

@[simp] theorem binarySimplexScaleToCounts_strength (z : BinarySimplexScale) :
    (binarySimplexScaleToCounts z).strength = z.strength := by
  unfold binarySimplexScaleToCounts BinaryCounts.strength BinaryCounts.total
  field_simp [ne_of_gt z.total_pos]
  ring

theorem binaryCounts_strength_nonneg_of_total_pos
    (e : BinaryCounts) (hTotal : 0 < e.total) :
    0 ≤ e.strength := by
  unfold BinaryCounts.strength
  exact div_nonneg e.nPlus_nonneg (le_of_lt hTotal)

theorem binaryCounts_strength_le_one_of_total_pos
    (e : BinaryCounts) (hTotal : 0 < e.total) :
    e.strength ≤ 1 := by
  unfold BinaryCounts.strength
  exact (div_le_one hTotal).2 (by
    unfold BinaryCounts.total at hTotal ⊢
    linarith [e.nMinus_nonneg])

/-- Convert positive-total binary counts to simplex-scale coordinates. -/
noncomputable def binaryCountsToSimplexScale
    (e : BinaryCounts) (hTotal : 0 < e.total) : BinarySimplexScale where
  strength := e.strength
  total := e.total
  strength_nonneg := binaryCounts_strength_nonneg_of_total_pos e hTotal
  strength_le_one := binaryCounts_strength_le_one_of_total_pos e hTotal
  total_pos := hTotal

/-- The theorem-level polar-coordinate equivalence:
positive binary counts are exactly a binary simplex direction times a positive
total evidence scale. -/
noncomputable def positiveBinaryCountsEquivSimplexScale :
    {e : BinaryCounts // 0 < e.total} ≃ BinarySimplexScale where
  toFun e := binaryCountsToSimplexScale e.val e.property
  invFun z :=
    ⟨binarySimplexScaleToCounts z, by
      rw [binarySimplexScaleToCounts_total]
      exact z.total_pos⟩
  left_inv := by
    intro e
    apply Subtype.ext
    cases e with
    | mk e hTotal =>
      cases e with
      | mk nPlus nMinus hp hm =>
        have hsum_pos : 0 < nPlus + nMinus := by
          simpa [BinaryCounts.total] using hTotal
        have hsum_ne : nPlus + nMinus ≠ 0 := ne_of_gt hsum_pos
        rw [BinaryCounts.mk.injEq]
        constructor
        · dsimp [binaryCountsToSimplexScale, binarySimplexScaleToCounts,
            BinaryCounts.strength, BinaryCounts.total]
          field_simp [hsum_ne]
        · dsimp [binaryCountsToSimplexScale, binarySimplexScaleToCounts,
            BinaryCounts.strength, BinaryCounts.total]
          field_simp [hsum_ne]
          ring
  right_inv := by
    intro z
    rw [BinarySimplexScale.mk.injEq]
    constructor
    · exact binarySimplexScaleToCounts_strength z
    · exact binarySimplexScaleToCounts_total z

/-! ## Binary Bernoulli information geometry -/

/-- Bernoulli log support-odds, the natural/e-coordinate on the open binary
simplex. -/
noncomputable def bernoulliLogOdds (p : ℝ) : ℝ :=
  Real.log (p / (1 - p))

/-- Logistic/sigmoid chart from the natural/e-coordinate back to the
mean/m-coordinate. -/
noncomputable def bernoulliNaturalToMean (θ : ℝ) : ℝ :=
  Real.exp θ / (1 + Real.exp θ)

/-- The natural-to-mean chart lands in the open binary simplex. -/
theorem bernoulliNaturalToMean_pos (θ : ℝ) :
    0 < bernoulliNaturalToMean θ := by
  have hExp : 0 < Real.exp θ := Real.exp_pos θ
  have hDen : 0 < 1 + Real.exp θ := by linarith
  unfold bernoulliNaturalToMean
  exact div_pos hExp hDen

/-- The natural-to-mean chart lands below `1`. -/
theorem bernoulliNaturalToMean_lt_one (θ : ℝ) :
    bernoulliNaturalToMean θ < 1 := by
  have hExp : 0 < Real.exp θ := Real.exp_pos θ
  have hDen : 0 < 1 + Real.exp θ := by linarith
  unfold bernoulliNaturalToMean
  exact (div_lt_one hDen).2 (by linarith)

/-- Log-odds and logistic/sigmoid are inverse charts from natural to mean
coordinates. -/
theorem bernoulliLogOdds_naturalToMean (θ : ℝ) :
    bernoulliLogOdds (bernoulliNaturalToMean θ) = θ := by
  have hDen : 0 < 1 + Real.exp θ := by
    have hExp : 0 < Real.exp θ := Real.exp_pos θ
    linarith
  have hDen_ne : 1 + Real.exp θ ≠ 0 := ne_of_gt hDen
  have honeMinus :
      1 - Real.exp θ / (1 + Real.exp θ) = 1 / (1 + Real.exp θ) := by
    field_simp [hDen_ne]
    ring
  unfold bernoulliLogOdds bernoulliNaturalToMean
  rw [honeMinus]
  have hratio :
      (Real.exp θ / (1 + Real.exp θ)) / (1 / (1 + Real.exp θ)) =
        Real.exp θ := by
    field_simp [hDen_ne]
  rw [hratio, Real.log_exp]

/-- Log-odds and logistic/sigmoid are inverse charts from mean to natural
coordinates on the open binary simplex. -/
theorem bernoulliNaturalToMean_logOdds
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    bernoulliNaturalToMean (bernoulliLogOdds p) = p := by
  have hcomp : 0 < 1 - p := by linarith
  have hratio_pos : 0 < p / (1 - p) := div_pos hp0 hcomp
  have hcomp_ne : 1 - p ≠ 0 := ne_of_gt hcomp
  unfold bernoulliNaturalToMean bernoulliLogOdds
  rw [Real.exp_log hratio_pos]
  have hden : 1 + p / (1 - p) = 1 / (1 - p) := by
    field_simp [hcomp_ne]
    ring
  rw [hden]
  field_simp [hcomp_ne]

/-- Bernoulli Fisher metric in the mean/m-coordinate `p`. -/
noncomputable def bernoulliFisherMetric (p : ℝ) : ℝ :=
  1 / (p * (1 - p))

/-- The one-dimensional Fisher tensor/quadratic form in the mean coordinate. -/
noncomputable def bernoulliFisherTensor (p v w : ℝ) : ℝ :=
  (v * w) / (p * (1 - p))

/-- Bernoulli KL divergence from `p` to `q`. -/
noncomputable def bernoulliKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- Jeffreys divergence, the symmetrized Bernoulli KL divergence. -/
noncomputable def bernoulliJeffreys (p q : ℝ) : ℝ :=
  bernoulliKL p q + bernoulliKL q p

/-- The Hellinger/square-root embedding of the binary simplex into the
Euclidean unit circle. -/
noncomputable def bernoulliHellingerEmbedding (p : ℝ) : ℝ × ℝ :=
  (Real.sqrt p, Real.sqrt (1 - p))

/-- Born-style positive probability recovered from a real two-amplitude. -/
noncomputable def bernoulliBornPositive (a : ℝ × ℝ) : ℝ :=
  a.1 ^ 2

/-- Born-style negative probability recovered from a real two-amplitude. -/
noncomputable def bernoulliBornNegative (a : ℝ × ℝ) : ℝ :=
  a.2 ^ 2

/-- The Hellinger embedding lands on the unit circle for every binary
probability value. -/
theorem bernoulliHellingerEmbedding_unit_circle
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliHellingerEmbedding p).1 ^ 2 +
        (bernoulliHellingerEmbedding p).2 ^ 2 = 1 := by
  have hcomp : 0 ≤ 1 - p := by linarith
  unfold bernoulliHellingerEmbedding
  rw [Real.sq_sqrt hp0, Real.sq_sqrt hcomp]
  ring

/-- The Fisher metric is positive on the open binary simplex. -/
theorem bernoulliFisherMetric_pos
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < bernoulliFisherMetric p := by
  have hcomp : 0 < 1 - p := by linarith
  have hprod : 0 < p * (1 - p) := mul_pos hp0 hcomp
  unfold bernoulliFisherMetric
  exact div_pos zero_lt_one hprod

/-- At the balanced point, the Fisher metric has value `4`. -/
theorem bernoulliFisherMetric_half :
    bernoulliFisherMetric (1 / 2) = 4 := by
  norm_num [bernoulliFisherMetric]

/-- The Fisher tensor is symmetric in its tangent arguments. -/
theorem bernoulliFisherTensor_symm (p v w : ℝ) :
    bernoulliFisherTensor p v w = bernoulliFisherTensor p w v := by
  unfold bernoulliFisherTensor
  ring

/-- The Fisher tensor is positive on nonzero tangent vectors over the open
binary simplex. -/
theorem bernoulliFisherTensor_diag_pos
    {p v : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hv : v ≠ 0) :
    0 < bernoulliFisherTensor p v v := by
  have hcomp : 0 < 1 - p := by linarith
  have hden : 0 < p * (1 - p) := mul_pos hp0 hcomp
  have hnum : 0 < v * v := mul_self_pos.mpr hv
  unfold bernoulliFisherTensor
  exact div_pos hnum hden

/-- At the balanced point, the Fisher tensor scales tangent products by `4`. -/
theorem bernoulliFisherTensor_half (v w : ℝ) :
    bernoulliFisherTensor (1 / 2) v w = 4 * v * w := by
  unfold bernoulliFisherTensor
  norm_num
  ring

/-! ## One-dimensional differential information-geometry handles -/

/-- The m-flat/mixture geodesic in the Bernoulli mean coordinate. -/
noncomputable def bernoulliMixtureGeodesic (p q t : ℝ) : ℝ :=
  (1 - t) * p + t * q

/-- The e-flat/exponential geodesic: straight line in log-odds, then the
logistic chart back to mean/strength. -/
noncomputable def bernoulliExponentialGeodesic (p q t : ℝ) : ℝ :=
  bernoulliNaturalToMean
    ((1 - t) * bernoulliLogOdds p + t * bernoulliLogOdds q)

/-- Velocity-form presentation of the m-flat/mixture geodesic.  It is
algebraically the same path as `bernoulliMixtureGeodesic`, but its derivative
is immediate from the affine form. -/
noncomputable def bernoulliMixtureGeodesicVelocityPath
    (p q : ℝ) : ℝ → ℝ :=
  (fun _ : ℝ => p) + fun t : ℝ => t * (q - p)

/-- Velocity-form presentation of the e-flat/exponential geodesic in the
natural/log-odds coordinate. -/
noncomputable def bernoulliExponentialGeodesicNaturalVelocityPath
    (p q : ℝ) : ℝ → ℝ :=
  (fun _ : ℝ => bernoulliLogOdds p) +
    fun t : ℝ => t * (bernoulliLogOdds q - bernoulliLogOdds p)

/-- The velocity-form mixture path is the displayed mixture geodesic. -/
theorem bernoulliMixtureGeodesicVelocityPath_eq_geodesic
    (p q t : ℝ) :
    bernoulliMixtureGeodesicVelocityPath p q t =
      bernoulliMixtureGeodesic p q t := by
  unfold bernoulliMixtureGeodesicVelocityPath bernoulliMixtureGeodesic
  simp [Pi.add_apply]
  ring

/-- The velocity-form natural path is the displayed straight line in
log-odds. -/
theorem bernoulliExponentialGeodesicNaturalVelocityPath_eq_linear
    (p q t : ℝ) :
    bernoulliExponentialGeodesicNaturalVelocityPath p q t =
      (1 - t) * bernoulliLogOdds p + t * bernoulliLogOdds q := by
  unfold bernoulliExponentialGeodesicNaturalVelocityPath
  simp [Pi.add_apply]
  ring

/-- The m-flat geodesic has constant velocity `q - p`. -/
theorem bernoulliMixtureGeodesicVelocityPath_hasDerivAt
    (p q t : ℝ) :
    HasDerivAt (bernoulliMixtureGeodesicVelocityPath p q) (q - p) t := by
  simpa [bernoulliMixtureGeodesicVelocityPath, one_mul, zero_add] using
    (hasDerivAt_const t p).add ((hasDerivAt_id t).mul_const (q - p))

/-- The displayed mixture geodesic has constant velocity `q - p`. -/
theorem bernoulliMixtureGeodesic_hasDerivAt
    (p q t : ℝ) :
    HasDerivAt (fun τ : ℝ => bernoulliMixtureGeodesic p q τ)
      (q - p) t := by
  have hfun :
      (fun τ : ℝ => bernoulliMixtureGeodesic p q τ) =
        bernoulliMixtureGeodesicVelocityPath p q := by
    funext τ
    exact (bernoulliMixtureGeodesicVelocityPath_eq_geodesic p q τ).symm
  rw [hfun]
  exact bernoulliMixtureGeodesicVelocityPath_hasDerivAt p q t

/-- The e-flat natural-coordinate geodesic has constant velocity equal to the
log-odds displacement. -/
theorem bernoulliExponentialGeodesicNaturalVelocityPath_hasDerivAt
    (p q t : ℝ) :
    HasDerivAt (bernoulliExponentialGeodesicNaturalVelocityPath p q)
      (bernoulliLogOdds q - bernoulliLogOdds p) t := by
  simpa [bernoulliExponentialGeodesicNaturalVelocityPath, one_mul, zero_add]
    using
      (hasDerivAt_const t (bernoulliLogOdds p)).add
        ((hasDerivAt_id t).mul_const
          (bernoulliLogOdds q - bernoulliLogOdds p))

@[simp] theorem bernoulliMixtureGeodesic_zero (p q : ℝ) :
    bernoulliMixtureGeodesic p q 0 = p := by
  unfold bernoulliMixtureGeodesic
  ring

@[simp] theorem bernoulliMixtureGeodesic_one (p q : ℝ) :
    bernoulliMixtureGeodesic p q 1 = q := by
  unfold bernoulliMixtureGeodesic
  ring

theorem bernoulliMixtureGeodesic_in_open_simplex
    {p q t : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < bernoulliMixtureGeodesic p q t ∧
      bernoulliMixtureGeodesic p q t < 1 := by
  have h1mt : 0 < 1 - t := by linarith
  constructor
  · unfold bernoulliMixtureGeodesic
    exact add_pos (mul_pos h1mt hp0) (mul_pos ht0 hq0)
  · have hcomp_p : 0 < 1 - p := by linarith
    have hcomp_q : 0 < 1 - q := by linarith
    have hpos :
        0 < (1 - t) * (1 - p) + t * (1 - q) :=
      add_pos (mul_pos h1mt hcomp_p) (mul_pos ht0 hcomp_q)
    unfold bernoulliMixtureGeodesic
    linarith

@[simp] theorem bernoulliExponentialGeodesic_zero
    {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    bernoulliExponentialGeodesic p q 0 = p := by
  unfold bernoulliExponentialGeodesic
  rw [show (1 - (0 : ℝ)) * bernoulliLogOdds p +
        0 * bernoulliLogOdds q = bernoulliLogOdds p by ring]
  exact bernoulliNaturalToMean_logOdds hp0 hp1

@[simp] theorem bernoulliExponentialGeodesic_one
    {p q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliExponentialGeodesic p q 1 = q := by
  unfold bernoulliExponentialGeodesic
  rw [show (1 - (1 : ℝ)) * bernoulliLogOdds p +
        1 * bernoulliLogOdds q = bernoulliLogOdds q by ring]
  exact bernoulliNaturalToMean_logOdds hq0 hq1

theorem bernoulliExponentialGeodesic_in_open_simplex (p q t : ℝ) :
    0 < bernoulliExponentialGeodesic p q t ∧
      bernoulliExponentialGeodesic p q t < 1 := by
  constructor
  · exact bernoulliNaturalToMean_pos _
  · exact bernoulliNaturalToMean_lt_one _

/-- The e-geodesic is linear in the natural/log-odds coordinate. -/
theorem bernoulliLogOdds_exponentialGeodesic (p q t : ℝ) :
    bernoulliLogOdds (bernoulliExponentialGeodesic p q t) =
      (1 - t) * bernoulliLogOdds p + t * bernoulliLogOdds q := by
  unfold bernoulliExponentialGeodesic
  exact bernoulliLogOdds_naturalToMean _

/-- The e-flat geodesic is a constant-velocity affine path after applying the
log-odds/natural coordinate. -/
theorem bernoulliLogOdds_exponentialGeodesic_hasDerivAt
    (p q t : ℝ) :
    HasDerivAt
      (fun τ : ℝ => bernoulliLogOdds (bernoulliExponentialGeodesic p q τ))
      (bernoulliLogOdds q - bernoulliLogOdds p) t := by
  have hfun :
      (fun τ : ℝ => bernoulliLogOdds
        (bernoulliExponentialGeodesic p q τ)) =
        bernoulliExponentialGeodesicNaturalVelocityPath p q := by
    funext τ
    rw [bernoulliLogOdds_exponentialGeodesic]
    exact
      (bernoulliExponentialGeodesicNaturalVelocityPath_eq_linear p q τ).symm
  rw [hfun]
  exact bernoulliExponentialGeodesicNaturalVelocityPath_hasDerivAt p q t

/-- The logistic chart sends the zero natural coordinate to the balanced
Bernoulli mean. -/
theorem bernoulliNaturalToMean_zero :
    bernoulliNaturalToMean 0 = 1 / 2 := by
  unfold bernoulliNaturalToMean
  rw [Real.exp_zero]
  norm_num

/-- Fisher tensor in the natural/log-odds coordinate.  Since
`dp/dθ = p(1-p)`, the pullback metric has coefficient `p(1-p)`. -/
noncomputable def bernoulliNaturalFisherTensor (θ u v : ℝ) : ℝ :=
  bernoulliNaturalToMean θ * (1 - bernoulliNaturalToMean θ) * u * v

theorem bernoulliNaturalFisherTensor_symm (θ u v : ℝ) :
    bernoulliNaturalFisherTensor θ u v =
      bernoulliNaturalFisherTensor θ v u := by
  unfold bernoulliNaturalFisherTensor
  ring

theorem bernoulliNaturalFisherTensor_diag_pos
    {θ u : ℝ} (hu : u ≠ 0) :
    0 < bernoulliNaturalFisherTensor θ u u := by
  have hp0 : 0 < bernoulliNaturalToMean θ :=
    bernoulliNaturalToMean_pos θ
  have hp1 : bernoulliNaturalToMean θ < 1 :=
    bernoulliNaturalToMean_lt_one θ
  have hcomp : 0 < 1 - bernoulliNaturalToMean θ := by linarith
  have hcoord : 0 < bernoulliNaturalToMean θ *
      (1 - bernoulliNaturalToMean θ) := mul_pos hp0 hcomp
  have hu2 : 0 < u * u := mul_self_pos.mpr hu
  unfold bernoulliNaturalFisherTensor
  nlinarith

theorem bernoulliNaturalFisherTensor_zero (u v : ℝ) :
    bernoulliNaturalFisherTensor 0 u v = (1 / 4) * u * v := by
  unfold bernoulliNaturalFisherTensor
  rw [bernoulliNaturalToMean_zero]
  ring

/-- Pulling the Fisher tensor back along the log-odds chart gives the natural
coordinate Fisher tensor. -/
theorem bernoulliFisherTensor_pullback_logOdds
    (θ u v : ℝ) :
    bernoulliFisherTensor (bernoulliNaturalToMean θ)
        (bernoulliNaturalToMean θ * (1 - bernoulliNaturalToMean θ) * u)
        (bernoulliNaturalToMean θ * (1 - bernoulliNaturalToMean θ) * v) =
      bernoulliNaturalFisherTensor θ u v := by
  have hp0 : 0 < bernoulliNaturalToMean θ :=
    bernoulliNaturalToMean_pos θ
  have hp1 : bernoulliNaturalToMean θ < 1 :=
    bernoulliNaturalToMean_lt_one θ
  have hprod :
      bernoulliNaturalToMean θ * (1 - bernoulliNaturalToMean θ) ≠ 0 := by
    exact ne_of_gt (mul_pos hp0 (by linarith))
  unfold bernoulliFisherTensor bernoulliNaturalFisherTensor
  field_simp [hprod]

/-- The m-flat affine connection has zero coefficient in the mean coordinate. -/
noncomputable def bernoulliMixtureConnectionCoeff (_p : ℝ) : ℝ := 0

/-- The e-flat affine connection has zero coefficient in the natural/log-odds
coordinate. -/
noncomputable def bernoulliExponentialConnectionCoeff (_θ : ℝ) : ℝ := 0

/-- Levi-Civita connection coefficient of the Bernoulli Fisher metric in the
mean coordinate. -/
noncomputable def bernoulliLeviCivitaMeanConnectionCoeff (p : ℝ) : ℝ :=
  (2 * p - 1) / (2 * p * (1 - p))

@[simp] theorem bernoulliMixtureConnectionCoeff_zero (p : ℝ) :
    bernoulliMixtureConnectionCoeff p = 0 := rfl

@[simp] theorem bernoulliExponentialConnectionCoeff_zero (θ : ℝ) :
    bernoulliExponentialConnectionCoeff θ = 0 := rfl

theorem bernoulliLeviCivitaMeanConnectionCoeff_half :
    bernoulliLeviCivitaMeanConnectionCoeff (1 / 2) = 0 := by
  norm_num [bernoulliLeviCivitaMeanConnectionCoeff]

/-- Squared Hellinger distance for Bernoulli parameters, expressed through the
real square-root embedding. -/
noncomputable def bernoulliSquaredHellinger (p q : ℝ) : ℝ :=
  (Real.sqrt p - Real.sqrt q) ^ 2 +
    (Real.sqrt (1 - p) - Real.sqrt (1 - q)) ^ 2

theorem bernoulliSquaredHellinger_nonneg (p q : ℝ) :
    0 ≤ bernoulliSquaredHellinger p q := by
  unfold bernoulliSquaredHellinger
  nlinarith [sq_nonneg (Real.sqrt p - Real.sqrt q),
    sq_nonneg (Real.sqrt (1 - p) - Real.sqrt (1 - q))]

theorem bernoulliSquaredHellinger_symm (p q : ℝ) :
    bernoulliSquaredHellinger p q = bernoulliSquaredHellinger q p := by
  unfold bernoulliSquaredHellinger
  ring

theorem bernoulliSquaredHellinger_self (p : ℝ) :
    bernoulliSquaredHellinger p p = 0 := by
  unfold bernoulliSquaredHellinger
  ring

/-- KL divergence from a Bernoulli parameter to itself is zero in the open
simplex. -/
theorem bernoulliKL_self
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    bernoulliKL p p = 0 := by
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have hcomp_ne : 1 - p ≠ 0 := by linarith
  have hp_div : p / p = 1 := div_self hp_ne
  have hcomp_div : (1 - p) / (1 - p) = 1 := div_self hcomp_ne
  unfold bernoulliKL
  rw [hp_div, hcomp_div, Real.log_one]
  ring

/-- Jeffreys divergence is symmetric by construction. -/
theorem bernoulliJeffreys_symm (p q : ℝ) :
    bernoulliJeffreys p q = bernoulliJeffreys q p := by
  unfold bernoulliJeffreys
  ring

/-- Jeffreys divergence also vanishes on the diagonal in the open simplex. -/
theorem bernoulliJeffreys_self
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    bernoulliJeffreys p p = 0 := by
  unfold bernoulliJeffreys
  rw [bernoulliKL_self hp0 hp1]
  ring

/-- Balanced Bernoulli log-odds are zero. -/
theorem bernoulliLogOdds_half :
    bernoulliLogOdds (1 / 2) = 0 := by
  norm_num [bernoulliLogOdds]

/-- The positive Born projection of the Hellinger embedding recovers the
Bernoulli strength. -/
theorem bernoulliBornPositive_hellinger
    {p : ℝ} (hp0 : 0 ≤ p) :
    bernoulliBornPositive (bernoulliHellingerEmbedding p) = p := by
  unfold bernoulliBornPositive bernoulliHellingerEmbedding
  exact Real.sq_sqrt hp0

/-- The negative Born projection of the Hellinger embedding recovers the
complementary Bernoulli strength. -/
theorem bernoulliBornNegative_hellinger
    {p : ℝ} (hp1 : p ≤ 1) :
    bernoulliBornNegative (bernoulliHellingerEmbedding p) = 1 - p := by
  have hcomp : 0 ≤ 1 - p := by linarith
  unfold bernoulliBornNegative bernoulliHellingerEmbedding
  exact Real.sq_sqrt hcomp

/-! ## Phase boundary canary -/

/-- Minimal binary amplitude-with-phase record.

The current PLN truth tower formalizes the real, phaseless Hellinger/Born
shadow.  A genuine quantum or waveform extension would need an additional
relative phase coordinate; this record marks that as extra structure rather
than silently identifying it with classical strength/confidence. -/
structure BinaryPhasedAmplitude where
  positiveMagnitude : ℝ
  negativeMagnitude : ℝ
  relativePhase : ℝ

namespace BinaryPhasedAmplitude

/-- Forget the relative phase, retaining only the real amplitude magnitudes. -/
def forgetPhase (a : BinaryPhasedAmplitude) : ℝ × ℝ :=
  (a.positiveMagnitude, a.negativeMagnitude)

end BinaryPhasedAmplitude

/-- Negative canary for the classical-to-quantum boundary: forgetting relative
phase is not injective.  The real Hellinger/Born shadow therefore does not carry
waveform phase information. -/
theorem binaryPhasedAmplitude_forgetPhase_not_injective :
    ¬ Function.Injective BinaryPhasedAmplitude.forgetPhase := by
  intro h
  let a : BinaryPhasedAmplitude := ⟨1, 0, 0⟩
  let b : BinaryPhasedAmplitude := ⟨1, 0, 1⟩
  have hforget : a.forgetPhase = b.forgetPhase := rfl
  have hab : a = b := h hforget
  have hphase :
      a.relativePhase = b.relativePhase :=
    congrArg BinaryPhasedAmplitude.relativePhase hab
  norm_num [a, b] at hphase

/-- Revision/pooling of positive-total binary counts is affine in the
mean/m-coordinate: the revised strength is the total-evidence weighted
mixture of the input strengths. -/
theorem binaryRevisionStrength_is_mixture_coordinate
    (e₁ e₂ : BinaryCounts)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0)
    (hSum : e₁.total + e₂.total ≠ 0) :
    (e₁.add e₂).strength =
      (e₁.strength * e₁.total + e₂.strength * e₂.total) /
        (e₁.total + e₂.total) :=
  BinaryCounts.add_strength_eq_weighted_mixture e₁ e₂ h₁ h₂ hSum

/-- Tensor/deductive composition is additive in the natural/e-coordinate:
log support-odds add under evidence tensor in the finite nonzero regime. -/
theorem binaryTruthLogOdds_tensor_is_natural_coordinate
    (x y : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence)
    (hx_neg : x.neg ≠ 0) (hy_neg : y.neg ≠ 0)
    (hx_odds0 : x.truthOdds ≠ 0) (hy_odds0 : y.truthOdds ≠ 0)
    (hx_oddsTop : x.truthOdds ≠ ⊤) (hy_oddsTop : y.truthOdds ≠ ⊤) :
    (x * y).truthLogOdds = x.truthLogOdds + y.truthLogOdds :=
  Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.truthLogOdds_tensor_add
    x y hx_neg hy_neg hx_odds0 hy_odds0 hx_oddsTop hy_oddsTop

/-- Binary Beta-style coordinates: posterior mean/strength together with
total concentration.  This is deliberately independent of any displayed
confidence link. -/
structure BetaMeanConcentration where
  mean : ℝ
  concentration : ℝ

namespace BetaMeanConcentration

/-- Decode a mean/concentration pair back to positive and negative counts. -/
noncomputable def decodeCounts (z : BetaMeanConcentration) : ℝ × ℝ :=
  (z.mean * z.concentration, (1 - z.mean) * z.concentration)

/-- The empirical mean/concentration coordinate of finite binary evidence. -/
noncomputable def fromCounts (e : BinaryCounts) : BetaMeanConcentration where
  mean := e.strength
  concentration := e.total

/-- Turn a binary information-geometric coordinate into a typed STV by choosing
a confidence coordinate for its concentration. -/
noncomputable def toTypedSTV
    (χ : EvidenceWeightCoordinate) (z : BetaMeanConcentration) : TypedSTV χ where
  strength := z.mean
  confidence := TypedConfidence.ofWeight χ z.concentration

/-- Once the confidence coordinate is chosen, the typed STV projection factors
through the binary mean/concentration coordinate. -/
theorem typedSTV_fromCounts_factors_through_betaCoordinate
    (χ : EvidenceWeightCoordinate) (e : BinaryCounts) :
    (fromCounts e).toTypedSTV χ = TypedSTV.fromCounts χ e :=
  rfl

/-- For positive-total evidence, empirical mean/concentration coordinates are
lossless: decoding recovers the original positive and negative evidence counts. -/
theorem decode_fromCounts (e : BinaryCounts) (hTotal : e.total ≠ 0) :
    (fromCounts e).decodeCounts = (e.nPlus, e.nMinus) := by
  have hTotal' : e.nPlus + e.nMinus ≠ 0 := by
    simpa [BinaryCounts.total] using hTotal
  ext
  · unfold decodeCounts fromCounts BinaryCounts.strength
    field_simp [hTotal']
  · unfold decodeCounts fromCounts BinaryCounts.strength
    field_simp [hTotal']
    simp [BinaryCounts.total]

end BetaMeanConcentration

/-! ## Confidence as a link on concentration -/

/-- PLN/NARS odds confidence as a link function on concentration. -/
noncomputable def plnConfidenceLink
    (k : ℝ) (hk : 0 < k) (z : BetaMeanConcentration) : ℝ :=
  (plnOddsCoordinate k hk).encode z.concentration

/-- A cautious reserve-half confidence link on the same concentration
coordinate. -/
noncomputable def reserveHalfLink
    (k : ℝ) (hk : 0 < k) (z : BetaMeanConcentration) : ℝ :=
  (reserveHalfCoordinate k hk).encode z.concentration

/-- Applying the PLN confidence link to an evidence point is exactly applying
the PLN odds coordinate to that point's total concentration. -/
theorem plnConfidenceLink_fromCounts
    (k : ℝ) (hk : 0 < k) (e : BinaryCounts) :
    plnConfidenceLink k hk (BetaMeanConcentration.fromCounts e) =
      (plnOddsCoordinate k hk).encode e.total :=
  rfl

/-- The PLN displayed confidence is exactly the display field of the typed STV
obtained by choosing the PLN odds link for the same concentration. -/
theorem plnConfidenceLink_eq_typedDisplay
    (k : ℝ) (hk : 0 < k) (z : BetaMeanConcentration) :
    plnConfidenceLink k hk z =
      (z.toTypedSTV (plnOddsCoordinate k hk)).confidence.display :=
  rfl

/-- Applying the reserve-half link to an evidence point is exactly applying the
reserve-half coordinate to that point's total concentration. -/
theorem reserveHalfLink_fromCounts
    (k : ℝ) (hk : 0 < k) (e : BinaryCounts) :
    reserveHalfLink k hk (BetaMeanConcentration.fromCounts e) =
      (reserveHalfCoordinate k hk).encode e.total :=
  rfl

/-- The reserve-half displayed confidence is likewise just the display field of
the typed STV obtained by choosing that link for the same concentration. -/
theorem reserveHalfLink_eq_typedDisplay
    (k : ℝ) (hk : 0 < k) (z : BetaMeanConcentration) :
    reserveHalfLink k hk z =
      (z.toTypedSTV (reserveHalfCoordinate k hk)).confidence.display :=
  rfl

/-- Canary: the same mean/concentration coordinate supports two valid but
different confidence links.  Mean/concentration alone therefore does not force
the displayed confidence convention. -/
theorem same_beta_coordinate_two_valid_confidence_links_differ :
    let z : BetaMeanConcentration := ⟨1 / 2, 1⟩
    plnConfidenceLink 1 (by norm_num) z ≠
      reserveHalfLink 1 (by norm_num) z := by
  dsimp [plnConfidenceLink, reserveHalfLink, plnOddsCoordinate,
    reserveHalfCoordinate]
  norm_num

/-! ## General Beta prior mean/concentration smoothing -/

/-- A general Beta prior expressed in information-geometric coordinates:
prior mean together with prior concentration. -/
structure BetaPriorMeanConcentration where
  mean : ℝ
  concentration : ℝ
  mean_nonneg : 0 ≤ mean
  mean_le_one : mean ≤ 1
  concentration_pos : 0 < concentration

namespace BetaPriorMeanConcentration

/-- The prior positive pseudo-count encoded by mean/concentration. -/
noncomputable def priorPositiveWeight (π : BetaPriorMeanConcentration) : ℝ :=
  π.mean * π.concentration

/-- The prior negative pseudo-count encoded by mean/concentration. -/
noncomputable def priorNegativeWeight (π : BetaPriorMeanConcentration) : ℝ :=
  (1 - π.mean) * π.concentration

/-- The prior pseudo-counts sum to the prior concentration. -/
theorem priorWeights_total (π : BetaPriorMeanConcentration) :
    π.priorPositiveWeight + π.priorNegativeWeight = π.concentration := by
  unfold priorPositiveWeight priorNegativeWeight
  ring

/-- The concentration-weight or Bühlmann-style credibility factor attached to
a general Beta prior. -/
noncomputable def blendWeight
    (π : BetaPriorMeanConcentration) (e : BinaryCounts) : ℝ :=
  e.total / (e.total + π.concentration)

/-- Posterior mean after updating a general Beta mean/concentration prior with
finite binary evidence. -/
noncomputable def posteriorMean
    (π : BetaPriorMeanConcentration) (e : BinaryCounts) : ℝ :=
  (π.priorPositiveWeight + e.nPlus) / (π.concentration + e.total)

/-- Posterior concentration is observed concentration plus prior
concentration. -/
noncomputable def posteriorConcentration
    (π : BetaPriorMeanConcentration) (e : BinaryCounts) : ℝ :=
  e.total + π.concentration

/-- Posterior concentration is strictly positive, so the posterior can itself
serve as the next Beta prior in a sequential update. -/
theorem posteriorConcentration_pos
    (π : BetaPriorMeanConcentration) (e : BinaryCounts) :
    0 < π.posteriorConcentration e := by
  unfold posteriorConcentration
  have htotal : 0 ≤ e.total := e.total_nonneg
  linarith [π.concentration_pos, htotal]

/-- General Beta posterior means stay in the unit interval. -/
theorem posteriorMean_nonneg
    (π : BetaPriorMeanConcentration) (e : BinaryCounts) :
    0 ≤ π.posteriorMean e := by
  unfold posteriorMean priorPositiveWeight
  apply div_nonneg
  · exact add_nonneg
      (mul_nonneg π.mean_nonneg (le_of_lt π.concentration_pos))
      e.nPlus_nonneg
  · have htotal : 0 ≤ e.total := e.total_nonneg
    linarith [π.concentration_pos, htotal]

/-- General Beta posterior means stay below one. -/
theorem posteriorMean_le_one
    (π : BetaPriorMeanConcentration) (e : BinaryCounts) :
    π.posteriorMean e ≤ 1 := by
  have hprior :
      π.priorPositiveWeight ≤ π.concentration := by
    unfold priorPositiveWeight
    calc
      π.mean * π.concentration ≤ 1 * π.concentration :=
        mul_le_mul_of_nonneg_right π.mean_le_one
          (le_of_lt π.concentration_pos)
      _ = π.concentration := by ring
  have hnum :
      π.priorPositiveWeight + e.nPlus ≤ π.concentration + e.total := by
    unfold BinaryCounts.total
    linarith [hprior, e.nMinus_nonneg]
  have hden : 0 < π.concentration + e.total := by
    have htotal : 0 ≤ e.total := e.total_nonneg
    linarith [π.concentration_pos, htotal]
  unfold posteriorMean
  exact (div_le_one hden).2 hnum

/-- Repackage a posterior Beta mean/concentration pair as the prior for the
next update.  This is the thin Bayesian counterpart of PLN evidence revision:
the new pseudo-counts are the old prior pseudo-counts plus observed evidence. -/
noncomputable def posteriorPrior
    (π : BetaPriorMeanConcentration) (e : BinaryCounts) :
    BetaPriorMeanConcentration where
  mean := π.posteriorMean e
  concentration := π.posteriorConcentration e
  mean_nonneg := π.posteriorMean_nonneg e
  mean_le_one := π.posteriorMean_le_one e
  concentration_pos := π.posteriorConcentration_pos e

/-- Updating the prior by evidence `e` adds `e`'s positive count to the prior
positive pseudo-count. -/
theorem posteriorPrior_priorPositiveWeight
    (π : BetaPriorMeanConcentration) (e : BinaryCounts) :
    (π.posteriorPrior e).priorPositiveWeight =
      π.priorPositiveWeight + e.nPlus := by
  unfold posteriorPrior posteriorMean posteriorConcentration priorPositiveWeight
  have hden : π.concentration + e.total ≠ 0 := by
    have htotal : 0 ≤ e.total := e.total_nonneg
    nlinarith [π.concentration_pos, htotal]
  field_simp [hden]
  ring

/-- Updating the prior by evidence `e` adds `e`'s negative count to the prior
negative pseudo-count. -/
theorem posteriorPrior_priorNegativeWeight
    (π : BetaPriorMeanConcentration) (e : BinaryCounts) :
    (π.posteriorPrior e).priorNegativeWeight =
      π.priorNegativeWeight + e.nMinus := by
  unfold posteriorPrior posteriorMean posteriorConcentration priorPositiveWeight
    priorNegativeWeight BinaryCounts.total
  have hden : π.concentration + (e.nPlus + e.nMinus) ≠ 0 := by
    have htotal : 0 ≤ e.nPlus + e.nMinus :=
      add_nonneg e.nPlus_nonneg e.nMinus_nonneg
    nlinarith [π.concentration_pos, htotal]
  field_simp [hden]
  ring

/-- Batch and sequential evidence updates have the same posterior
concentration. -/
theorem posteriorConcentration_add_eq_sequential
    (π : BetaPriorMeanConcentration) (e₁ e₂ : BinaryCounts) :
    π.posteriorConcentration (e₁.add e₂) =
      (π.posteriorPrior e₁).posteriorConcentration e₂ := by
  unfold posteriorPrior posteriorConcentration BinaryCounts.add BinaryCounts.total
  ring

/-- Batch PLN evidence revision is sequential Bayesian updating for a general
Beta mean/concentration prior.  This is the count-backed revision jewel: the
revision operation adds sufficient statistics, and the Beta posterior obtained
from the combined evidence is the same posterior obtained by updating in two
steps. -/
theorem posteriorMean_add_eq_sequential
    (π : BetaPriorMeanConcentration) (e₁ e₂ : BinaryCounts) :
    π.posteriorMean (e₁.add e₂) =
      (π.posteriorPrior e₁).posteriorMean e₂ := by
  unfold posteriorMean
  rw [posteriorPrior_priorPositiveWeight]
  unfold posteriorPrior posteriorConcentration BinaryCounts.add BinaryCounts.total
  ring

/-- Canary: with prior mean `1/2` and prior concentration `2`, updating by
`(1,1)` and then `(3,1)` equals the one-shot update by `(4,2)`, and differs
from the raw empirical strength `4/6`.  The prior is doing real Bayesian work;
this is not merely maximum-likelihood count pooling. -/
theorem posteriorMean_add_eq_sequential_canary :
    let π : BetaPriorMeanConcentration :=
      ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num⟩
    let e₁ : BinaryCounts :=
      ⟨1, 1, by norm_num, by norm_num⟩
    let e₂ : BinaryCounts :=
      ⟨3, 1, by norm_num, by norm_num⟩
    π.posteriorMean (e₁.add e₂) = 5 / 8 ∧
      (π.posteriorPrior e₁).posteriorMean e₂ = 5 / 8 ∧
      π.posteriorMean (e₁.add e₂) ≠ (e₁.add e₂).strength := by
  dsimp [posteriorPrior, posteriorMean, posteriorConcentration,
    priorPositiveWeight, BinaryCounts.add, BinaryCounts.strength,
    BinaryCounts.total]
  norm_num

/-- The general Beta blend weight is exactly the PLN/NARS odds link applied to
observed concentration, with `k` equal to prior concentration. -/
theorem blendWeight_eq_plnConfidenceLink
    (π : BetaPriorMeanConcentration) (e : BinaryCounts) :
    π.blendWeight e =
      plnConfidenceLink π.concentration π.concentration_pos
        (BetaMeanConcentration.fromCounts e) :=
  rfl

/-- General Beta posterior mean is a blend of empirical strength and prior
mean, with blend weight determined only by observed and prior concentration. -/
theorem posteriorMean_eq_blend_empirical_with_prior_mean
    (π : BetaPriorMeanConcentration) (e : BinaryCounts)
    (hTotal : e.total ≠ 0) :
    π.posteriorMean e =
      π.blendWeight e * e.strength +
        (1 - π.blendWeight e) * π.mean := by
  have ht : e.nPlus + e.nMinus ≠ 0 := by
    simpa [BinaryCounts.total] using hTotal
  have hden : e.nPlus + e.nMinus + π.concentration ≠ 0 := by
    have hnon : 0 ≤ e.nPlus + e.nMinus :=
      add_nonneg e.nPlus_nonneg e.nMinus_nonneg
    nlinarith [π.concentration_pos, hnon]
  have hden' : π.concentration + (e.nPlus + e.nMinus) ≠ 0 := by
    intro h
    apply hden
    linarith
  unfold posteriorMean blendWeight priorPositiveWeight BinaryCounts.strength
    BinaryCounts.total
  have hterm1 :
      ((e.nPlus + e.nMinus) /
          (e.nPlus + e.nMinus + π.concentration)) *
          (e.nPlus / (e.nPlus + e.nMinus)) =
        e.nPlus / (e.nPlus + e.nMinus + π.concentration) := by
    field_simp [ht, hden]
  have hterm2a :
      1 - (e.nPlus + e.nMinus) /
          (e.nPlus + e.nMinus + π.concentration) =
        π.concentration / (e.nPlus + e.nMinus + π.concentration) := by
    field_simp [hden]
    ring
  have hterm2 :
      (1 - (e.nPlus + e.nMinus) /
          (e.nPlus + e.nMinus + π.concentration)) * π.mean =
        π.mean * π.concentration /
          (e.nPlus + e.nMinus + π.concentration) := by
    rw [hterm2a]
    field_simp [hden]
  rw [hterm1, hterm2]
  have hsum :
      e.nPlus / (e.nPlus + e.nMinus + π.concentration) +
          π.mean * π.concentration /
            (e.nPlus + e.nMinus + π.concentration) =
        (π.mean * π.concentration + e.nPlus) /
          (π.concentration + (e.nPlus + e.nMinus)) := by
    field_simp [hden, hden']
    ring
  exact hsum.symm

/-- Canary: the prior mean is a real degree of freedom for posterior strength.
The same one-positive-observation evidence and same prior concentration give
different posterior means under different prior means. -/
theorem prior_mean_changes_posterior_strength :
    let e : BinaryCounts :=
      ⟨1, 0, by norm_num, by norm_num⟩
    let π₀ : BetaPriorMeanConcentration :=
      ⟨0, 2, by norm_num, by norm_num, by norm_num⟩
    let π₁ : BetaPriorMeanConcentration :=
      ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num⟩
    π₀.posteriorMean e ≠ π₁.posteriorMean e := by
  dsimp [posteriorMean, priorPositiveWeight, BinaryCounts.total]
  norm_num

/-- Canary: prior concentration is a real degree of freedom for the confidence
or blend-weight scale.  The same evidence and prior mean can give different
blend weights when the prior concentration changes. -/
theorem prior_concentration_changes_blend_weight :
    let e : BinaryCounts :=
      ⟨1, 0, by norm_num, by norm_num⟩
    let π₁ : BetaPriorMeanConcentration :=
      ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num⟩
    let π₂ : BetaPriorMeanConcentration :=
      ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num⟩
    π₁.blendWeight e ≠ π₂.blendWeight e := by
  dsimp [blendWeight, BinaryCounts.total]
  norm_num

end BetaPriorMeanConcentration

/-! ## Symmetric Beta prior smoothing -/

/-- A symmetric Beta prior with parameter `prior` on both positive and negative
outcomes. -/
structure SymmetricBetaPrior where
  prior : ℝ
  prior_pos : 0 < prior

namespace SymmetricBetaPrior

/-- The concentration-weight or Bühlmann-style credibility factor attached to a
symmetric Beta prior: observed concentration divided by observed plus prior
concentration. -/
noncomputable def blendWeight (π : SymmetricBetaPrior) (e : BinaryCounts) : ℝ :=
  e.total / (e.total + 2 * π.prior)

/-- Posterior mean after updating a symmetric Beta prior with finite binary
evidence. -/
noncomputable def posteriorMean (π : SymmetricBetaPrior) (e : BinaryCounts) : ℝ :=
  (π.prior + e.nPlus) / (2 * π.prior + e.total)

/-- The posterior concentration is observed concentration plus prior
concentration. -/
noncomputable def posteriorConcentration
    (π : SymmetricBetaPrior) (e : BinaryCounts) : ℝ :=
  e.total + 2 * π.prior

/-- The symmetric-Beta blend weight is exactly the PLN/NARS odds link applied
to concentration, with `k` equal to the prior concentration `2 * prior`. -/
theorem blendWeight_eq_plnConfidenceLink
    (π : SymmetricBetaPrior) (e : BinaryCounts) :
    π.blendWeight e =
      plnConfidenceLink (2 * π.prior) (by nlinarith [π.prior_pos])
        (BetaMeanConcentration.fromCounts e) :=
  rfl

/-- Symmetric Beta posterior mean is a convex-style blend of the empirical
strength with the symmetric prior mean `1/2`.  The blend weight is exactly the
observed concentration factor `n/(n+2 prior)`.

This is the precise binary/Beta version of the information-geometric slogan:
mean and concentration are the real coordinates; confidence-like quantities are
links of concentration. -/
theorem posteriorMean_eq_blend_empirical_with_prior_half
    (π : SymmetricBetaPrior) (e : BinaryCounts) (hTotal : e.total ≠ 0) :
    π.posteriorMean e =
      π.blendWeight e * e.strength +
        (1 - π.blendWeight e) * (1 / 2 : ℝ) := by
  have ht : e.nPlus + e.nMinus ≠ 0 := by
    simpa [BinaryCounts.total] using hTotal
  have hden : e.nPlus + e.nMinus + 2 * π.prior ≠ 0 := by
    have hnon : 0 ≤ e.nPlus + e.nMinus :=
      add_nonneg e.nPlus_nonneg e.nMinus_nonneg
    nlinarith [π.prior_pos, hnon]
  have hden' : π.prior * 2 + e.nPlus + e.nMinus ≠ 0 := by
    intro h
    apply hden
    linarith
  unfold posteriorMean blendWeight BinaryCounts.strength BinaryCounts.total
  field_simp [ht, hden, hden']
  rw [show (1 : ℝ) =
      (π.prior * 2 + e.nPlus + e.nMinus) *
        (π.prior * 2 + e.nPlus + e.nMinus)⁻¹ by
    exact (mul_inv_cancel₀ hden').symm]
  ring

end SymmetricBetaPrior

/-! ## Categorical Dirichlet coordinates -/

open Mettapedia.Logic.EvidenceDirichlet

/-- Categorical Dirichlet-style coordinates: a mean vector together with total
concentration.  As in the binary case, this deliberately does not choose a
displayed confidence link. -/
structure DirichletMeanConcentration (k : ℕ) where
  mean : Fin k → ℝ
  concentration : ℝ

namespace DirichletMeanConcentration

/-- Decode a mean-vector/concentration pair back to real-valued category
counts. -/
noncomputable def decodeCounts {k : ℕ}
    (z : DirichletMeanConcentration k) : Fin k → ℝ :=
  fun i => z.mean i * z.concentration

/-- The empirical mean-vector/concentration coordinate of finite categorical
evidence. -/
noncomputable def fromCounts {k : ℕ}
    (e : MultiEvidence k) : DirichletMeanConcentration k where
  mean := fun i => (e.counts i : ℝ) / (e.total : ℝ)
  concentration := (e.total : ℝ)

/-- Turn a categorical information-geometric coordinate into a typed
categorical truth view by choosing a confidence coordinate for its total
concentration. -/
noncomputable def toTypedTruth {k : ℕ}
    (χ : EvidenceWeightCoordinate) (z : DirichletMeanConcentration k) :
    TypedCategoricalTruth k χ where
  mean := z.mean
  confidence := TypedConfidence.ofWeight χ z.concentration

/-- Once the confidence coordinate is chosen, the typed categorical projection
factors through the Dirichlet mean/concentration coordinate. -/
theorem typedCategorical_fromCounts_factors_through_dirichletCoordinate {k : ℕ}
    (χ : EvidenceWeightCoordinate) (e : MultiEvidence k) :
    (fromCounts e).toTypedTruth χ =
      TypedCategoricalTruth.fromCounts χ e :=
  rfl

/-- For positive-total evidence, empirical Dirichlet mean/concentration
coordinates are lossless, pointwise in every category. -/
theorem decode_fromCounts {k : ℕ}
    (e : MultiEvidence k) (hTotal : e.total ≠ 0) (i : Fin k) :
    (fromCounts e).decodeCounts i = (e.counts i : ℝ) := by
  have hTotalR : (e.total : ℝ) ≠ 0 := by
    exact_mod_cast hTotal
  unfold decodeCounts fromCounts
  field_simp [hTotalR]

end DirichletMeanConcentration

/-- PLN/NARS odds confidence as a link function on categorical
concentration. -/
noncomputable def dirichletPLNConfidenceLink {k : ℕ}
    (s : ℝ) (hs : 0 < s) (z : DirichletMeanConcentration k) : ℝ :=
  (plnOddsCoordinate s hs).encode z.concentration

/-- The categorical PLN displayed confidence is exactly the typed display field
obtained by choosing the PLN odds link for the same concentration. -/
theorem dirichletPLNConfidenceLink_eq_typedDisplay {k : ℕ}
    (s : ℝ) (hs : 0 < s) (z : DirichletMeanConcentration k) :
    dirichletPLNConfidenceLink s hs z =
      (z.toTypedTruth (plnOddsCoordinate s hs)).confidence.display :=
  rfl

/-- Reserve-half confidence as an alternative link on categorical
concentration. -/
noncomputable def dirichletReserveHalfLink {k : ℕ}
    (s : ℝ) (hs : 0 < s) (z : DirichletMeanConcentration k) : ℝ :=
  (reserveHalfCoordinate s hs).encode z.concentration

/-- The categorical reserve-half displayed confidence is likewise just the
typed display field obtained by choosing that link. -/
theorem dirichletReserveHalfLink_eq_typedDisplay {k : ℕ}
    (s : ℝ) (hs : 0 < s) (z : DirichletMeanConcentration k) :
    dirichletReserveHalfLink s hs z =
      (z.toTypedTruth (reserveHalfCoordinate s hs)).confidence.display :=
  rfl

/-- Canary: a categorical mean-vector/concentration point also supports
different valid confidence links.  The multinomial coordinate therefore does
not force the displayed confidence convention. -/
theorem same_dirichlet_coordinate_two_valid_confidence_links_differ :
    let z : DirichletMeanConcentration 3 := ⟨fun _ => 1 / 3, 1⟩
    dirichletPLNConfidenceLink 1 (by norm_num) z ≠
      dirichletReserveHalfLink 1 (by norm_num) z := by
  dsimp [dirichletPLNConfidenceLink, dirichletReserveHalfLink,
    plnOddsCoordinate, reserveHalfCoordinate]
  norm_num

/-! ## Symmetric Dirichlet prior smoothing -/

/-- A symmetric Dirichlet prior with the same parameter in every category. -/
structure SymmetricDirichletPrior (k : ℕ) where
  prior : ℝ
  prior_pos : 0 < prior

namespace SymmetricDirichletPrior

/-- Total prior concentration for a symmetric `k`-category Dirichlet prior. -/
noncomputable def priorConcentration {k : ℕ}
    (π : SymmetricDirichletPrior k) : ℝ :=
  (k : ℝ) * π.prior

/-- The concentration-weight or Bühlmann-style credibility factor attached to a
symmetric Dirichlet prior. -/
noncomputable def blendWeight {k : ℕ}
    (π : SymmetricDirichletPrior k) (e : MultiEvidence k) : ℝ :=
  (e.total : ℝ) / ((e.total : ℝ) + π.priorConcentration)

/-- Posterior mean for one category after updating a symmetric Dirichlet prior
with finite categorical evidence. -/
noncomputable def posteriorMean {k : ℕ}
    (π : SymmetricDirichletPrior k) (e : MultiEvidence k) (i : Fin k) : ℝ :=
  (π.prior + (e.counts i : ℝ)) / (π.priorConcentration + (e.total : ℝ))

/-- Symmetric Dirichlet prior mean for each category. -/
noncomputable def priorMean {k : ℕ} (_π : SymmetricDirichletPrior k) : ℝ :=
  1 / (k : ℝ)

/-- The symmetric-Dirichlet blend weight is exactly the PLN/NARS odds link
applied to categorical concentration, with `k` equal to the prior
concentration. -/
theorem blendWeight_eq_dirichletPLNConfidenceLink {k : ℕ}
    (π : SymmetricDirichletPrior k) (hk : 0 < k) (e : MultiEvidence k) :
    π.blendWeight e =
      dirichletPLNConfidenceLink π.priorConcentration
        (by
          have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
          unfold priorConcentration
          exact mul_pos hkR π.prior_pos)
        (DirichletMeanConcentration.fromCounts e) := by
  rfl

/-- Symmetric Dirichlet posterior mean is a categorywise blend of the empirical
mean vector with the symmetric prior mean `1/k`.  The blend weight is observed
concentration divided by observed plus prior concentration. -/
theorem posteriorMean_eq_blend_empirical_with_prior_mean {k : ℕ}
    (π : SymmetricDirichletPrior k) (hk : 0 < k) (e : MultiEvidence k)
    (hTotal : e.total ≠ 0) (i : Fin k) :
    π.posteriorMean e i =
      π.blendWeight e * (DirichletMeanConcentration.fromCounts e).mean i +
        (1 - π.blendWeight e) * π.priorMean := by
  have hTotalR : (e.total : ℝ) ≠ 0 := by
    exact_mod_cast hTotal
  have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkR : (k : ℝ) ≠ 0 := ne_of_gt hkR_pos
  have hD : (e.total : ℝ) + (k : ℝ) * π.prior ≠ 0 := by
    have hnon : 0 ≤ (e.total : ℝ) := by
      exact_mod_cast (Nat.zero_le e.total)
    nlinarith [hnon, hkR_pos, π.prior_pos]
  have hD' : (k : ℝ) * π.prior + (e.total : ℝ) ≠ 0 := by
    intro h
    apply hD
    linarith
  unfold posteriorMean blendWeight priorMean priorConcentration
    DirichletMeanConcentration.fromCounts
  have hterm1 :
      ((e.total : ℝ) / ((e.total : ℝ) + (k : ℝ) * π.prior)) *
          ((e.counts i : ℝ) / (e.total : ℝ)) =
        (e.counts i : ℝ) / ((e.total : ℝ) + (k : ℝ) * π.prior) := by
    field_simp [hTotalR, hD]
  have hterm2a :
      1 - (e.total : ℝ) / ((e.total : ℝ) + (k : ℝ) * π.prior) =
        ((k : ℝ) * π.prior) /
          ((e.total : ℝ) + (k : ℝ) * π.prior) := by
    field_simp [hD]
    ring
  have hterm2 :
      (1 - (e.total : ℝ) / ((e.total : ℝ) + (k : ℝ) * π.prior)) *
          (1 / (k : ℝ)) =
        π.prior / ((e.total : ℝ) + (k : ℝ) * π.prior) := by
    rw [hterm2a]
    field_simp [hkR]
  rw [hterm1, hterm2]
  have hsum :
      (e.counts i : ℝ) / ((e.total : ℝ) + (k : ℝ) * π.prior) +
          π.prior / ((e.total : ℝ) + (k : ℝ) * π.prior) =
        (π.prior + (e.counts i : ℝ)) /
          ((k : ℝ) * π.prior + (e.total : ℝ)) := by
    field_simp [hD, hD']
    ring
  exact hsum.symm

end SymmetricDirichletPrior

end Mettapedia.Logic.PLNInformationGeometry
