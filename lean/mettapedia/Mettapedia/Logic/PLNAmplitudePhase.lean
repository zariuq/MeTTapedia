import Mettapedia.Logic.PLNInformationGeometry
import Mettapedia.Algebra.TwoDimClassification
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Amplitude/Phase PLN Boundary

This module records the first formal bridge from ordinary PLN strength and
confidence views to a possible amplitude/phase extension.

The current theorem surface is intentionally conservative:

* ordinary PLN is recovered as the Born-shadow projection of a real binary
  amplitude together with the usual concentration/confidence link;
* relative phase is not visible to the standard `TypedSTV` projection;
* algebraic two-path interference is extra structure beyond incoherent
  probability addition;
* the existing two-dimensional Knuth--Skilling-style algebra classification
  selects the complex/negative-`μ` carrier exactly when the conjugate norm is
  positive-definite.

Thus this file sets up an extension boundary.  It does not claim that a full
quantum PLN calculus has already been built.
-/

namespace Mettapedia.Logic.PLNAmplitudePhase

open Mettapedia.Logic.PLNTruthTower
open Mettapedia.Logic.PLNInformationGeometry
open Mettapedia.Logic.PLNConfidenceWeight
open Mettapedia.Logic.PLNConfidenceWeight.EvidenceWeightCoordinate
open Mettapedia.Algebra.TwoDimClassification

/-! ## Phased binary PLN states and their ordinary shadow -/

/-- A binary amplitude/phase state with the same concentration axis used by
ordinary PLN confidence links.

The magnitudes are intentionally stored as real coordinates here; the current
bridge only needs the Born shadow.  A later complex-amplitude calculus can
replace or enrich this record with an explicit complex phase factor. -/
structure BinaryAmplitudePhaseState where
  positiveMagnitude : ℝ
  negativeMagnitude : ℝ
  relativePhase : ℝ
  concentration : ℝ

namespace BinaryAmplitudePhaseState

/-- Forget concentration, retaining the minimal phased-amplitude part. -/
def toPhasedAmplitude (a : BinaryAmplitudePhaseState) :
    BinaryPhasedAmplitude where
  positiveMagnitude := a.positiveMagnitude
  negativeMagnitude := a.negativeMagnitude
  relativePhase := a.relativePhase

/-- Forget relative phase, retaining only the real amplitude magnitudes. -/
def classicalAmplitude (a : BinaryAmplitudePhaseState) : ℝ × ℝ :=
  a.toPhasedAmplitude.forgetPhase

/-- Born-style positive strength extracted from the classical shadow. -/
noncomputable def bornStrength (a : BinaryAmplitudePhaseState) : ℝ :=
  bernoulliBornPositive a.classicalAmplitude

/-- Born-style negative/complementary strength extracted from the classical
shadow. -/
noncomputable def bornCounterStrength (a : BinaryAmplitudePhaseState) : ℝ :=
  bernoulliBornNegative a.classicalAmplitude

/-- Project a phased binary state to the ordinary typed-STV view by forgetting
phase, applying Born's rule for strength, and using the chosen confidence link
on the concentration axis. -/
noncomputable def toTypedSTV
    (χ : EvidenceWeightCoordinate) (a : BinaryAmplitudePhaseState) :
    TypedSTV χ where
  strength := a.bornStrength
  confidence := TypedConfidence.ofWeight χ a.concentration

@[simp] theorem toTypedSTV_strength
    (χ : EvidenceWeightCoordinate) (a : BinaryAmplitudePhaseState) :
    (a.toTypedSTV χ).strength = a.bornStrength :=
  rfl

@[simp] theorem toTypedSTV_confidence
    (χ : EvidenceWeightCoordinate) (a : BinaryAmplitudePhaseState) :
    (a.toTypedSTV χ).confidence =
      TypedConfidence.ofWeight χ a.concentration :=
  rfl

/-- Build a phased state whose real amplitude magnitudes are the Hellinger
square roots of a Bernoulli strength and whose concentration is the PLN
evidence weight axis. -/
noncomputable def fromStrengthConcentration
    (p concentration phase : ℝ) : BinaryAmplitudePhaseState where
  positiveMagnitude := Real.sqrt p
  negativeMagnitude := Real.sqrt (1 - p)
  relativePhase := phase
  concentration := concentration

/-- The positive Born projection of the Hellinger/phased state recovers the
ordinary strength coordinate. -/
theorem fromStrengthConcentration_bornStrength
    {p concentration phase : ℝ} (hp0 : 0 ≤ p) :
    (fromStrengthConcentration p concentration phase).bornStrength = p := by
  unfold bornStrength classicalAmplitude toPhasedAmplitude fromStrengthConcentration
  exact bernoulliBornPositive_hellinger hp0

/-- The negative Born projection recovers the complementary strength. -/
theorem fromStrengthConcentration_bornCounterStrength
    {p concentration phase : ℝ} (hp1 : p ≤ 1) :
    (fromStrengthConcentration p concentration phase).bornCounterStrength =
      1 - p := by
  unfold bornCounterStrength classicalAmplitude toPhasedAmplitude
    fromStrengthConcentration
  exact bernoulliBornNegative_hellinger hp1

/-- The ordinary typed-STV projection of a phased Hellinger state has the
original Bernoulli strength. -/
theorem fromStrengthConcentration_toTypedSTV_strength
    (χ : EvidenceWeightCoordinate)
    {p concentration phase : ℝ} (hp0 : 0 ≤ p) :
    ((fromStrengthConcentration p concentration phase).toTypedSTV χ).strength =
      p := by
  rw [toTypedSTV_strength, fromStrengthConcentration_bornStrength hp0]

/-- Build a phased binary state from finite binary evidence.  The evidence
strength fixes the Hellinger magnitudes; phase is new extension data. -/
noncomputable def fromCounts
    (e : BinaryCounts) (phase : ℝ) : BinaryAmplitudePhaseState :=
  fromStrengthConcentration e.strength e.total phase

/-- For positive-total counts, the phased-amplitude Born shadow recovers the
ordinary PLN strength. -/
theorem fromCounts_bornStrength
    (e : BinaryCounts) (hTotal : 0 < e.total) (phase : ℝ) :
    (fromCounts e phase).bornStrength = e.strength := by
  exact
    fromStrengthConcentration_bornStrength
      (binaryCounts_strength_nonneg_of_total_pos e hTotal)

/-- For positive-total counts, the complementary Born shadow recovers
`1 - strength`. -/
theorem fromCounts_bornCounterStrength
    (e : BinaryCounts) (hTotal : 0 < e.total) (phase : ℝ) :
    (fromCounts e phase).bornCounterStrength = 1 - e.strength := by
  exact
    fromStrengthConcentration_bornCounterStrength
      (binaryCounts_strength_le_one_of_total_pos e hTotal)

/-- The ordinary typed-STV projection of a phased count state keeps the
standard PLN strength. -/
theorem fromCounts_toTypedSTV_strength
    (χ : EvidenceWeightCoordinate)
    (e : BinaryCounts) (hTotal : 0 < e.total) (phase : ℝ) :
    ((fromCounts e phase).toTypedSTV χ).strength = e.strength := by
  rw [toTypedSTV_strength, fromCounts_bornStrength e hTotal phase]

/-- The ordinary typed-STV projection of a phased count state uses the same
concentration/confidence link as ordinary PLN. -/
theorem fromCounts_toTypedSTV_confidence
    (χ : EvidenceWeightCoordinate) (e : BinaryCounts) (phase : ℝ) :
    ((fromCounts e phase).toTypedSTV χ).confidence =
      TypedConfidence.ofWeight χ e.total :=
  rfl

/-- Canary: two states can differ only in phase while projecting to the same
ordinary PLN typed-STV view. -/
theorem phase_not_visible_to_standard_pln_view :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let a := fromStrengthConcentration (1 / 2) 1 0
    let b := fromStrengthConcentration (1 / 2) 1 1
    a ≠ b ∧ a.toTypedSTV χ = b.toTypedSTV χ := by
  dsimp [fromStrengthConcentration, toTypedSTV, bornStrength,
    classicalAmplitude, toPhasedAmplitude, bernoulliBornPositive]
  constructor
  · intro h
    have hphase :
        (0 : ℝ) = 1 :=
      congrArg BinaryAmplitudePhaseState.relativePhase h
    norm_num at hphase
  · rfl

end BinaryAmplitudePhaseState

/-! ## Algebraic interference canaries -/

/-- Incoherent two-path probability weight: add the two Born weights and
discard phase. -/
noncomputable def incoherentTwoPathWeight (r s : ℝ) : ℝ :=
  r ^ 2 + s ^ 2

/-- Coherent two-path Born weight with a supplied relative phase cosine.
The last term is the interference contribution. -/
noncomputable def coherentTwoPathWeight (r s cosDelta : ℝ) : ℝ :=
  r ^ 2 + s ^ 2 + 2 * r * s * cosDelta

/-- Coherent weight is incoherent weight plus the interference term. -/
theorem coherentTwoPathWeight_eq_incoherent_plus_interference
    (r s cosDelta : ℝ) :
    coherentTwoPathWeight r s cosDelta =
      incoherentTwoPathWeight r s + 2 * r * s * cosDelta :=
  rfl

/-- If the relative phase averages the cosine to zero, the coherent and
incoherent weights agree. -/
theorem coherentTwoPathWeight_zero_interference
    (r s : ℝ) :
    coherentTwoPathWeight r s 0 = incoherentTwoPathWeight r s := by
  unfold coherentTwoPathWeight incoherentTwoPathWeight
  ring

/-- Constructive interference is not classical incoherent addition. -/
theorem constructiveInterference_differs_from_incoherent :
    coherentTwoPathWeight 1 1 1 ≠ incoherentTwoPathWeight 1 1 := by
  norm_num [coherentTwoPathWeight, incoherentTwoPathWeight]

/-- Destructive interference is not classical incoherent addition. -/
theorem destructiveInterference_differs_from_incoherent :
    coherentTwoPathWeight 1 1 (-1) ≠ incoherentTwoPathWeight 1 1 := by
  norm_num [coherentTwoPathWeight, incoherentTwoPathWeight]

/-! ## Complex phase factors and Born interference -/

/-- The unit complex phase factor in polar normal form.  This is the
cosine/sine normal form of `exp (i θ)`. -/
noncomputable def complexPhaseFactor (θ : ℝ) : ℂ :=
  Complex.mk (Real.cos θ) (Real.sin θ)

/-- A complex amplitude with real magnitude `r` and phase `θ`.  This is the
polar-normal-form version of `r * exp (i θ)`. -/
noncomputable def complexAmplitude (r θ : ℝ) : ℂ :=
  Complex.mk (r * Real.cos θ) (r * Real.sin θ)

/-- The polar phase factor is literally the complex exponential
`exp (i θ)`. -/
theorem complexPhaseFactor_eq_exp_mul_I (θ : ℝ) :
    complexPhaseFactor θ = Complex.exp ((θ : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp [complexPhaseFactor, Complex.exp_ofReal_mul_I_re]
  · simp [complexPhaseFactor, Complex.exp_ofReal_mul_I_im]

/-- The polar-normal-form amplitude is literally `r * exp (i θ)`. -/
theorem complexAmplitude_eq_real_mul_exp_mul_I (r θ : ℝ) :
    complexAmplitude r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp [complexAmplitude, Complex.exp_ofReal_mul_I_re, Complex.mul_re]
  · simp [complexAmplitude, Complex.exp_ofReal_mul_I_im, Complex.mul_im]

/-- The complex phase factor has unit Born weight. -/
theorem complexPhaseFactor_normSq (θ : ℝ) :
    Complex.normSq (complexPhaseFactor θ) = 1 := by
  simp [complexPhaseFactor, Complex.normSq_apply]
  simpa [sq] using Real.cos_sq_add_sin_sq θ

/-- Born's rule for a single complex amplitude: the phase disappears and the
weight is the squared magnitude. -/
theorem complexAmplitude_normSq (r θ : ℝ) :
    Complex.normSq (complexAmplitude r θ) = r ^ 2 := by
  simp [complexAmplitude, Complex.normSq_apply]
  nlinarith [Real.cos_sq_add_sin_sq θ]

/-- Hellinger/Born complex amplitude for a single Bernoulli probability. -/
noncomputable def complexHellingerAmplitude (p θ : ℝ) : ℂ :=
  complexAmplitude (Real.sqrt p) θ

/-- The complex Hellinger amplitude recovers the original probability by
Born's rule. -/
theorem complexHellingerAmplitude_normSq
    {p θ : ℝ} (hp : 0 ≤ p) :
    Complex.normSq (complexHellingerAmplitude p θ) = p := by
  unfold complexHellingerAmplitude
  rw [complexAmplitude_normSq, Real.sq_sqrt hp]

/-- Coherent two-path Born weight computed from honest complex amplitudes. -/
noncomputable def complexTwoPathBornWeight
    (r s θ φ : ℝ) : ℝ :=
  Complex.normSq (complexAmplitude r θ + complexAmplitude s φ)

/-- The complex two-path Born calculation gives the usual interference term. -/
theorem complexTwoPathBornWeight_interference
    (r s θ φ : ℝ) :
    complexTwoPathBornWeight r s θ φ =
      r ^ 2 + s ^ 2 + 2 * r * s * Real.cos (θ - φ) := by
  unfold complexTwoPathBornWeight complexAmplitude
  rw [Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im]
  rw [Real.cos_sub]
  ring_nf
  nlinarith [Real.cos_sq_add_sin_sq θ, Real.cos_sq_add_sin_sq φ]

/-- The complex-amplitude theorem reduces exactly to the earlier algebraic
coherent-weight canary. -/
theorem complexTwoPathBornWeight_eq_coherentWeight
    (r s θ φ : ℝ) :
    complexTwoPathBornWeight r s θ φ =
      coherentTwoPathWeight r s (Real.cos (θ - φ)) := by
  rw [complexTwoPathBornWeight_interference]
  rfl

/-- With zero phase difference, the two complex paths interfere
constructively. -/
theorem complexTwoPath_constructive_at_equal_phase :
    complexTwoPathBornWeight 1 1 0 0 = 4 := by
  norm_num [complexTwoPathBornWeight_interference]

/-- With opposite phase, the two equal complex paths destructively cancel. -/
theorem complexTwoPath_destructive_at_pi :
    complexTwoPathBornWeight 1 1 0 Real.pi = 0 := by
  rw [complexTwoPathBornWeight_interference]
  rw [show (0 : ℝ) - Real.pi = -Real.pi by ring, Real.cos_neg, Real.cos_pi]
  norm_num

/-! ## Two-dimensional KS-style carrier bridge -/

/-- The two-dimensional negative-`μ` carrier selected by positive-definite
conjugate norm. -/
abbrev KSComplexPhaseCarrier :=
  MuAlgebra (-1)

/-- The selected negative-`μ` carrier is the ordinary complex numbers. -/
noncomputable def ksComplexPhaseCarrierEquivComplex :
    KSComplexPhaseCarrier ≃+* ℂ :=
  muAlgebraNegOneEquivComplex

/-- The complex/negative-`μ` carrier has positive-definite conjugate norm. -/
theorem ksComplexPhaseCarrier_positiveDefinite :
    ∀ z : KSComplexPhaseCarrier,
      0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0) := by
  exact (selection_theorem (-1)).2 (by norm_num)

/-- The dual-number `μ = 0` carrier fails the positive-definite norm gate. -/
theorem dualCarrier_not_positiveDefinite :
    ¬ ∀ z : MuAlgebra 0,
      0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0) := by
  intro h
  have hneg : (0 : ℝ) < 0 :=
    (selection_theorem 0).1 h
  norm_num at hneg

/-- The split-complex `μ = 1` carrier fails the positive-definite norm gate. -/
theorem splitCarrier_not_positiveDefinite :
    ¬ ∀ z : MuAlgebra 1,
      0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0) := by
  intro h
  have hneg : (1 : ℝ) < 0 :=
    (selection_theorem 1).1 h
  norm_num at hneg

end Mettapedia.Logic.PLNAmplitudePhase
