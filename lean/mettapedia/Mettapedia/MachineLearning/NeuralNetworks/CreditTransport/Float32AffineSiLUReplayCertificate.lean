import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ActivationReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalUnaryWireCertificateChecker
import Mathlib.Tactic

/-!
# Exact binary32 affine--SiLU replay certificates

This module composes one accepted binary32 affine replay with one accepted
SiLU replay per output coordinate.  The checker requires exact word continuity
between the observed affine output and the activation input, and it checks a
single rational region containing both the observed and ideal preactivations.

The resulting pointwise local-error budget is

`sum activationError + siluRate radius * affineError`.

It certifies only the traced block at the supplied input.  Source provenance,
coverage of other invocations, backend accumulation order, and uniform
regional floating-point error remain separate obligations.  The kernel checks
the arithmetic and exact interior word connection; an external verifier and
its hashes must bind the two endpoint payloads to an actual trace.  Hashes
printed in generated Lean comments are provenance metadata, not kernel facts.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32AffineSiLUReplayCertificate

open scoped BigOperators
open Float32CheckpointMatrix
open Float32AffineReplayCertificate
open Float32ActivationReplayCertificate
open FiniteMatrixOperatorBounds
open FinitePrecisionEvaluationError
open RegisteredUnaryExpressionCertificate
open RationalRangeReducedActivationEnclosureCertificate
open RationalUnaryWireCertificateChecker
open SiLUTransitionBounds

noncomputable section

/-- One affine invocation followed by coordinatewise SiLU.  Every activation
record is indexed by the affine output coordinate, so no count field can drift
from the tensor shape. -/
structure Float32AffineSiLUReplay (rows columns : ℕ) where
  affine : Float32AffineReplay rows columns
  activation : Fin rows → Float32ActivationReplay
  radius : ℚ

/-- Propositional contract mirrored by the executable checker. -/
def Float32AffineSiLUReplay.Valid
    {rows columns : ℕ} (replay : Float32AffineSiLUReplay rows columns) : Prop :=
  replay.affine.Valid ∧
    0 ≤ replay.radius ∧
    ∀ row,
      (replay.activation row).Valid ∧
      (replay.activation row).input.word = (replay.affine.output row).word ∧
      (replay.activation row).enclosure.operation = .silu ∧
      |(replay.affine.output row).toRat| ≤ replay.radius ∧
      |replay.affine.idealOutputRat row| ≤ replay.radius

/-- Check affine and activation records, exact connecting words, the SiLU tag,
and the common rational preactivation region. -/
def Float32AffineSiLUReplay.check
    {rows columns : ℕ} (replay : Float32AffineSiLUReplay rows columns) : Bool :=
  replay.affine.check &&
    decide (0 ≤ replay.radius ∧
      ∀ row,
        (replay.activation row).check = true ∧
        (replay.activation row).input.word = (replay.affine.output row).word ∧
        (replay.activation row).enclosure.operation = .silu ∧
        |(replay.affine.output row).toRat| ≤ replay.radius ∧
        |replay.affine.idealOutputRat row| ≤ replay.radius)

theorem Float32AffineSiLUReplay.check_eq_true_iff
    {rows columns : ℕ} (replay : Float32AffineSiLUReplay rows columns) :
    replay.check = true ↔ replay.Valid := by
  simp [Float32AffineSiLUReplay.check, Float32AffineSiLUReplay.Valid,
    Float32AffineReplay.check_eq_true_iff,
    Float32ActivationReplay.check_eq_true_iff]

/-- Assemble a composed replay from an already accepted affine replay, accepted
coordinatewise activations, exact connecting words, and a bound on the
observed affine outputs.  The common SiLU radius need only cover the observed
radius plus the affine replay's accepted aggregate error: the corresponding
ideal-coordinate bound is transported from the affine certificate rather than
recomputed. -/
theorem Float32AffineSiLUReplay.check_of_observed_radius_and_affine_budget
    {rows columns : ℕ} (replay : Float32AffineSiLUReplay rows columns)
    (observedRadius : ℚ)
    (haffine : replay.affine.check = true)
    (hradius : 0 ≤ replay.radius)
    (hbudget :
      observedRadius + replay.affine.localError ≤ replay.radius)
    (hactivation :
      ∀ row, (replay.activation row).check = true)
    (hword :
      ∀ row,
        (replay.activation row).input.word =
          (replay.affine.output row).word)
    (hoperation :
      ∀ row, (replay.activation row).enclosure.operation = .silu)
    (hobserved :
      ∀ row, |(replay.affine.output row).toRat| ≤ observedRadius) :
    replay.check = true := by
  apply replay.check_eq_true_iff.mpr
  have haffineValid := replay.affine.check_eq_true_iff.mp haffine
  refine ⟨haffineValid, hradius, ?_⟩
  intro row
  have hactivationValid :=
    (replay.activation row).check_eq_true_iff.mp (hactivation row)
  refine ⟨hactivationValid, hword row, hoperation row, ?_, ?_⟩
  · exact (hobserved row).trans
      ((le_add_of_nonneg_right haffineValid.2.2.1).trans hbudget)
  · exact
      (replay.affine.idealOutputRat_abs_le_output_abs_add_localError
        haffine row).trans
        ((add_le_add (hobserved row) (le_refl replay.affine.localError)).trans
          hbudget)

/-- Observed binary32 output of the coordinatewise activation. -/
def Float32AffineSiLUReplay.decodedOutput
    {rows columns : ℕ} (replay : Float32AffineSiLUReplay rows columns) :
    EuclideanSpace ℝ (Fin rows) :=
  WithLp.toLp 2 fun row ↦ (replay.activation row).output.toReal

/-- Exact-real affine--SiLU block declared by the replay. -/
def Float32AffineSiLUReplay.idealBlock
    {rows columns : ℕ} (replay : Float32AffineSiLUReplay rows columns)
    (input : EuclideanSpace ℝ (Fin columns)) :
    EuclideanSpace ℝ (Fin rows) :=
  WithLp.toLp 2 fun row ↦
    sourceSiLU (replay.affine.idealAffine input row)

/-- Sum of the checked coordinatewise activation errors. -/
def Float32AffineSiLUReplay.totalActivationErrorRat
    {rows columns : ℕ} (replay : Float32AffineSiLUReplay rows columns) : ℚ :=
  ∑ row, (replay.activation row).enclosure.localError

/-- Conservative pointwise block budget: local activation error plus the
transported affine mismatch. -/
def Float32AffineSiLUReplay.totalCertifiedErrorRat
    {rows columns : ℕ} (replay : Float32AffineSiLUReplay rows columns) : ℚ :=
  replay.totalActivationErrorRat +
    registeredPairRateRat .silu replay.radius * replay.affine.localError

private theorem finiteWord_toReal_eq_of_word_eq
    {left right : FiniteFloat32Word} (hword : left.word = right.word) :
    left.toReal = right.toReal := by
  simp [FiniteFloat32Word.toReal, FiniteFloat32Word.toRat, hword]

private theorem idealOutputRat_cast_eq
    {rows columns : ℕ} (affine : Float32AffineReplay rows columns)
    (row : Fin rows) :
    (affine.idealOutputRat row : ℝ) =
      affine.idealAffine affine.decodedInput row := by
  simp [Float32AffineReplay.idealOutputRat,
    Float32AffineReplay.idealAffine, Float32AffineReplay.decodedInput,
    FiniteFloat32Word.toReal, Rat.cast_sum]

/-- Each accepted coordinate is bounded by its local activation error plus
the SiLU transport of the observed affine mismatch. -/
theorem Float32AffineSiLUReplay.coordinate_error_le
    {rows columns : ℕ} (replay : Float32AffineSiLUReplay rows columns)
    (hcheck : replay.check = true) (row : Fin rows) :
    |replay.decodedOutput row -
        replay.idealBlock replay.affine.decodedInput row| ≤
      ((replay.activation row).enclosure.localError : ℝ) +
        RegisteredUnaryOp.silu.pairRate (replay.radius : ℝ) *
          |replay.affine.decodedOutput row -
            replay.affine.idealAffine replay.affine.decodedInput row| := by
  have hvalid := replay.check_eq_true_iff.mp hcheck
  rcases hvalid.2.2 row with
    ⟨hactivation, hword, hoperation, hruntimeRat, hidealRat⟩
  have hactivationCheck : (replay.activation row).check = true :=
    (replay.activation row).check_eq_true_iff.mpr hactivation
  have hlocal := (replay.activation row).sound hactivationCheck
  rw [hoperation] at hlocal
  have hwordReal :
      (replay.activation row).input.toReal =
        (replay.affine.output row).toReal :=
    finiteWord_toReal_eq_of_word_eq hword
  rw [hwordReal] at hlocal
  have hradiusReal : 0 ≤ (replay.radius : ℝ) := by
    exact_mod_cast hvalid.2.1
  have hruntimeReal :
      |replay.affine.decodedOutput row| ≤ (replay.radius : ℝ) := by
    change |(replay.affine.output row).toReal| ≤ (replay.radius : ℝ)
    rw [← (replay.affine.output row).cast_toRat, ← Rat.cast_abs]
    exact_mod_cast hruntimeRat
  have hidealReal :
      |replay.affine.idealAffine replay.affine.decodedInput row| ≤
        (replay.radius : ℝ) := by
    rw [← idealOutputRat_cast_eq replay.affine row, ← Rat.cast_abs]
    exact_mod_cast hidealRat
  have hpair := RegisteredUnaryOp.pair_bound .silu hradiusReal
    hruntimeReal hidealReal
  calc
    |replay.decodedOutput row -
        replay.idealBlock replay.affine.decodedInput row| ≤
        |replay.decodedOutput row -
          sourceSiLU (replay.affine.decodedOutput row)| +
        |sourceSiLU (replay.affine.decodedOutput row) -
          sourceSiLU
            (replay.affine.idealAffine replay.affine.decodedInput row)| :=
      by
        simpa [Float32AffineSiLUReplay.idealBlock] using
          (abs_sub_le (replay.decodedOutput row)
            (sourceSiLU (replay.affine.decodedOutput row))
            (sourceSiLU
              (replay.affine.idealAffine replay.affine.decodedInput row)))
    _ ≤ ((replay.activation row).enclosure.localError : ℝ) +
        RegisteredUnaryOp.silu.pairRate (replay.radius : ℝ) *
          |replay.affine.decodedOutput row -
            replay.affine.idealAffine replay.affine.decodedInput row| :=
      add_le_add (by
        change
          |(replay.activation row).output.toReal -
              sourceSiLU (replay.affine.output row).toReal| ≤
            ((replay.activation row).enclosure.localError : ℝ)
        exact hlocal) (by
        simpa [RegisteredUnaryOp.realMap] using hpair)

/-- The entrywise absolute mismatch of the accepted traced block is bounded by
the same conservative budget used for its Euclidean error.  This stronger
aggregation form composes directly with later coordinatewise runtime stages. -/
theorem Float32AffineSiLUReplay.totalCoordinateError_le
    {rows columns : ℕ} (replay : Float32AffineSiLUReplay rows columns)
    (hcheck : replay.check = true) :
    (∑ row, |replay.decodedOutput row -
        replay.idealBlock replay.affine.decodedInput row|) ≤
      (replay.totalCertifiedErrorRat : ℝ) := by
  have hvalid := replay.check_eq_true_iff.mp hcheck
  have haffineError :
      (∑ row,
        |replay.affine.decodedOutput row -
          replay.affine.idealAffine replay.affine.decodedInput row|) ≤
        (replay.affine.localError : ℝ) := by
    rw [replay.affine.totalAbsoluteErrorReal_eq]
    exact_mod_cast hvalid.1.2.2.2
  have hrateNonneg :
      0 ≤ RegisteredUnaryOp.silu.pairRate (replay.radius : ℝ) :=
    RegisteredUnaryOp.pairRate_nonneg .silu (by exact_mod_cast hvalid.2.1)
  calc
    (∑ row, |replay.decodedOutput row -
        replay.idealBlock replay.affine.decodedInput row|) ≤ ∑ row,
        (((replay.activation row).enclosure.localError : ℝ) +
          RegisteredUnaryOp.silu.pairRate (replay.radius : ℝ) *
            |replay.affine.decodedOutput row -
              replay.affine.idealAffine replay.affine.decodedInput row|) :=
      Finset.sum_le_sum fun row _ ↦ replay.coordinate_error_le hcheck row
    _ = (∑ row,
          ((replay.activation row).enclosure.localError : ℝ)) +
        RegisteredUnaryOp.silu.pairRate (replay.radius : ℝ) *
          (∑ row,
            |replay.affine.decodedOutput row -
              replay.affine.idealAffine replay.affine.decodedInput row|) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (∑ row,
          ((replay.activation row).enclosure.localError : ℝ)) +
        RegisteredUnaryOp.silu.pairRate (replay.radius : ℝ) *
          (replay.affine.localError : ℝ) := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left haffineError hrateNonneg)
    _ = (replay.totalCertifiedErrorRat : ℝ) := by
      simp [Float32AffineSiLUReplay.totalCertifiedErrorRat,
        Float32AffineSiLUReplay.totalActivationErrorRat,
        cast_registeredPairRateRat, Rat.cast_sum]

/-- The accepted traced block has a single Euclidean local-evaluation-error
budget obtained by summing coordinatewise activation errors and transporting
the affine replay error through the registered SiLU rate. -/
theorem Float32AffineSiLUReplay.sound
    {rows columns : ℕ} (replay : Float32AffineSiLUReplay rows columns)
    (hcheck : replay.check = true) :
    ‖replay.decodedOutput -
        replay.idealBlock replay.affine.decodedInput‖ ≤
      (replay.totalCertifiedErrorRat : ℝ) := by
  exact (euclidean_norm_le_entrywiseL1 _).trans
    (replay.totalCoordinateError_le hcheck)

/-- Export the composed block through the generic local-error interface. -/
theorem Float32AffineSiLUReplay.toLocalEvaluationErrorCertificate
    {rows columns : ℕ} (replay : Float32AffineSiLUReplay rows columns)
    (hcheck : replay.check = true) :
    LocalEvaluationErrorCertificate replay.idealBlock
      replay.affine.decodedInput replay.decodedOutput
      (replay.totalCertifiedErrorRat : ℝ) := by
  refine
    { localError_nonneg := ?_
      output_error_le := replay.sound hcheck }
  have hvalid := replay.check_eq_true_iff.mp hcheck
  have hactivationNonneg :
      ∀ row, 0 ≤ (replay.activation row).enclosure.localError := by
    intro row
    exact (hvalid.2.2 row).1.1.localError_nonneg
  have hsumNonneg : 0 ≤ replay.totalActivationErrorRat := by
    exact Finset.sum_nonneg fun row _ ↦ hactivationNonneg row
  have hrateNonneg :
      0 ≤ registeredPairRateRat .silu replay.radius := by
    simp only [registeredPairRateRat]
    linarith [hvalid.2.1]
  have htotalRat : 0 ≤ replay.totalCertifiedErrorRat := by
    exact add_nonneg hsumNonneg
      (mul_nonneg hrateNonneg hvalid.1.2.2.1)
  exact_mod_cast htotalRat

/-! ## Finite invocation batches -/

/-- A nonempty finite family of affine--SiLU invocations with one fixed tensor
shape.  Source identity and shared checkpoint tensors remain external binding
obligations. -/
structure Float32AffineSiLUReplayBatch (rows columns : ℕ) where
  expectedCount : ℕ
  entries : List (Float32AffineSiLUReplay rows columns)

def Float32AffineSiLUReplayBatch.Valid
    {rows columns : ℕ}
    (batch : Float32AffineSiLUReplayBatch rows columns) : Prop :=
  0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount ∧
    ∀ replay ∈ batch.entries, replay.Valid

def Float32AffineSiLUReplayBatch.check
    {rows columns : ℕ}
    (batch : Float32AffineSiLUReplayBatch rows columns) : Bool :=
  decide (0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount) &&
    batch.entries.all Float32AffineSiLUReplay.check

theorem Float32AffineSiLUReplayBatch.check_eq_true_iff
    {rows columns : ℕ}
    (batch : Float32AffineSiLUReplayBatch rows columns) :
    batch.check = true ↔ batch.Valid := by
  simp [Float32AffineSiLUReplayBatch.check,
    Float32AffineSiLUReplayBatch.Valid, List.all_eq_true,
    Float32AffineSiLUReplay.check_eq_true_iff, and_assoc]

theorem Float32AffineSiLUReplayBatch.sound_of_mem
    {rows columns : ℕ}
    (batch : Float32AffineSiLUReplayBatch rows columns)
    (hcheck : batch.check = true)
    {replay : Float32AffineSiLUReplay rows columns}
    (hmem : replay ∈ batch.entries) :
    ‖replay.decodedOutput -
        replay.idealBlock replay.affine.decodedInput‖ ≤
      (replay.totalCertifiedErrorRat : ℝ) := by
  have hvalid := (batch.check_eq_true_iff.mp hcheck).2.2 replay hmem
  exact replay.sound <| replay.check_eq_true_iff.mpr hvalid

def Float32AffineSiLUReplayBatch.totalObservedError
    {rows columns : ℕ}
    (batch : Float32AffineSiLUReplayBatch rows columns) : ℝ :=
  (batch.entries.map fun replay ↦
    ‖replay.decodedOutput -
      replay.idealBlock replay.affine.decodedInput‖).sum

def Float32AffineSiLUReplayBatch.totalCertifiedError
    {rows columns : ℕ}
    (batch : Float32AffineSiLUReplayBatch rows columns) : ℝ :=
  (batch.entries.map fun replay ↦
    (replay.totalCertifiedErrorRat : ℝ)).sum

theorem Float32AffineSiLUReplayBatch.totalObservedError_le
    {rows columns : ℕ}
    (batch : Float32AffineSiLUReplayBatch rows columns)
    (hcheck : batch.check = true) :
    batch.totalObservedError ≤ batch.totalCertifiedError := by
  apply List.sum_le_sum
  intro replay hmem
  exact batch.sound_of_mem hcheck hmem

/-! ## Positive and negative fixtures -/

def zeroWord : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

/-- The exact affine stage computes `1/2 * 1 + 0 = 1/2`, which is exactly the
input word of the accepted SiLU replay. -/
def halfAffineReplay : Float32AffineReplay 1 1 where
  input := ![positiveOne]
  weight := ![Float32ActivationReplayCertificate.positiveHalf]
  bias := ![zeroWord]
  output := ![Float32ActivationReplayCertificate.positiveHalf]
  localError := 0

theorem halfAffineReplay_is_accepted : halfAffineReplay.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat, halfAffineReplay,
    positiveOne, Float32ActivationReplayCertificate.positiveHalf,
    zeroWord, FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    rowMajorIndex]

def halfSiLUReplay : Float32AffineSiLUReplay 1 1 where
  affine := halfAffineReplay
  activation := fun _ ↦ siluHalfReplay
  radius := 1

theorem halfSiLUReplay_is_accepted : halfSiLUReplay.check = true := by
  apply (Float32AffineSiLUReplay.check_eq_true_iff halfSiLUReplay).mpr
  refine ⟨(Float32AffineReplay.check_eq_true_iff halfAffineReplay).mp
      halfAffineReplay_is_accepted, by norm_num [halfSiLUReplay], ?_⟩
  intro row
  fin_cases row
  refine ⟨(Float32ActivationReplay.check_eq_true_iff siluHalfReplay).mp
      siluHalfReplay_is_accepted, rfl, rfl, ?_, ?_⟩
  · norm_num [halfSiLUReplay, halfAffineReplay,
      Float32ActivationReplayCertificate.positiveHalf_toRat]
  · norm_num [halfSiLUReplay, halfAffineReplay,
      Float32AffineReplay.idealOutputRat,
      positiveOne, Float32ActivationReplayCertificate.positiveHalf,
      zeroWord, FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
      rowMajorIndex]

theorem halfSiLUReplay_sound :
    ‖halfSiLUReplay.decodedOutput -
        halfSiLUReplay.idealBlock halfSiLUReplay.affine.decodedInput‖ ≤
      (halfSiLUReplay.totalCertifiedErrorRat : ℝ) :=
  halfSiLUReplay.sound halfSiLUReplay_is_accepted

def halfSiLUReplayBatch : Float32AffineSiLUReplayBatch 1 1 where
  expectedCount := 1
  entries := [halfSiLUReplay]

theorem halfSiLUReplayBatch_is_accepted :
    halfSiLUReplayBatch.check = true := by
  simp [Float32AffineSiLUReplayBatch.check, halfSiLUReplayBatch,
    halfSiLUReplay_is_accepted]

theorem halfSiLUReplayBatch_total_error_is_bounded :
    halfSiLUReplayBatch.totalObservedError ≤
      halfSiLUReplayBatch.totalCertifiedError :=
  halfSiLUReplayBatch.totalObservedError_le halfSiLUReplayBatch_is_accepted

/-- Empty batches are rejected even when their declared count is zero. -/
def emptySiLUReplayBatch : Float32AffineSiLUReplayBatch 1 1 where
  expectedCount := 0
  entries := []

theorem emptySiLUReplayBatch_is_rejected :
    emptySiLUReplayBatch.check = false := by
  norm_num [Float32AffineSiLUReplayBatch.check, emptySiLUReplayBatch]

/-- This affine replay is independently valid and produces the binary32 word
for `2`, rather than the word for `1/2`. -/
def twoAffineReplay : Float32AffineReplay 1 1 where
  input := ![positiveOne]
  weight := ![Float32AffineReplayCertificate.positiveTwo]
  bias := ![zeroWord]
  output := ![Float32AffineReplayCertificate.positiveTwo]
  localError := 0

theorem twoAffineReplay_is_accepted : twoAffineReplay.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat, twoAffineReplay,
    positiveOne, Float32AffineReplayCertificate.positiveTwo,
    zeroWord, FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    rowMajorIndex]

/-- The affine and activation components are individually accepted and the
activation is SiLU, but the activation consumes a different binary32 word
from the affine output.  Composition therefore rejects the pair. -/
def miswiredSiLUReplay : Float32AffineSiLUReplay 1 1 where
  affine := twoAffineReplay
  activation := fun _ ↦ siluHalfReplay
  radius := 3

theorem miswiredSiLUReplay_is_rejected :
    miswiredSiLUReplay.check = false := by
  apply Bool.eq_false_iff.mpr
  intro hcheck
  have hvalid :=
    (Float32AffineSiLUReplay.check_eq_true_iff miswiredSiLUReplay).mp hcheck
  have hword := (hvalid.2.2 (0 : Fin 1)).2.1
  norm_num [miswiredSiLUReplay, twoAffineReplay, siluHalfReplay,
    Float32AffineReplayCertificate.positiveTwo,
    Float32ActivationReplayCertificate.positiveHalf] at hword

/-- Both component replays are individually valid here, but sigmoid is not
the registered hidden-site activation, so the composed block rejects it. -/
def wrongOperationReplay : Float32AffineSiLUReplay 1 1 where
  affine := halfAffineReplay
  activation := fun _ ↦ sigmoidHalfReplay
  radius := 1

theorem wrongOperationReplay_is_rejected :
    wrongOperationReplay.check = false := by
  apply Bool.eq_false_iff.mpr
  intro hcheck
  have hvalid :=
    (Float32AffineSiLUReplay.check_eq_true_iff wrongOperationReplay).mp hcheck
  have hoperation := (hvalid.2.2 (0 : Fin 1)).2.2.1
  simp [wrongOperationReplay, sigmoidHalfReplay,
    ActivationCertificate.operation,
    RationalActivationEnclosureCertificate.sigmoidHalf] at hoperation

/-- A region that omits the observed and ideal preactivation cannot be used
to transport the affine error through SiLU. -/
def tooSmallRegionReplay : Float32AffineSiLUReplay 1 1 :=
  { halfSiLUReplay with radius := 1 / 4 }

theorem tooSmallRegionReplay_is_rejected :
    tooSmallRegionReplay.check = false := by
  apply Bool.eq_false_iff.mpr
  intro hcheck
  have hvalid :=
    (Float32AffineSiLUReplay.check_eq_true_iff tooSmallRegionReplay).mp hcheck
  have hruntime := (hvalid.2.2 (0 : Fin 1)).2.2.2.1
  norm_num [tooSmallRegionReplay, halfSiLUReplay, halfAffineReplay,
    Float32ActivationReplayCertificate.positiveHalf_toRat] at hruntime

#print axioms Float32AffineSiLUReplay.check_eq_true_iff
#print axioms Float32AffineSiLUReplay.check_of_observed_radius_and_affine_budget
#print axioms Float32AffineSiLUReplay.coordinate_error_le
#print axioms Float32AffineSiLUReplay.totalCoordinateError_le
#print axioms Float32AffineSiLUReplay.sound
#print axioms Float32AffineSiLUReplay.toLocalEvaluationErrorCertificate
#print axioms Float32AffineSiLUReplayBatch.check_eq_true_iff
#print axioms Float32AffineSiLUReplayBatch.totalObservedError_le
#print axioms halfSiLUReplay_is_accepted
#print axioms halfSiLUReplayBatch_total_error_is_bounded
#print axioms emptySiLUReplayBatch_is_rejected
#print axioms miswiredSiLUReplay_is_rejected
#print axioms wrongOperationReplay_is_rejected
#print axioms tooSmallRegionReplay_is_rejected

end

end Float32AffineSiLUReplayCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
