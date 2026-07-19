import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.NaturalEvidenceCoordinates

/-!
# Overlap-aware evidence fusion

Natural-coordinate addition is calibrated only for fresh evidence.  This file
models a known scalar overlap between two Gaussian information packets.  Naive
addition overstates precision by exactly the overlap; subtracting that common
information, equivalently discounting the second packet, restores the declared
precision.  The resulting variance-calibration gap is also quantified exactly.

The final section gives the same bookkeeping rule directly in the primal
binary count chart `(n⁺, n⁻)`.  These are finite-dimensional overlap identities,
not an estimator for unknown dependence or a claim that all correlations reduce
to one scalar overlap.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Mettapedia.PLN.Evidence

/-! ## Scalar Gaussian overlap -/

/-- Precision reported by treating both packets as independent. -/
noncomputable def naiveOverlappingPrecision
    (priorPrecision firstPrecision secondPrecision : ℝ) : ℝ :=
  priorPrecision + firstPrecision + secondPrecision

/-- Precision after removing information shared by both packets exactly once. -/
noncomputable def overlapCalibratedPrecision
    (priorPrecision firstPrecision secondPrecision overlap : ℝ) : ℝ :=
  priorPrecision + firstPrecision + secondPrecision - overlap

/-- A declared overlap is admissible when it is nonnegative and no larger than
either contributing packet. -/
def ValidPrecisionOverlap
    (firstPrecision secondPrecision overlap : ℝ) : Prop :=
  0 ≤ overlap ∧ overlap ≤ firstPrecision ∧ overlap ≤ secondPrecision

/-- Naive addition overstates calibrated precision by exactly the overlap. -/
theorem naivePrecision_sub_calibrated_eq_overlap
    (priorPrecision firstPrecision secondPrecision overlap : ℝ) :
    naiveOverlappingPrecision priorPrecision firstPrecision secondPrecision -
        overlapCalibratedPrecision priorPrecision firstPrecision
          secondPrecision overlap =
      overlap := by
  simp [naiveOverlappingPrecision, overlapCalibratedPrecision]

/-- Fraction of the second packet retained after removing a known overlap. -/
noncomputable def overlapRetention
    (secondPrecision overlap : ℝ) : ℝ :=
  1 - overlap / secondPrecision

/-- Discounting the second packet by its overlap fraction retains exactly its
non-overlapping precision. -/
theorem secondPrecision_mul_overlapRetention
    (secondPrecision overlap : ℝ) (hsecond : secondPrecision ≠ 0) :
    secondPrecision * overlapRetention secondPrecision overlap =
      secondPrecision - overlap := by
  unfold overlapRetention
  field_simp [hsecond]

/-- Overlap-aware subtraction and discounted natural-coordinate addition are
the same precision update. -/
theorem overlapCalibratedPrecision_eq_discountedAddition
    (priorPrecision firstPrecision secondPrecision overlap : ℝ)
    (hsecond : secondPrecision ≠ 0) :
    overlapCalibratedPrecision priorPrecision firstPrecision
        secondPrecision overlap =
      priorPrecision + firstPrecision +
        secondPrecision * overlapRetention secondPrecision overlap := by
  rw [secondPrecision_mul_overlapRetention secondPrecision overlap hsecond]
  unfold overlapCalibratedPrecision
  ring

/-- Under a valid overlap and positive prior precision, the calibrated
posterior variance exceeds the naively reported variance by the exact rational
gap shown here. -/
theorem overlapVarianceGap_exact
    (priorPrecision firstPrecision secondPrecision overlap : ℝ)
    (hprior : 0 < priorPrecision)
    (hvalid : ValidPrecisionOverlap firstPrecision secondPrecision overlap) :
    1 / overlapCalibratedPrecision priorPrecision firstPrecision
          secondPrecision overlap -
        1 / naiveOverlappingPrecision priorPrecision firstPrecision
          secondPrecision =
      overlap /
        (overlapCalibratedPrecision priorPrecision firstPrecision
            secondPrecision overlap *
          naiveOverlappingPrecision priorPrecision firstPrecision
            secondPrecision) := by
  have hfirst : 0 ≤ firstPrecision := le_trans hvalid.1 hvalid.2.1
  have hsecond : 0 ≤ secondPrecision := le_trans hvalid.1 hvalid.2.2
  have hnaive : 0 <
      naiveOverlappingPrecision priorPrecision firstPrecision secondPrecision := by
    unfold naiveOverlappingPrecision
    positivity
  have hcalibrated : 0 < overlapCalibratedPrecision
      priorPrecision firstPrecision secondPrecision overlap := by
    unfold overlapCalibratedPrecision
    nlinarith [hvalid.2.2]
  have hnaive' : priorPrecision + firstPrecision + secondPrecision ≠ 0 := by
    simpa [naiveOverlappingPrecision] using hnaive.ne'
  have hcalibrated' :
      priorPrecision + firstPrecision + secondPrecision - overlap ≠ 0 := by
    simpa [overlapCalibratedPrecision] using hcalibrated.ne'
  unfold overlapCalibratedPrecision naiveOverlappingPrecision
  field_simp [hnaive', hcalibrated']
  ring

/-- Positive overlap makes naive independent-evidence addition strictly
overconfident: its reported variance is strictly too small. -/
theorem naiveVariance_lt_calibratedVariance_of_overlap
    (priorPrecision firstPrecision secondPrecision overlap : ℝ)
    (hprior : 0 < priorPrecision)
    (hvalid : ValidPrecisionOverlap firstPrecision secondPrecision overlap)
    (hoverlap : 0 < overlap) :
    1 / naiveOverlappingPrecision priorPrecision firstPrecision secondPrecision <
      1 / overlapCalibratedPrecision priorPrecision firstPrecision
        secondPrecision overlap := by
  have hfirst : 0 ≤ firstPrecision := le_trans hvalid.1 hvalid.2.1
  have hsecond : 0 ≤ secondPrecision := le_trans hvalid.1 hvalid.2.2
  have hnaive : 0 <
      naiveOverlappingPrecision priorPrecision firstPrecision secondPrecision := by
    unfold naiveOverlappingPrecision
    positivity
  have hcalibrated : 0 < overlapCalibratedPrecision
      priorPrecision firstPrecision secondPrecision overlap := by
    unfold overlapCalibratedPrecision
    nlinarith [hvalid.2.2]
  have hgap := overlapVarianceGap_exact priorPrecision firstPrecision
    secondPrecision overlap hprior hvalid
  have hpositive : 0 < overlap /
      (overlapCalibratedPrecision priorPrecision firstPrecision
          secondPrecision overlap *
        naiveOverlappingPrecision priorPrecision firstPrecision
          secondPrecision) :=
    div_pos hoverlap (mul_pos hcalibrated hnaive)
  linarith

/-! ## Primal `(n⁺, n⁻)` overlap bookkeeping -/

/-- Remove a known componentwise overlap from an incoming binary count packet. -/
def discountBinEvNat (packet overlap : BinEvNat) : BinEvNat :=
  ⟨packet.pos - overlap.pos, packet.neg - overlap.neg⟩

/-- A binary count overlap is valid when it is componentwise contained in both
packets whose shared observations it represents. -/
def ValidBinEvNatOverlap
    (first second overlap : BinEvNat) : Prop :=
  overlap.pos ≤ first.pos ∧ overlap.neg ≤ first.neg ∧
    overlap.pos ≤ second.pos ∧ overlap.neg ≤ second.neg

/-- Discounting a valid overlap removes it exactly: reattaching the shared
packet reconstructs the original second packet componentwise. -/
theorem discountBinEvNat_add_overlap_eq
    (first second overlap : BinEvNat)
    (hvalid : ValidBinEvNatOverlap first second overlap) :
    discountBinEvNat second overlap + overlap = second := by
  ext
  · exact Nat.sub_add_cancel hvalid.2.2.1
  · exact Nat.sub_add_cancel hvalid.2.2.2

/-- Revise counts after discounting the second packet's declared overlap with
the first packet. -/
def overlapCalibratedBinEvNatRevision
    (base first second overlap : BinEvNat) : BinEvNat :=
  base + first + discountBinEvNat second overlap

/-- Componentwise count subtraction is the native overlap-aware revision rule. -/
theorem overlapCalibratedBinEvNatRevision_components
    (base first second overlap : BinEvNat) :
    (overlapCalibratedBinEvNatRevision base first second overlap).pos =
        base.pos + first.pos + (second.pos - overlap.pos) ∧
      (overlapCalibratedBinEvNatRevision base first second overlap).neg =
        base.neg + first.neg + (second.neg - overlap.neg) := by
  exact ⟨rfl, rfl⟩

/-- Positive fixture: zero overlap recovers independent count addition. -/
theorem zeroOverlap_recovers_independentCountAddition
    (base first second : BinEvNat) :
    overlapCalibratedBinEvNatRevision base first second ⟨0, 0⟩ =
      base + first + second := by
  ext <;> simp [overlapCalibratedBinEvNatRevision, discountBinEvNat]

/-- Negative fixture: adding one scalar observation twice overstates unit-prior
precision by one and understates variance by `1/6`. -/
theorem duplicateObservation_overconfidence_negativeExample :
    naiveOverlappingPrecision 1 1 1 = 3 ∧
      overlapCalibratedPrecision 1 1 1 1 = 2 ∧
      1 / overlapCalibratedPrecision 1 1 1 1 -
          1 / naiveOverlappingPrecision 1 1 1 = (1 / 6 : ℝ) := by
  norm_num [naiveOverlappingPrecision, overlapCalibratedPrecision]

/-- Count-level duplicate fixture: after declaring the shared positive count,
the second copy contributes no fresh evidence. -/
theorem duplicatePositiveCount_discounted_negativeExample :
    overlapCalibratedBinEvNatRevision ⟨0, 0⟩ ⟨1, 0⟩ ⟨1, 0⟩ ⟨1, 0⟩ =
      ⟨1, 0⟩ := by
  decide

#print axioms naivePrecision_sub_calibrated_eq_overlap
#print axioms overlapCalibratedPrecision_eq_discountedAddition
#print axioms overlapVarianceGap_exact
#print axioms naiveVariance_lt_calibratedVariance_of_overlap
#print axioms discountBinEvNat_add_overlap_eq
#print axioms zeroOverlap_recovers_independentCountAddition
#print axioms duplicateObservation_overconfidence_negativeExample
#print axioms duplicatePositiveCount_discounted_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
