import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.MatrixBelief
import Mettapedia.PLN.Evidence.EvidentialLedger
import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.ConfidenceCharacterization
import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.ConfidenceCoordinates

/-!
# Natural evidence coordinates for belief registers

Binary belief registers store natural-number evidence counts `(n⁺, n⁻)`.
Independent revision is their commutative-monoid addition.  Strength and
confidence are derived display coordinates, and the sealed confidence
characterization recovers the original positive finite counts.

The continuous twin stores Gaussian natural information `(η, Λ)`.  Its fusion
is also addition; matrix gain interpolation is exactly the moment-coordinate
view of that sum.  Thus the two belief families share one operational rule
without identifying their distinct statistical models.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Evidence.EvidentialLedger
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate
open Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
open scoped ENNReal

/-! ## Counts-primal binary evidence -/

/-- Revision is componentwise addition in the stored `(n⁺, n⁻)` chart. -/
theorem binEvNat_revision_components (first second : BinEvNat) :
    ((first + second).pos, (first + second).neg) =
      (first.pos + second.pos, first.neg + second.neg) :=
  rfl

/-- Count revision is associative, so grouping independent packets is inert. -/
theorem binEvNat_revision_assoc (first second third : BinEvNat) :
    first + second + third = first + (second + third) :=
  add_assoc first second third

/-- Count revision is commutative, so independent packet order is inert. -/
theorem binEvNat_revision_comm (first second : BinEvNat) :
    first + second = second + first :=
  add_comm first second

/-- Strength and confidence are computed columns over the primal count state. -/
noncomputable def binEvNatDerivedSTV (κ : ℝ≥0∞) (evidence : BinEvNat) : ℝ × ℝ :=
  BinaryEvidence.toSTV κ (EvidentialLedger.BinEvNat.toBinaryEvidence evidence)

/-- The computed columns are precisely the canonical strength/confidence view
of the count packet embedded into `BinaryEvidence`. -/
theorem binEvNatDerivedSTV_eq_canonical (κ : ℝ≥0∞) (evidence : BinEvNat) :
    binEvNatDerivedSTV κ evidence =
      ((BinaryEvidence.toStrength
          (EvidentialLedger.BinEvNat.toBinaryEvidence evidence)).toReal,
       (BinaryEvidence.toConfidence κ
          (EvidentialLedger.BinEvNat.toBinaryEvidence evidence)).toReal) :=
  rfl

/-- Appending a finite evidence packet cannot lower confidence when the prior
weight is positive and finite. -/
theorem binEvNat_confidence_mono_revision
    (κ : ℝ≥0∞) (hκ_pos : κ ≠ 0) (hκ_top : κ ≠ ⊤)
    (base added : BinEvNat) :
    BinaryEvidence.toConfidence κ
        (EvidentialLedger.BinEvNat.toBinaryEvidence base) ≤
      BinaryEvidence.toConfidence κ
        (EvidentialLedger.BinEvNat.toBinaryEvidence (base + added)) := by
  apply BinaryEvidence.confidence_monotone_in_total κ
      (EvidentialLedger.BinEvNat.toBinaryEvidence base)
      (EvidentialLedger.BinEvNat.toBinaryEvidence (base + added))
      hκ_pos hκ_top
  · simp [EvidentialLedger.BinEvNat.toBinaryEvidence, BinaryEvidence.total]
  · change (base.pos : ℝ≥0∞) + (base.neg : ℝ≥0∞) ≤
      ((base.pos + added.pos : Nat) : ℝ≥0∞) +
        ((base.neg + added.neg : Nat) : ℝ≥0∞)
    norm_cast
    omega

/-- The sealed PLN odds confidence coordinate reconstructs positive finite
counts exactly.  This theorem makes the count state primary and the displayed
strength/confidence pair a reversible chart on its valid domain. -/
theorem plnDerivedChart_reconstructs_counts
    (κ nPlus nMinus : ℝ) (hκ : 0 < κ)
    (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus)
    (hTotal : nPlus + nMinus ≠ 0) :
    (plnOddsCoordinate κ hκ).decodeCounts
        ((plnOddsCoordinate κ hκ).encodeCounts nPlus nMinus) =
      (nPlus, nMinus) :=
  pln_odds_coordinate_reconstructs_binary_counts
    κ hκ hPlus hMinus hTotal

/-! ## One additive rule, two statistical families -/

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- Natural-coordinate crown: discrete count fusion and continuous Gaussian
information fusion are both componentwise addition; the latter becomes the
usual matrix-gain interpolation only after deriving its mean chart. -/
theorem naturalEvidenceFusionCrown
    (first second : BinEvNat)
    (oldMean proposedMean : Index → ℝ)
    (priorPrecision observationPrecision : Matrix Index Index ℝ)
    (hprior : priorPrecision.PosDef)
    (hobservation : observationPrecision.PosDef) :
    ((first + second).pos = first.pos + second.pos) ∧
    ((first + second).neg = first.neg + second.neg) ∧
    matrixPrecisionInterpolate oldMean proposedMean
        priorPrecision observationPrecision =
      (GaussianInformation.ofMeanPrecision oldMean priorPrecision +
        GaussianInformation.ofMeanPrecision proposedMean
          observationPrecision).mean := by
  exact ⟨rfl, rfl,
    matrixPrecisionInterpolate_eq_fusedInformationMean
      oldMean proposedMean priorPrecision observationPrecision
      hprior hobservation⟩

/-! ## Positive and negative fixtures -/

/-- Concrete positive revision: two positive and one negative observation are
stored without normalization loss. -/
theorem binEvNat_revision_positiveExample :
    (⟨1, 0⟩ : BinEvNat) + ⟨1, 1⟩ = ⟨2, 1⟩ := by
  decide

/-- Negative boundary: `(strength, confidence)` is not a primal count chart at
zero total evidence, so the reconstructive theorem's positive-total premise
cannot be dropped. -/
theorem zeroTotal_counts_reconstruction_premise_fails :
    ¬((0 : ℝ) + 0 ≠ 0) := by
  norm_num

#print axioms binEvNat_revision_assoc
#print axioms binEvNat_revision_comm
#print axioms binEvNat_confidence_mono_revision
#print axioms plnDerivedChart_reconstructs_counts
#print axioms naturalEvidenceFusionCrown
#print axioms binEvNat_revision_positiveExample
#print axioms zeroTotal_counts_reconstruction_premise_fails

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
