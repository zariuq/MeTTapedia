import Mettapedia.MachineLearning.NeuralNetworks.Architecture.StateCarrier
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.NaturalEvidenceCoordinates
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.WeightedEvidenceDynamics

/-!
# Evidence-coordinate belief carriers

The primal state of each carrier is evidence, not its displayed
strength-confidence chart.  Exact natural evidence uses additive revision;
weighted evidence uses fade-then-fuse with an explicit retention route.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

open StateCarrier
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Evidence.EvidentialLedger
open Mettapedia.PLN.Evidence.EvidenceQuantale
open scoped ENNReal

/-! ## Additive natural-count evidence -/

/-- Exact count evidence as a carrier.  The confidence weight is immutable
slow configuration used only to derive the observation chart. -/
noncomputable def naturalEvidenceCarrier :
    StateCarrier Unit ℝ≥0∞ BinEvNat BinEvNat BinEvNat Unit BinEvNat
      (ℝ × ℝ) (ℝ × ℝ) where
  initialState := fun _environment _confidenceWeight => 0
  read := fun _environment _confidenceWeight evidence => evidence
  route := fun _environment _confidenceWeight _fresh _state _read => ()
  propose := fun _environment _confidenceWeight fresh _state _read _route => fresh
  write := fun _environment _confidenceWeight _fresh state _route proposal =>
    state + proposal
  observe := fun _environment confidenceWeight evidence =>
    binEvNatDerivedSTV confidenceWeight evidence
  policy := fun _environment _confidenceWeight observation => observation

/-- One exact-count carrier step is precisely componentwise evidence
revision. -/
@[simp] theorem naturalEvidenceCarrier_step_eq
    (confidenceWeight : ℝ≥0∞) (fresh state : BinEvNat) :
    naturalEvidenceCarrier.step () confidenceWeight fresh state = state + fresh :=
  rfl

/-- A nonzero evidence packet genuinely moves the natural-count carrier. -/
theorem naturalEvidenceCarrier_positive_revision :
    naturalEvidenceCarrier.step () 1 (⟨1, 1⟩ : BinEvNat) ⟨1, 0⟩ =
      ⟨2, 1⟩ := by
  exact binEvNat_revision_positiveExample

/-- The zero packet is the exact no-update boundary. -/
theorem naturalEvidenceCarrier_zero_packet (state : BinEvNat) :
    naturalEvidenceCarrier.step () 1 0 state = state := by
  simp

/-! ## Weighted evidence with explicit retention -/

/-- One temporal weighted-evidence write: route old evidence by `retention`,
then fuse the fresh packet at full strength. -/
structure RetentionEvidenceCommand where
  retention : ℝ≥0∞
  fresh : WeightedEvidence

/-- Learned-retention belief dynamics as a distinct carrier from exact
additive evidence.  The retention is exposed as the route, so fading cannot be
mistaken for ordinary independent-evidence addition. -/
noncomputable def weightedEvidenceCarrier :
    StateCarrier Unit ℝ≥0∞ RetentionEvidenceCommand WeightedEvidence
      WeightedEvidence ℝ≥0∞ WeightedEvidence (ℝ × ℝ) (ℝ × ℝ) where
  initialState := fun _environment _confidenceWeight => 0
  read := fun _environment _confidenceWeight evidence => evidence
  route := fun _environment _confidenceWeight command _state _read =>
    command.retention
  propose := fun _environment _confidenceWeight command _state _read _retention =>
    command.fresh
  write := fun _environment _confidenceWeight _command state retention fresh =>
    WeightedEvidence.fadeThenFuse retention state fresh
  observe := fun _environment confidenceWeight evidence =>
    WeightedEvidence.derivedSTV confidenceWeight evidence
  policy := fun _environment _confidenceWeight observation => observation

/-- One weighted carrier step is exactly the existing fade-then-fuse update. -/
@[simp] theorem weightedEvidenceCarrier_step_eq
    (confidenceWeight : ℝ≥0∞) (command : RetentionEvidenceCommand)
    (state : WeightedEvidence) :
    weightedEvidenceCarrier.step () confidenceWeight command state =
      WeightedEvidence.fadeThenFuse command.retention state command.fresh := rfl

/-- Unit retention recovers exact weighted-evidence addition. -/
theorem weightedEvidenceCarrier_unitRetention_eq_add
    (confidenceWeight : ℝ≥0∞) (old fresh : WeightedEvidence) :
    weightedEvidenceCarrier.step () confidenceWeight ⟨1, fresh⟩ old =
      old + fresh := by
  exact WeightedEvidence.fadeThenFuse_one old fresh

/-- Fractional retention can lower confidence.  Consequently the weighted
carrier is not merely the additive carrier with a different display chart. -/
theorem weightedEvidenceCarrier_halfRetention_lowersConfidence :
    BinaryEvidence.toConfidence 1
        (weightedEvidenceCarrier.step () 1
          ⟨(1 / 2 : ℝ≥0∞), 0⟩ (⟨2, 0⟩ : WeightedEvidence)) <
      BinaryEvidence.toConfidence 1 (⟨2, 0⟩ : WeightedEvidence) := by
  simpa [WeightedEvidence.fadeThenFuse] using
    fractionalFade_lowersConfidence_negativeExample

#print axioms naturalEvidenceCarrier_step_eq
#print axioms naturalEvidenceCarrier_positive_revision
#print axioms naturalEvidenceCarrier_zero_packet
#print axioms weightedEvidenceCarrier_step_eq
#print axioms weightedEvidenceCarrier_unitRetention_eq_add
#print axioms weightedEvidenceCarrier_halfRetention_lowersConfidence

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
