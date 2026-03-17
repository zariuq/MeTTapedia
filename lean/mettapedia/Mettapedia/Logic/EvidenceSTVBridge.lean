import Mettapedia.Logic.PLNDeduction
import Mettapedia.Logic.PLNDistributional
import Mettapedia.Logic.EvidenceQuantale

/-!
# BinaryEvidence/STV Bridge

Bridges the two STV record types currently used in PLN modules:

- `PLNDeduction.STV`
- `PLN.Distributional.SimpleTruthValue`

This file proves they are isomorphic by explicit conversion functions.
-/

noncomputable section

namespace Mettapedia.Logic.EvidenceSTVBridge

open Mettapedia.Logic
open scoped ENNReal

abbrev DeductionSTV := PLNDeduction.STV
abbrev DistributionalSTV := PLN.Distributional.SimpleTruthValue

/-- Convert distributional STV to deduction STV. -/
def distributionalToDeduction (s : DistributionalSTV) : DeductionSTV where
  strength := s.strength
  confidence := s.confidence
  strength_nonneg := s.strength_nonneg
  strength_le_one := s.strength_le_one
  confidence_nonneg := s.confidence_nonneg
  confidence_le_one := s.confidence_le_one

/-- Convert deduction STV to distributional STV. -/
def deductionToDistributional (s : DeductionSTV) : DistributionalSTV where
  strength := s.strength
  confidence := s.confidence
  strength_nonneg := s.strength_nonneg
  strength_le_one := s.strength_le_one
  confidence_nonneg := s.confidence_nonneg
  confidence_le_one := s.confidence_le_one

/-- Roundtrip: distributional → deduction → distributional is identity. -/
@[simp] theorem distributional_roundtrip (s : DistributionalSTV) :
    deductionToDistributional (distributionalToDeduction s) = s := by
  cases s
  rfl

/-- Roundtrip: deduction → distributional → deduction is identity. -/
@[simp] theorem deduction_roundtrip (s : DeductionSTV) :
    distributionalToDeduction (deductionToDistributional s) = s := by
  cases s
  rfl

/-- Package the bridge as an equivalence of STV carriers. -/
def stvEquiv : DistributionalSTV ≃ DeductionSTV where
  toFun := distributionalToDeduction
  invFun := deductionToDistributional
  left_inv := distributional_roundtrip
  right_inv := deduction_roundtrip

/-- BinaryEvidence view into deduction STV using the canonical evidence semantics. -/
def evidenceToDeductionSTV (κ : ℝ≥0∞) (e : EvidenceQuantale.BinaryEvidence) : DeductionSTV where
  strength := PLNDeduction.clamp01 ((EvidenceQuantale.BinaryEvidence.toStrength e).toReal)
  confidence := PLNDeduction.clamp01 ((EvidenceQuantale.BinaryEvidence.toConfidence κ e).toReal)
  strength_nonneg := PLNDeduction.clamp01_nonneg _
  strength_le_one := PLNDeduction.clamp01_le_one _
  confidence_nonneg := PLNDeduction.clamp01_nonneg _
  confidence_le_one := PLNDeduction.clamp01_le_one _

/-- BinaryEvidence view into distributional STV via the proven STV equivalence. -/
def evidenceToDistributionalSTV (κ : ℝ≥0∞) (e : EvidenceQuantale.BinaryEvidence) : DistributionalSTV :=
  deductionToDistributional (evidenceToDeductionSTV κ e)

end Mettapedia.Logic.EvidenceSTVBridge
