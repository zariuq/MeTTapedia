import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemantics
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemanticsInf

/-!
# Finite/Counting Fuzzy Quantifier Semantics

Finite-domain Chapter-11 fuzzy quantifier semantics, explicitly packaged as the
counting-instance front door.

This module does two things:

- re-exports the existing finite/counting layer under `...Fin` names
- proves that bounded finite profiles reduce exactly to the arbitrary-domain
  proxy-cut semantics via the normalized counting capacity
-/

namespace Mettapedia.Logic.PLNFirstOrder

open scoped unitInterval

abbrev FuzzyQuantifierParamsFin := FuzzyQuantifierParams

abbrev nearOneFin := nearOne
abbrev nearZeroFin := nearZero
noncomputable abbrev witnessCountFin := @witnessCount
noncomputable abbrev witnessFractionFin := @witnessFraction
noncomputable abbrev nearOneFractionFin := @nearOneFraction
noncomputable abbrev nearZeroFractionFin := @nearZeroFraction
noncomputable abbrev fuzzyExistsScoreFin := @fuzzyExistsScore
abbrev fuzzyIntervalHoldsFin := @fuzzyIntervalHolds
abbrev fuzzyForAllHoldsFin := @fuzzyForAllHolds
abbrev fuzzyThereExistsHoldsFin := @fuzzyThereExistsHolds
abbrev conjoinProfileFin := @conjoinProfile
abbrev QFMComposeFin := QFMCompose
abbrev QFMSyllogismEnvelopeFin := QFMSyllogismEnvelope
noncomputable abbrev qfmMulFin := qfmMul
noncomputable abbrev qfmMinFin := qfmMin
noncomputable abbrev qfmLukasiewiczFin := qfmLukasiewicz
noncomputable abbrev qfmProbSumFin := qfmProbSum

abbrev nearZeroFractionFin_eq_nearOneFractionFin_one_sub :=
  @nearZeroFraction_eq_nearOneFraction_one_sub

abbrev nearOneFractionFin_in_unit := @nearOneFraction_in_unit
abbrev nearZeroFractionFin_in_unit := @nearZeroFraction_in_unit
abbrev nearOneFractionFin_mono_of_pointwise := @nearOneFraction_mono_of_pointwise
abbrev nearOneFractionFin_eq_of_signatureEq := @nearOneFraction_eq_of_signatureEq
abbrev fuzzyThereExistsHoldsFin_iff_nearOneComplement :=
  @fuzzyThereExistsHolds_iff_nearOneComplement
abbrev fuzzyExistsScoreFin_mono_of_pointwise := @fuzzyExistsScore_mono_of_pointwise
abbrev fuzzyForAllHoldsFin_mono_of_pointwise := @fuzzyForAllHolds_mono_of_pointwise
abbrev fuzzyIntervalHoldsFin_iff_of_signatureEq := @fuzzyIntervalHolds_iff_of_signatureEq
abbrev fuzzyForAllHoldsFin_iff_of_signatureEq := @fuzzyForAllHolds_iff_of_signatureEq

/-- Finite Chapter-11 parameters viewed as arbitrary-domain fuzzy parameters. -/
def FuzzyQuantifierParams.toInf (p : FuzzyQuantifierParams) : FuzzyQuantifierParamsInf where
  ε := p.ε
  LPC := p.LPC
  UPC := p.UPC
  PCL := p.PCL
  hε := p.hε
  hLPC := p.hLPC
  hUPC := p.hUPC
  hPCL := p.hPCL
  hLPC_le_UPC := p.hLPC_le_UPC

/-- A bounded finite profile promoted into the arbitrary-domain fuzzy-profile type. -/
def boundedProfileFinToInf
    {U : Type*} (profile : U → ℝ) (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    FuzzyProfile U :=
  FuzzyProfile.ofFn profile hprofile

@[simp] theorem boundedProfileFinToInf_apply
    {U : Type*} (profile : U → ℝ) (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) (u : U) :
    ((boundedProfileFinToInf profile hprofile) u : ℝ) = profile u :=
  FuzzyProfile.ofFn_eval profile hprofile u

@[simp] theorem nearOneInf_toInf_iff
    (p : FuzzyQuantifierParams) (x : ℝ) :
    nearOneInf p.toInf x ↔ nearOne p x := by
  rfl

@[simp] theorem nearZeroInf_toInf_iff
    (p : FuzzyQuantifierParams) (x : ℝ) :
    nearZeroInf p.toInf x ↔ nearZero p x := by
  rfl

section CountingReduction

variable {U : Type*} [Fintype U] [MeasurableSpace U]

/-- Exact reduction of the arbitrary-domain near-one mass to the finite witness
fraction when the capacity is counting and the profile is bounded in `[0,1]`. -/
theorem nearOneMassInf_counting_eq_nearOneFractionFin
    (p : FuzzyQuantifierParams)
    (profile : U → ℝ)
    (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    (nearOneMassInf p.toInf (FuzzyCapacity.countingCapacity (U := U))
        (boundedProfileFinToInf profile hprofile) : ℝ) =
      nearOneFractionFin p profile := by
  classical
  unfold nearOneMassInf nearOneCutInf boundedProfileFinToInf
  unfold FuzzyCapacity.countingCapacity FuzzyCapacity.countingValue
  unfold nearOneFractionFin nearOneFraction witnessFraction witnessCount
  by_cases h0 : Fintype.card U = 0
  · simp [h0]
  · simp [h0]

/-- Exact reduction of the arbitrary-domain near-zero mass to the finite witness
fraction when the capacity is counting and the profile is bounded in `[0,1]`. -/
theorem nearZeroMassInf_counting_eq_nearZeroFractionFin
    (p : FuzzyQuantifierParams)
    (profile : U → ℝ)
    (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    (nearZeroMassInf p.toInf (FuzzyCapacity.countingCapacity (U := U))
        (boundedProfileFinToInf profile hprofile) : ℝ) =
      nearZeroFractionFin p profile := by
  classical
  unfold nearZeroMassInf nearZeroCutInf boundedProfileFinToInf
  unfold FuzzyCapacity.countingCapacity FuzzyCapacity.countingValue
  unfold nearZeroFractionFin nearZeroFraction witnessFraction witnessCount
  by_cases h0 : Fintype.card U = 0
  · simp [h0]
  · simp [h0]

/-- Exact reduction of the infinitary existential score to the finite/counting score. -/
theorem fuzzyExistsScoreInf_counting_eq_fuzzyExistsScoreFin
    (p : FuzzyQuantifierParams)
    (profile : U → ℝ)
    (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    (fuzzyExistsScoreInf p.toInf (FuzzyCapacity.countingCapacity (U := U))
        (boundedProfileFinToInf profile hprofile) : ℝ) =
      fuzzyExistsScoreFin p profile := by
  exact nearOneMassInf_counting_eq_nearOneFractionFin p profile hprofile

/-- Exact reduction of interval truth under the counting capacity. -/
theorem fuzzyIntervalHoldsInf_counting_iff_fuzzyIntervalHoldsFin
    (p : FuzzyQuantifierParams)
    (profile : U → ℝ)
    (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    fuzzyIntervalHoldsInf p.toInf (FuzzyCapacity.countingCapacity (U := U))
        (boundedProfileFinToInf profile hprofile) ↔
      fuzzyIntervalHoldsFin p profile := by
  unfold fuzzyIntervalHoldsInf fuzzyIntervalHoldsFin fuzzyIntervalHolds
  rw [nearOneMassInf_counting_eq_nearOneFractionFin p profile hprofile]
  simp [FuzzyQuantifierParams.toInf]

/-- Exact reduction of crisp-leaning universal truth under the counting capacity. -/
theorem fuzzyForAllHoldsInf_counting_iff_fuzzyForAllHoldsFin
    (p : FuzzyQuantifierParams)
    (profile : U → ℝ)
    (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    fuzzyForAllHoldsInf p.toInf (FuzzyCapacity.countingCapacity (U := U))
        (boundedProfileFinToInf profile hprofile) ↔
      fuzzyForAllHoldsFin p profile := by
  unfold fuzzyForAllHoldsInf fuzzyForAllHoldsFin fuzzyForAllHolds
  rw [nearOneMassInf_counting_eq_nearOneFractionFin p profile hprofile]
  simp [FuzzyQuantifierParams.toInf]

/-- Exact reduction of crisp-leaning existential truth under the counting capacity. -/
theorem fuzzyThereExistsHoldsInf_counting_iff_fuzzyThereExistsHoldsFin
    (p : FuzzyQuantifierParams)
    (profile : U → ℝ)
    (hprofile : ∀ u, profile u ∈ (I : Set ℝ)) :
    fuzzyThereExistsHoldsInf p.toInf (FuzzyCapacity.countingCapacity (U := U))
        (boundedProfileFinToInf profile hprofile) ↔
      fuzzyThereExistsHoldsFin p profile := by
  unfold fuzzyThereExistsHoldsInf fuzzyThereExistsHoldsFin fuzzyThereExistsHolds
  rw [nearZeroMassInf_counting_eq_nearZeroFractionFin p profile hprofile]
  simp [FuzzyQuantifierParams.toInf]

end CountingReduction

end Mettapedia.Logic.PLNFirstOrder
