import Mettapedia.Logic.PLNFirstOrder.SugenoIntegral

/-!
# Arbitrary-Domain Fuzzy Quantifier Semantics

General-domain fuzzy quantifier semantics based on capacities of proxy cuts,
with a Sugeno-integral quantitative hook living alongside the Chapter-11 proxy layer.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open scoped unitInterval

variable {U : Type*} [MeasurableSpace U]

/-- The near-one proxy cut of a fuzzy profile. -/
def nearOneCutInf
    (p : FuzzyQuantifierParamsInf) (f : FuzzyProfile U) : Set U :=
  {u | nearOneInf p (f u : ℝ)}

/-- The near-zero proxy cut of a fuzzy profile. -/
def nearZeroCutInf
    (p : FuzzyQuantifierParamsInf) (f : FuzzyProfile U) : Set U :=
  {u | nearZeroInf p (f u : ℝ)}

/-- Capacity of the near-one proxy cut. -/
def nearOneMassInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) : I :=
  ν (nearOneCutInf p f)

/-- Capacity of the near-zero proxy cut. -/
def nearZeroMassInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) : I :=
  ν (nearZeroCutInf p f)

/-- Existential-style score in the arbitrary-domain proxy-cut semantics. -/
def fuzzyExistsScoreInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) : I :=
  nearOneMassInf p ν f

/-- Generic fuzzy interval truth on arbitrary domains. -/
def fuzzyIntervalHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) : Prop :=
  p.LPC ≤ (nearOneMassInf p ν f : ℝ) ∧ (nearOneMassInf p ν f : ℝ) ≤ p.UPC

/-- Crisp-leaning `ForAll` on arbitrary domains. -/
def fuzzyForAllHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) : Prop :=
  p.PCL ≤ (nearOneMassInf p ν f : ℝ)

/-- Crisp-leaning `ThereExists` on arbitrary domains. -/
def fuzzyThereExistsHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) : Prop :=
  p.PCL ≤ 1 - (nearZeroMassInf p ν f : ℝ)

/-- Optional quantitative hook: direct Sugeno aggregation of the profile. -/
noncomputable def sugenoScoreInf
    (ν : FuzzyCapacity U) (f : FuzzyProfile U) : I :=
  FuzzyCapacity.sugenoIntegral ν f

theorem nearOneMassInf_in_unit
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    ((nearOneMassInf p ν f : I) : ℝ) ∈ (I : Set ℝ) :=
  (nearOneMassInf p ν f).2

theorem nearZeroMassInf_in_unit
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    ((nearZeroMassInf p ν f : I) : ℝ) ∈ (I : Set ℝ) :=
  (nearZeroMassInf p ν f).2

theorem nearOneMassInf_eq_of_signatureEq
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (f g : FuzzyProfile U)
    (hSig : ∀ u, nearOneInf p (f u : ℝ) ↔ nearOneInf p (g u : ℝ)) :
    nearOneMassInf p ν f = nearOneMassInf p ν g := by
  unfold nearOneMassInf nearOneCutInf
  congr 1
  ext u
  exact hSig u

theorem nearZeroMassInf_eq_of_signatureEq
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (f g : FuzzyProfile U)
    (hSig : ∀ u, nearZeroInf p (f u : ℝ) ↔ nearZeroInf p (g u : ℝ)) :
    nearZeroMassInf p ν f = nearZeroMassInf p ν g := by
  unfold nearZeroMassInf nearZeroCutInf
  congr 1
  ext u
  exact hSig u

theorem nearOneMassInf_mono_of_pointwise
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (f g : FuzzyProfile U)
    (hfg : ∀ u, f u ≤ g u) :
    nearOneMassInf p ν f ≤ nearOneMassInf p ν g := by
  unfold nearOneMassInf nearOneCutInf
  apply ν.mono
  intro u hu
  exact ⟨le_trans hu.1 (hfg u), unitInterval.le_one (g u)⟩

theorem fuzzyExistsScoreInf_mono_of_pointwise
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (f g : FuzzyProfile U)
    (hfg : ∀ u, f u ≤ g u) :
    fuzzyExistsScoreInf p ν f ≤ fuzzyExistsScoreInf p ν g := by
  exact nearOneMassInf_mono_of_pointwise p ν f g hfg

theorem fuzzyForAllHoldsInf_mono_of_pointwise
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (f g : FuzzyProfile U)
    (hfg : ∀ u, f u ≤ g u)
    (hForAll : fuzzyForAllHoldsInf p ν f) :
    fuzzyForAllHoldsInf p ν g := by
  unfold fuzzyForAllHoldsInf at *
  exact le_trans hForAll (nearOneMassInf_mono_of_pointwise p ν f g hfg)

theorem fuzzyIntervalHoldsInf_iff_of_signatureEq
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (f g : FuzzyProfile U)
    (hSig : ∀ u, nearOneInf p (f u : ℝ) ↔ nearOneInf p (g u : ℝ)) :
    fuzzyIntervalHoldsInf p ν f ↔ fuzzyIntervalHoldsInf p ν g := by
  have hEq := nearOneMassInf_eq_of_signatureEq p ν f g hSig
  unfold fuzzyIntervalHoldsInf
  simp [hEq]

theorem fuzzyForAllHoldsInf_iff_of_signatureEq
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (f g : FuzzyProfile U)
    (hSig : ∀ u, nearOneInf p (f u : ℝ) ↔ nearOneInf p (g u : ℝ)) :
    fuzzyForAllHoldsInf p ν f ↔ fuzzyForAllHoldsInf p ν g := by
  have hEq := nearOneMassInf_eq_of_signatureEq p ν f g hSig
  unfold fuzzyForAllHoldsInf
  simp [hEq]

theorem nearZeroMassInf_eq_nearOneMassInf_compl
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    nearZeroMassInf p ν f = nearOneMassInf p ν (FuzzyProfile.compl f) := by
  unfold nearZeroMassInf nearOneMassInf nearZeroCutInf nearOneCutInf
  congr 1
  ext u
  simpa [FuzzyProfile.compl_apply] using nearZeroInf_iff_nearOneInf_one_sub p (f u : ℝ)

theorem fuzzyThereExistsHoldsInf_iff_nearOneComplement
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    fuzzyThereExistsHoldsInf p ν f ↔
      p.PCL ≤ 1 - (nearOneMassInf p ν (FuzzyProfile.compl f) : ℝ) := by
  unfold fuzzyThereExistsHoldsInf
  rw [nearZeroMassInf_eq_nearOneMassInf_compl]

theorem sugenoScoreInf_mono
    (ν : FuzzyCapacity U) (f g : FuzzyProfile U)
    (hfg : ∀ u, f u ≤ g u) :
    sugenoScoreInf ν f ≤ sugenoScoreInf ν g :=
  FuzzyCapacity.sugenoIntegral_mono ν f g hfg

end Mettapedia.Logic.PLNFirstOrder
