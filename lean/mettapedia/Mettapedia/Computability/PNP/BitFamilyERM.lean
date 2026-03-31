import Mettapedia.Computability.PNP.FiniteERM
import Mettapedia.Computability.PNP.ExactSwitchedFamily

/-!
# P vs NP grassroots: ERM on bit-encoded local families

This file turns one fixed bit-encoded classifier family into a manuscript-shaped
ERM object:

* one chosen code per finite labeled sample,
* the corresponding chosen predictor,
* and an indexed predictor family obtained by choosing one code per index.

The point is simple.  Once a switched wrapper is honestly specified as "ERM over
this one local hypothesis class", the code witness is no longer a separate
burden: it is exactly the ERM-selected code.
-/

namespace Mettapedia.Computability.PNP

universe u v

namespace BitEncodedClassifierFamily

section ERM

variable {Input : Type u} {Index : Type v} {s : ℕ}

/-- The ERM-selected code in one fixed bit family. -/
noncomputable def empiricalRiskCode
    (F : BitEncodedClassifierFamily Input s) (sample : Sample Input Bool) : BitCode s :=
  letI : Nonempty F.toEncodedFamily.Code := by
    change Nonempty (BitCode s)
    exact ⟨fun _ => false⟩
  F.toEncodedFamily.empiricalRiskMinimizer sample

/-- The predictor decoded from the ERM-selected code. -/
noncomputable def empiricalRiskPredictor
    (F : BitEncodedClassifierFamily Input s) (sample : Sample Input Bool) : Input → Bool :=
  F.decode (F.empiricalRiskCode sample)

@[simp] theorem empiricalRiskPredictor_eq_decode_empiricalRiskCode
    (F : BitEncodedClassifierFamily Input s) (sample : Sample Input Bool) :
    F.empiricalRiskPredictor sample = F.decode (F.empiricalRiskCode sample) := rfl

theorem empiricalRiskPredictor_mem_realized
    (F : BitEncodedClassifierFamily Input s) (sample : Sample Input Bool) :
    F.empiricalRiskPredictor sample ∈ EncodedFamily.realized F.toEncodedFamily := by
  letI : Nonempty F.toEncodedFamily.Code := by
    change Nonempty (BitCode s)
    exact ⟨fun _ => false⟩
  simpa [empiricalRiskCode, empiricalRiskPredictor] using
    F.toEncodedFamily.empiricalRiskPredictor_mem_realized sample

theorem empiricalRiskPredictor_fitsSample_of_exists_code_fits
    (F : BitEncodedClassifierFamily Input s)
    (sample : Sample Input Bool)
    (hfit : ∃ c : BitCode s, FitsSample sample (F.decode c)) :
    FitsSample sample (F.empiricalRiskPredictor sample) := by
  letI : Nonempty F.toEncodedFamily.Code := by
    change Nonempty (BitCode s)
    exact ⟨fun _ => false⟩
  simpa [empiricalRiskCode, empiricalRiskPredictor] using
    F.toEncodedFamily.empiricalRiskPredictor_fitsSample_of_exists_code_fits sample hfit

/-- One fixed code per index yields one indexed predictor family. -/
def indexedCodeFamily
    (F : BitEncodedClassifierFamily Input s)
    (codes : Index → BitCode s) :
    IndexedPredictorFamily Index Input where
  predict i := F.decode (codes i)

/-- One ERM-selected code per index yields one indexed predictor family. -/
noncomputable def indexedEmpiricalRiskFamily
    (F : BitEncodedClassifierFamily Input s)
    (samples : Index → Sample Input Bool) :
    IndexedPredictorFamily Index Input where
  predict i := F.empiricalRiskPredictor (samples i)

@[simp] theorem indexedEmpiricalRiskFamily_eq_indexedCodeFamily
    (F : BitEncodedClassifierFamily Input s)
    (samples : Index → Sample Input Bool) :
    F.indexedEmpiricalRiskFamily samples =
      F.indexedCodeFamily (fun i => F.empiricalRiskCode (samples i)) := by
  rfl

theorem realizedByBitFamily_indexedEmpiricalRiskFamily
    (F : BitEncodedClassifierFamily Input s)
    (samples : Index → Sample Input Bool) :
    IndexedPredictorFamily.RealizedByBitFamily (F.indexedEmpiricalRiskFamily samples) F := by
  intro i
  refine ⟨F.empiricalRiskCode (samples i), ?_⟩
  funext x
  rfl

theorem hasBitBudget_indexedEmpiricalRiskFamily
    (F : BitEncodedClassifierFamily Input s)
    (samples : Index → Sample Input Bool) :
    IndexedPredictorFamily.HasBitBudget (F.indexedEmpiricalRiskFamily samples) s := by
  refine ⟨F, ?_⟩
  exact F.realizedByBitFamily_indexedEmpiricalRiskFamily samples

end ERM

end BitEncodedClassifierFamily

section ExactVisibleERM

open scoped ENNReal

variable {Z : Type*} {Index : Type*} {k s : ℕ}

theorem exactVisibleCompressionTarget_of_indexedEmpiricalRiskFamily
    (F : BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) s)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index)
      (F.indexedEmpiricalRiskFamily samples) s := by
  exact F.hasBitBudget_indexedEmpiricalRiskFamily samples

theorem exactVisibleRecoveryLowerBound_of_indexedEmpiricalRiskFamily
    [Fintype Z]
    (F : BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) s)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (i : Index) (m : ℕ)
    {q : ℝ≥0∞}
    (hq :
      ∀ c : F.toEncodedFamily.BadCodes ((F.indexedEmpiricalRiskFamily samples).predict i),
        agreementMass μ ((F.indexedEmpiricalRiskFamily samples).predict i) (F.decode c.1) ≤ q) :
    1 - (2 ^ s : ℝ≥0∞) * q ^ m ≤
      F.bitExactRecoverySampleMass μ ((F.indexedEmpiricalRiskFamily samples).predict i) m := by
  refine exactVisible_bitFamily_exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le_of_fintype
    (Z := Z) (k := k) (s := s) (F := F) (μ := μ)
    (target := (F.indexedEmpiricalRiskFamily samples).predict i) (m := m) ?_ hq
  refine ⟨F.empiricalRiskCode (samples i), ?_⟩
  funext x
  rfl

end ExactVisibleERM

end Mettapedia.Computability.PNP
