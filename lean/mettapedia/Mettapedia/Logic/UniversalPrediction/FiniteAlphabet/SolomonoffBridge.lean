import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.HutterEnumerationTheoremSemimeasure

/-!
# Solomonoff Bridge (Finite Alphabet): Chapter 2 → Chapter 3

This file is the finite-alphabet analogue of `UniversalPrediction/SolomonoffBridge.lean`.

It provides a theorem-grade “mixture route” universal predictor for `Word α := List α`:

1. Use the Levin/Hutter enumeration theorem (implemented concretely via `Nat.Partrec.Code`) to get a
   countable family of Hutter-lower-semicomputable semimeasures on `Word α`.
2. Form the universal mixture `M₂` using the provably summable `encodeWeight`.
3. Apply the generic dominance→regret lemma in `FiniteAlphabet.FiniteHorizon`:

   `Dominates M₂ μ c  ⟹  Dₙ(μ‖M₂) ≤ log(1/c)`.

This is “real Hutter” in the sense that:
* the enumeration is concrete (no toy axioms), and
* the dominance constant is an explicit code weight `encodeWeight code`.
-/

namespace Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge

open scoped Classical BigOperators ENNReal

open Mettapedia.Computability.Hutter
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open FiniteAlphabet.FiniteHorizon
open HutterEnumerationTheoremSemimeasure

variable {α : Type*} [Fintype α] [Primcodable α]

/-! ## A concrete universal mixture on `Word α` -/

/-- Universal mixture over lower-semicomputable semimeasures on `Word α`. -/
noncomputable abbrev M₂ : Semimeasure α :=
  (HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration (α := α)).xi

/-! ## Dominance / regret (theorem-grade) -/

/-- Dominance→regret bound for `M₂` against any lower-semicomputable prefix measure. -/
theorem relEntropy_le_log_inv_M₂ (μ : PrefixMeasure α)
    (hμ : LowerSemicomputablePrefixMeasure (α := α) μ) (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧ Dominates (M₂ (α := α)) μ c ∧
        relEntropy μ (M₂ (α := α)) n ≤ Real.log (1 / c.toReal) := by
  simpa [M₂] using
    (LSCSemimeasureEnumeration.relEntropy_le_log_inv_of_LSC
      (E := HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration (α := α)) (μ := μ) hμ n)

/-! ## Interpreting the dominance constant as a “code length” -/

theorem log_inv_encodeWeight (c : Nat.Partrec.Code) :
    Real.log (1 / (encodeWeight c).toReal) = (Encodable.encode c + 1) * Real.log 2 := by
  classical
  have hpow :
      (encodeWeight c).toReal = ((2 : ℝ)⁻¹) ^ (Encodable.encode c + 1) := by
    simp [encodeWeight, ENNReal.toReal_pow]
  have hdiv :
      (1 : ℝ) / (encodeWeight c).toReal = (2 : ℝ) ^ (Encodable.encode c + 1) := by
    have h2ne0 : (2 : ℝ) ≠ 0 := by norm_num
    calc
      (1 : ℝ) / (encodeWeight c).toReal
          = (1 : ℝ) / (((2 : ℝ)⁻¹) ^ (Encodable.encode c + 1)) := by simp [hpow]
      _ = (1 : ℝ) / ((2 : ℝ) ^ (Encodable.encode c + 1))⁻¹ := by
            simp [inv_pow]
      _ = (2 : ℝ) ^ (Encodable.encode c + 1) := by
            simp [div_eq_mul_inv]
  calc
    Real.log (1 / (encodeWeight c).toReal)
        = Real.log ((2 : ℝ) ^ (Encodable.encode c + 1)) := by simp [hdiv]
    _ = (Encodable.encode c + 1) * Real.log 2 := by simp [Real.log_pow]

/-- Code-level dominance→regret bound for `M₂`, stated as `(encode code + 1) * log 2`. -/
theorem relEntropy_le_codeLength_log2_M₂ (μ : PrefixMeasure α)
    (hμ : LowerSemicomputablePrefixMeasure (α := α) μ) (n : ℕ) :
    ∃ code : Nat.Partrec.Code,
      Dominates (M₂ (α := α)) μ (encodeWeight code) ∧
        relEntropy μ (M₂ (α := α)) n ≤ (Encodable.encode code + 1) * Real.log 2 := by
  classical
  -- Get a code for `μ` viewed as a semimeasure.
  have hμ_sem : LowerSemicomputableSemimeasure (α := α) μ.toSemimeasure := by
    simpa [LowerSemicomputableSemimeasure, LowerSemicomputablePrefixMeasure,
      PrefixMeasure.toSemimeasure_apply] using hμ
  obtain ⟨code, hcode⟩ :=
    (HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration (α := α)).surj_eval
      μ.toSemimeasure hμ_sem
  have hdom : Dominates (M₂ (α := α)) μ (encodeWeight code) := by
    intro x
    have hdom' :
        encodeWeight code * (HutterEnumerationTheoremSemimeasure.evalLSC (α := α) code) x ≤ (M₂ (α := α)) x := by
      -- `M₂ = xi ...` and dominance is termwise inside the `tsum`.
      simpa [M₂, HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration,
        LSCSemimeasureEnumeration.xi] using
        (LSCSemimeasureEnumeration.xi_dominates_eval
          (E := HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration (α := α)) code x)
    have hcode_x : HutterEnumerationTheoremSemimeasure.evalLSC (α := α) code x = μ x := by
      have := congrArg (fun ξ : Semimeasure α => ξ x) hcode
      simpa [PrefixMeasure.toSemimeasure_apply,
        HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration] using this
    simpa [hcode_x] using hdom'
  have hc0 : encodeWeight code ≠ 0 := by
    unfold encodeWeight
    exact pow_ne_zero _ (by simp)
  have hbound :=
    relEntropy_le_log_inv_of_dominates (μ := μ) (ξ := (M₂ (α := α))) (hdom := hdom) (hc0 := hc0) n
  refine ⟨code, hdom, ?_⟩
  -- Rewrite the RHS using the code-length lemma.
  exact hbound.trans_eq (log_inv_encodeWeight (c := code))

end Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge
