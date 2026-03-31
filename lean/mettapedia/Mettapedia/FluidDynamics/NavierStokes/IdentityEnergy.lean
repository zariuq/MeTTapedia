import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section FiniteGamma

variable {ι X : Type*} [Fintype ι]

/-- Finite carré-du-champ style energy for a family of directional derivatives. -/
def gamma (D : ι → ℝ) : ℝ :=
  ∑ i, (D i) ^ 2

theorem gamma_nonneg (D : ι → ℝ) : 0 ≤ gamma D := by
  unfold gamma
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem gamma_smul (c : ℝ) (D : ι → ℝ) :
    gamma (fun i => c * D i) = c ^ 2 * gamma D := by
  unfold gamma
  calc
    ∑ i, (c * D i) ^ 2
        = ∑ i, c ^ 2 * (D i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = c ^ 2 * ∑ i, (D i) ^ 2 := by rw [Finset.mul_sum]

/-- Pointwise log-gradient comparison:
if `F ≥ m > 0`, then replacing `DᵢF` by `DᵢF / F` costs at most a factor `1 / m²`. -/
theorem gamma_div_le (D : ι → ℝ) {F m : ℝ} (hm : 0 < m) (hF : m ≤ F) :
    gamma (fun i => D i / F) ≤ gamma D / m ^ 2 := by
  have hFpos : 0 < F := lt_of_lt_of_le hm hF
  have hm2pos : 0 < m ^ 2 := sq_pos_of_pos hm
  have hFm : m ^ 2 ≤ F ^ 2 := by nlinarith
  unfold gamma
  calc
    ∑ i, (D i / F) ^ 2 ≤ ∑ i, (D i) ^ 2 / m ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hDi : 0 ≤ (D i) ^ 2 := sq_nonneg (D i)
      have hdiv := div_le_div_of_nonneg_left hDi hm2pos hFm
      have hrewrite : (D i / F) ^ 2 = (D i) ^ 2 / F ^ 2 := by
        field_simp [hFpos.ne']
      simpa [hrewrite] using hdiv
    _ = (∑ i, (D i) ^ 2) / m ^ 2 := by
      calc
        ∑ i, D i ^ 2 / m ^ 2 = ∑ i, D i ^ 2 * (m ^ 2)⁻¹ := by simp [div_eq_mul_inv]
        _ = (∑ i, D i ^ 2) * (m ^ 2)⁻¹ := by rw [Finset.sum_mul]
        _ = (∑ i, D i ^ 2) / m ^ 2 := by simp [div_eq_mul_inv]

/-- The `W = -2ν log Φ` energy factor used in the SG-Cole-Hopf route. -/
theorem gamma_negTwoNuLog_le (D : ι → ℝ) {Φ m ν : ℝ}
    (hm : 0 < m) (hΦ : m ≤ Φ) :
    gamma (fun i => (-2 * ν) * (D i / Φ)) ≤ (4 * ν ^ 2 / m ^ 2) * gamma D := by
  have hbase := gamma_div_le (D := D) hm hΦ
  calc
    gamma (fun i => (-2 * ν) * (D i / Φ))
        = (-2 * ν) ^ 2 * gamma (fun i => D i / Φ) := gamma_smul (-2 * ν) _
    _ ≤ (-2 * ν) ^ 2 * (gamma D / m ^ 2) := by
          exact mul_le_mul_of_nonneg_left hbase (sq_nonneg (-2 * ν))
    _ = (4 * ν ^ 2 / m ^ 2) * gamma D := by ring

/-- Finite linear reconstruction from coefficient data and a frame. -/
def frameEval (coeff : ι → ℝ) (frame : ι → X → ℝ) (x : X) : ℝ :=
  ∑ i, coeff i * frame i x

/-- Cauchy-Schwarz in the finite frame form needed for vorticity push-down bounds. -/
theorem frameEval_sq_le (coeff : ι → ℝ) (frame : ι → X → ℝ) (x : X) :
    frameEval coeff frame x ^ 2 ≤ gamma coeff * gamma (fun i => frame i x) := by
  unfold frameEval gamma
  simpa [pow_two] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ coeff fun i => frame i x)

/-- Uniform pointwise frame control turns coefficient energy into a uniform field bound. -/
theorem abs_frameEval_le (coeff : ι → ℝ) (frame : ι → X → ℝ) {x : X} {A C : ℝ}
    (hcoeff : gamma coeff ≤ A)
    (hframe : gamma (fun i => frame i x) ≤ C) :
    |frameEval coeff frame x| ≤ Real.sqrt A * Real.sqrt C := by
  have hgammaCoeff : 0 ≤ gamma coeff := gamma_nonneg coeff
  have hgammaFrame : 0 ≤ gamma (fun i => frame i x) := gamma_nonneg _
  have hA : 0 ≤ A := le_trans hgammaCoeff hcoeff
  have hC : 0 ≤ C := le_trans hgammaFrame hframe
  have hsquare :
      frameEval coeff frame x ^ 2 ≤ A * C := by
    calc
      frameEval coeff frame x ^ 2
          ≤ gamma coeff * gamma (fun i => frame i x) := frameEval_sq_le coeff frame x
      _ ≤ A * C := by
            gcongr
  have hsqrt := Real.sqrt_le_sqrt hsquare
  have habs :
      |frameEval coeff frame x| = Real.sqrt (frameEval coeff frame x ^ 2) := by
    simpa [pow_two] using (Real.sqrt_sq_eq_abs (frameEval coeff frame x)).symm
  rw [← habs] at hsqrt
  simpa [Real.sqrt_mul hA] using hsqrt

/-- The manuscript's vorticity estimate is exactly the preceding frame bound with `frame = curl E`. -/
theorem abs_vorticity_le (coeff : ι → ℝ) (curlFrame : ι → X → ℝ) {x : X} {A CcurlE : ℝ}
    (hcoeff : gamma coeff ≤ A)
    (hcurl : gamma (fun i => curlFrame i x) ≤ CcurlE) :
    |frameEval coeff curlFrame x| ≤ Real.sqrt A * Real.sqrt CcurlE :=
  abs_frameEval_le coeff curlFrame hcoeff hcurl

end FiniteGamma

end NavierStokes
end FluidDynamics
end Mettapedia
