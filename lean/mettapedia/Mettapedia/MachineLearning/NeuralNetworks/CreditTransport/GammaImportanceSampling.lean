import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.WeightedStrongConvexity

/-!
# The gamma family of importance-sampled coordinate descent

Bubeck, *Convex Optimization: Algorithms and Complexity*,
arXiv:1405.4980, Section 6.4.1 and Theorem 6.8, samples coordinate `i`
with probability proportional to `βᵢ^γ`.  Strong convexity is measured in the
primal coordinate geometry with weights `βᵢ^(1 - γ)`.

This module constructs that family using real powers and binds it to the
general weighted strong-convexity rate.  Positivity of every directional
smoothness is explicit: it normalizes the sampling law, makes the induced
primal/dual ratio well-defined, and cannot be inferred from a coordinate
label.

The source assumes `γ ≥ 0`.  The finite algebra below is valid for every real
`γ` when all `βᵢ` are positive.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace GammaImportanceSampling

open ImportanceSampledCoordinateDescent WeightedStrongConvexity

universe u

variable {Coordinate : Type u}

/-- Unnormalized source sampling weights `βᵢ^γ`. -/
noncomputable def gammaSamplingWeight
    (smoothness : Coordinate → ℝ) (gamma : ℝ) : Coordinate → ℝ :=
  fun coordinate => smoothness coordinate ^ gamma

/-- Source primal norm weights `βᵢ^(1 - γ)`. -/
noncomputable def gammaPrimalWeight
    (smoothness : Coordinate → ℝ) (gamma : ℝ) : Coordinate → ℝ :=
  fun coordinate => smoothness coordinate ^ (1 - gamma)

/-- Positive directional smoothness makes every real-power sampling weight
strictly positive. -/
theorem gammaSamplingWeight_pos
    (smoothness : Coordinate → ℝ) (gamma : ℝ)
    (positiveSmoothness :
      ∀ coordinate, 0 < smoothness coordinate) :
    ∀ coordinate, 0 < gammaSamplingWeight smoothness gamma coordinate := by
  intro coordinate
  exact Real.rpow_pos_of_pos (positiveSmoothness coordinate) gamma

/-- The general sampler's primal ratio `βᵢ / pᵢ` is exactly the source
weight `βᵢ^(1 - γ)`. -/
theorem smoothness_div_gammaSamplingWeight
    (smoothness : Coordinate → ℝ) (gamma : ℝ)
    (positiveSmoothness :
      ∀ coordinate, 0 < smoothness coordinate) :
    (fun coordinate =>
      smoothness coordinate /
        gammaSamplingWeight smoothness gamma coordinate) =
      gammaPrimalWeight smoothness gamma := by
  funext coordinate
  rw [gammaSamplingWeight, gammaPrimalWeight,
    Real.rpow_sub (positiveSmoothness coordinate), Real.rpow_one]

/-- `γ = 0` recovers uniform unnormalized sampling weights. -/
theorem gammaSamplingWeight_zero
    (smoothness : Coordinate → ℝ) :
    gammaSamplingWeight smoothness 0 = fun _coordinate => 1 := by
  funext coordinate
  simp [gammaSamplingWeight]

/-- `γ = 1` recovers sampling in direct proportion to directional
smoothness. -/
theorem gammaSamplingWeight_one
    (smoothness : Coordinate → ℝ) :
    gammaSamplingWeight smoothness 1 = smoothness := by
  funext coordinate
  simp [gammaSamplingWeight]

/-- At `γ = 0`, the primal geometry retains the directional smoothness. -/
theorem gammaPrimalWeight_zero
    (smoothness : Coordinate → ℝ) :
    gammaPrimalWeight smoothness 0 = smoothness := by
  funext coordinate
  simp [gammaPrimalWeight]

/-- At `γ = 1`, the primal geometry becomes unweighted. -/
theorem gammaPrimalWeight_one
    (smoothness : Coordinate → ℝ) :
    gammaPrimalWeight smoothness 1 = fun _coordinate => 1 := by
  funext coordinate
  simp [gammaPrimalWeight]

section Finite

variable [Fintype Coordinate] [Nonempty Coordinate]

/-- Full finite form of Bubeck Theorem 6.8 for the source's `γ` family.

Directional smoothness supplies `coordinateDecrease`; weighted strong
convexity supplies the first-order model.  The theorem constructs the sampling
weights, derives gradient dominance, and proves the recursively averaged
geometric rate. -/
theorem gammaWeightedStronglyConvex_meanGap_le
    (smoothness : Coordinate → ℝ)
    (gamma : ℝ)
    (objective : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (step : Coordinate → (Coordinate → ℝ) → Coordinate → ℝ)
    (reference : Coordinate → ℝ)
    (modulus : ℝ)
    (positiveSmoothness :
      ∀ coordinate, 0 < smoothness coordinate)
    (positiveModulus : 0 < modulus)
    (modulus_le_total :
      modulus ≤ totalWeight
        (gammaSamplingWeight smoothness gamma))
    (strong :
      IsWeightedStronglyConvexAtGradient
        (gammaPrimalWeight smoothness gamma)
        objective gradient modulus)
    (coordinateDecrease :
      ∀ state coordinate,
        objective (step coordinate state) - objective reference ≤
          objective state - objective reference -
            gradient state coordinate ^ 2 /
              (2 * smoothness coordinate))
    (rounds : ℕ) (state : Coordinate → ℝ) :
    weightedMeanGapAfter
        (gammaSamplingWeight smoothness gamma) step
        (fun point => objective point - objective reference)
        rounds state ≤
      (1 - modulus /
          totalWeight (gammaSamplingWeight smoothness gamma)) ^ rounds *
        (objective state - objective reference) := by
  apply weightedStronglyConvex_meanGap_le
    (gammaSamplingWeight smoothness gamma) smoothness
    objective gradient step reference modulus
    (gammaSamplingWeight_pos
      smoothness gamma positiveSmoothness)
    positiveSmoothness positiveModulus modulus_le_total
  · rw [smoothness_div_gammaSamplingWeight
      smoothness gamma positiveSmoothness]
    exact strong
  · exact coordinateDecrease

/-! ## Exact anisotropic source specialization -/

theorem anisotropic_gammaOne_totalWeight :
    totalWeight
      (gammaSamplingWeight anisotropicSmoothness 1) = 4 := by
  rw [gammaSamplingWeight_one, anisotropic_totalWeight]

/-- The exact anisotropic fixture now passes through the source's constructed
`γ = 1` sampling family. -/
theorem anisotropic_gammaOne_meanGap_le
    (rounds : ℕ) (state : Bool → ℝ) :
    weightedMeanGapAfter
        (gammaSamplingWeight anisotropicSmoothness 1)
        zeroSelectedCoordinate
        (fun point =>
          anisotropicGap point - anisotropicGap zeroBoolState)
        rounds state ≤
      (3 / 4 : ℝ) ^ rounds *
        (anisotropicGap state - anisotropicGap zeroBoolState) := by
  have strong :
      IsWeightedStronglyConvexAtGradient
        (gammaPrimalWeight anisotropicSmoothness 1)
        anisotropicGap anisotropicGradient 1 := by
    rw [gammaPrimalWeight_one]
    exact anisotropic_weightedStrongConvexity
  have theoremInstance :=
    gammaWeightedStronglyConvex_meanGap_le
      anisotropicSmoothness 1 anisotropicGap anisotropicGradient
      zeroSelectedCoordinate zeroBoolState 1
      (by
        intro coordinate
        cases coordinate <;>
          norm_num [anisotropicSmoothness])
      (by norm_num)
      (by
        rw [anisotropic_gammaOne_totalWeight]
        norm_num)
      strong
      (by
        intro point coordinate
        rw [anisotropic_coordinateDecrease_exact]
        norm_num [anisotropicGap, zeroBoolState])
      rounds state
  rw [anisotropic_gammaOne_totalWeight] at theoremInstance
  norm_num at theoremInstance ⊢
  exact theoremInstance

end Finite

/-! ## Negative boundary -/

def zeroSmoothness (_coordinate : Unit) : ℝ := 0

/-- A zero directional smoothness cannot enter the positive real-power
sampling theorem, even at the benign `γ = 1` endpoint. -/
theorem zeroSmoothness_gammaOne_not_positive :
    ¬ ∀ coordinate,
      0 < gammaSamplingWeight zeroSmoothness 1 coordinate := by
  intro claimed
  have contradiction := claimed ()
  norm_num [gammaSamplingWeight, zeroSmoothness] at contradiction

#print axioms gammaSamplingWeight_pos
#print axioms smoothness_div_gammaSamplingWeight
#print axioms gammaSamplingWeight_zero
#print axioms gammaSamplingWeight_one
#print axioms gammaPrimalWeight_zero
#print axioms gammaPrimalWeight_one
#print axioms gammaWeightedStronglyConvex_meanGap_le
#print axioms anisotropic_gammaOne_meanGap_le
#print axioms zeroSmoothness_gammaOne_not_positive

end GammaImportanceSampling

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
