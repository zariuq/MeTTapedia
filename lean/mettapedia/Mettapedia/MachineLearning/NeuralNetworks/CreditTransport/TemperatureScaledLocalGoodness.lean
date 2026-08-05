import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic

/-!
# Temperature-scaled local-goodness geometry

Chen, *Synthetic Benchmarks Overstate Forward-Forward Scaling: Real-Data
Limits of Layer-Local Training* (2026, arXiv:2606.06539), introduces a
bounded learnable temperature for each detached Forward-Forward goodness
loss.  Appendix A derives the local cross-entropy credit

`T⁻¹ R (p - e_y)`

and the bound `‖p - e_y‖₂ ≤ √2`.

This file formalizes the finite geometry behind that mechanism.

* A sigmoid-parameterized temperature lies strictly between its declared
  positive endpoints and starts at their midpoint.
* Scaling goodness by a fixed nonzero temperature is exactly invertible.
* Every finite probability vector has squared one-hot error at most two.
* A declared squared operator bound for the fixed projection transports that
  estimate into an explicit temperature-scaled local-credit bound.

The implementation boundary is equally important.  A global classifier term
that shares layer parameters makes the first-layer gradient depend on later
features, even when the goodness path itself is detached.  A concrete scalar
fixture records this hybrid failure of strict inter-layer locality.  Zero
temperature and signed, non-probability score vectors are separate negative
fixtures.

These results do not establish Forward-Forward task accuracy, memory or
throughput superiority, mutual-information preservation, or convergence.

Source artifact SHA-256:
`8b3617e3cbaa53634532e5bf151025cfb37cff3336a9d24d65d54ca751bb853a`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace TemperatureScaledLocalGoodness

open scoped BigOperators

noncomputable section

/-! ## Bounded learnable temperature -/

/-- Sigmoid parameterization of a temperature between fixed endpoints. -/
def boundedTemperature
    (minimum maximum alpha : ℝ) : ℝ :=
  minimum + (maximum - minimum) * Real.sigmoid alpha

/-- A finite sigmoid parameter never reaches the lower endpoint. -/
theorem minimum_lt_boundedTemperature
    (minimum maximum alpha : ℝ)
    (hbounds : minimum < maximum) :
    minimum < boundedTemperature minimum maximum alpha := by
  have hsigmoid := Real.sigmoid_pos alpha
  simp only [boundedTemperature]
  nlinarith

/-- A finite sigmoid parameter never reaches the upper endpoint. -/
theorem boundedTemperature_lt_maximum
    (minimum maximum alpha : ℝ)
    (hbounds : minimum < maximum) :
    boundedTemperature minimum maximum alpha < maximum := by
  have hsigmoid := Real.sigmoid_lt_one alpha
  simp only [boundedTemperature]
  nlinarith

/-- Closed endpoint bounds follow, but the strict theorem above records the
stronger finite-parameter fact. -/
theorem boundedTemperature_mem_Icc
    (minimum maximum alpha : ℝ)
    (hbounds : minimum < maximum) :
    boundedTemperature minimum maximum alpha ∈
      Set.Icc minimum maximum :=
  ⟨(minimum_lt_boundedTemperature minimum maximum alpha hbounds).le,
    (boundedTemperature_lt_maximum minimum maximum alpha hbounds).le⟩

/-- Initializing the unconstrained parameter to zero gives the arithmetic
midpoint of the temperature interval. -/
theorem boundedTemperature_zero_eq_midpoint
    (minimum maximum : ℝ) :
    boundedTemperature minimum maximum 0 =
      (minimum + maximum) / 2 := by
  rw [boundedTemperature, Real.sigmoid_zero]
  ring

/-- A positive lower endpoint makes every finite learned temperature
positive. -/
theorem boundedTemperature_pos
    (minimum maximum alpha : ℝ)
    (hminimum : 0 < minimum)
    (hbounds : minimum < maximum) :
    0 < boundedTemperature minimum maximum alpha :=
  hminimum.trans
    (minimum_lt_boundedTemperature minimum maximum alpha hbounds)

/-! ## Fixed temperature scaling preserves the representation exactly -/

variable {Index : Type*}

/-- Divide every goodness coordinate by the fixed temperature. -/
def scaleGoodness (temperature : ℝ) (goodness : Index → ℝ) :
    Index → ℝ :=
  fun index => goodness index / temperature

/-- Inverse rescaling for a fixed temperature. -/
def unscaleGoodness (temperature : ℝ) (scaled : Index → ℝ) :
    Index → ℝ :=
  fun index => temperature * scaled index

theorem unscaleGoodness_scaleGoodness
    (temperature : ℝ) (goodness : Index → ℝ)
    (htemperature : temperature ≠ 0) :
    unscaleGoodness temperature
        (scaleGoodness temperature goodness) =
      goodness := by
  funext index
  simp only [unscaleGoodness, scaleGoodness]
  field_simp

theorem scaleGoodness_unscaleGoodness
    (temperature : ℝ) (scaled : Index → ℝ)
    (htemperature : temperature ≠ 0) :
    scaleGoodness temperature
        (unscaleGoodness temperature scaled) =
      scaled := by
  funext index
  simp only [scaleGoodness, unscaleGoodness]
  field_simp

/-! ## Finite probability-to-one-hot geometry -/

variable {Class Feature : Type*}
  [Fintype Class] [DecidableEq Class]
  [Fintype Feature]

/-- Squared Euclidean norm of a finite real vector. -/
def squaredNorm {Coordinate : Type*} [Fintype Coordinate]
    (vector : Coordinate → ℝ) : ℝ :=
  ∑ coordinate, vector coordinate ^ 2

/-- One-hot vector for a class label. -/
def oneHot (label : Class) : Class → ℝ :=
  fun classIndex => if classIndex = label then 1 else 0

/-- Probability error relative to a one-hot label. -/
def probabilityError
    (probability : Class → ℝ) (label : Class) : Class → ℝ :=
  probability - oneHot label

/-- Finite probability simplex assumptions. -/
def IsProbabilityVector (probability : Class → ℝ) : Prop :=
  (∀ classIndex, 0 ≤ probability classIndex) ∧
    ∑ classIndex, probability classIndex = 1

omit [DecidableEq Class] in
theorem probability_coordinate_le_one
    (probability : Class → ℝ)
    (hprobability : IsProbabilityVector probability)
    (classIndex : Class) :
    probability classIndex ≤ 1 := by
  have hsingle :
      probability classIndex ≤ ∑ index, probability index := by
    exact
      Finset.single_le_sum
        (fun index _ => hprobability.1 index)
        (Finset.mem_univ classIndex)
  simpa [hprobability.2] using hsingle

/-- The squared distance from a probability vector to any one-hot label is
at most two. -/
theorem squaredNorm_probabilityError_le_two
    (probability : Class → ℝ)
    (label : Class)
    (hprobability : IsProbabilityVector probability) :
    squaredNorm (probabilityError probability label) ≤ 2 := by
  classical
  let errorTerm : Class → ℝ :=
    fun index => probabilityError probability label index ^ 2
  have herase :
      ∑ index ∈ Finset.univ.erase label, errorTerm index ≤
        ∑ index ∈ Finset.univ.erase label, probability index := by
    apply Finset.sum_le_sum
    intro index hindex
    have hne : index ≠ label := by
      simpa using hindex
    have hnonneg := hprobability.1 index
    have hle := probability_coordinate_le_one probability hprobability index
    simp only [errorTerm, probabilityError, oneHot, Pi.sub_apply, hne,
      ↓reduceIte, sub_zero]
    nlinarith
  have hsumErase :
      ∑ index ∈ Finset.univ.erase label, probability index =
        1 - probability label := by
    have hsum :=
      Finset.sum_erase_add Finset.univ probability
        (Finset.mem_univ label)
    rw [hprobability.2] at hsum
    linarith
  have hlabelNonneg := hprobability.1 label
  have hlabelLe :=
    probability_coordinate_le_one probability hprobability label
  change ∑ index, errorTerm index ≤ 2
  rw [← Finset.sum_erase_add Finset.univ errorTerm
    (Finset.mem_univ label)]
  have hlabel :
      errorTerm label = (probability label - 1) ^ 2 := by
    simp [errorTerm, probabilityError, oneHot]
  rw [hlabel]
  calc
    (∑ index ∈ Finset.univ.erase label, errorTerm index) +
          (probability label - 1) ^ 2
        ≤ (∑ index ∈ Finset.univ.erase label, probability index) +
            (probability label - 1) ^ 2 :=
      add_le_add herase le_rfl
    _ = (1 - probability label) +
          (probability label - 1) ^ 2 := by rw [hsumErase]
    _ ≤ 2 := by nlinarith

/-! ## Projection and temperature transport -/

/-- A squared operator bound for the fixed local random projection. -/
def HasSquaredOperatorBound
    (project : (Class → ℝ) → (Feature → ℝ))
    (bound : ℝ) : Prop :=
  ∀ vector,
    squaredNorm (project vector) ≤
      bound ^ 2 * squaredNorm vector

/-- The temperature-scaled local credit before transport through the layer
Jacobian. -/
def temperatureScaledCredit
    (temperature : ℝ)
    (project : (Class → ℝ) → (Feature → ℝ))
    (probability : Class → ℝ)
    (label : Class) :
    Feature → ℝ :=
  scaleGoodness temperature
    (project (probabilityError probability label))

/-- Squared norm of coordinatewise temperature scaling. -/
theorem squaredNorm_scaleGoodness
    (temperature : ℝ) (vector : Feature → ℝ) :
    squaredNorm (scaleGoodness temperature vector) =
      squaredNorm vector / temperature ^ 2 := by
  simp only [squaredNorm, scaleGoodness, div_pow]
  rw [Finset.sum_div]

/-- Explicit finite version of the source local-credit bound:
`‖T⁻¹ R(p-e_y)‖² ≤ 2 ‖R‖² / T²`. -/
theorem temperatureScaledCredit_squaredNorm_le
    (temperature bound : ℝ)
    (project : (Class → ℝ) → (Feature → ℝ))
    (probability : Class → ℝ)
    (label : Class)
    (htemperature : 0 < temperature)
    (hproject : HasSquaredOperatorBound project bound)
    (hprobability : IsProbabilityVector probability) :
    squaredNorm
        (temperatureScaledCredit temperature project probability label) ≤
      2 * bound ^ 2 / temperature ^ 2 := by
  rw [temperatureScaledCredit, squaredNorm_scaleGoodness]
  have hprojectBound :=
    hproject (probabilityError probability label)
  have herror :=
    squaredNorm_probabilityError_le_two probability label hprobability
  have hboundSq : 0 ≤ bound ^ 2 := sq_nonneg bound
  have hmul :
      bound ^ 2 * squaredNorm (probabilityError probability label) ≤
        bound ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left herror hboundSq
  have htrans :
      squaredNorm (project (probabilityError probability label)) ≤
        bound ^ 2 * 2 :=
    hprojectBound.trans hmul
  exact
    (div_le_div_iff_of_pos_right (sq_pos_of_pos htemperature)).2
      (by nlinarith)

/-! ## Negative boundaries -/

/-- At zero temperature Lean's totalized division maps every coordinate to
zero, so scaling is not invertible.  A strictly positive lower endpoint is
essential. -/
theorem zeroTemperature_collapses_nonzeroGoodness :
    scaleGoodness (Index := Bool) 0
        (fun index => if index then (1 : ℝ) else 0) =
      fun _ => 0 := by
  funext index
  simp [scaleGoodness]

/-- Unit-sum signed scores need not satisfy the probability error bound:
nonnegativity is load-bearing. -/
theorem signedUnitSum_scores_break_error_bound :
    let scores : Bool → ℝ :=
      fun index => if index then 3 else -2
    (∑ index, scores index = 1) ∧
      2 < squaredNorm (probabilityError scores true) := by
  norm_num [squaredNorm, probabilityError, oneHot]

/-- A scalar hybrid loss combines a local first-layer term with a global term
sharing both layers. -/
def hybridFirstGradient
    (first second : ℝ) : ℝ :=
  2 * first + 2 * (first + second)

/-- The first-layer gradient of the hybrid objective changes when only the
later feature changes.  Detaching the local goodness path therefore does not
make a shared global-classifier objective inter-layer local. -/
theorem hybridClassifier_breaks_firstLayer_locality :
    hybridFirstGradient 1 0 ≠ hybridFirstGradient 1 1 := by
  norm_num [hybridFirstGradient]

end

end TemperatureScaledLocalGoodness

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
