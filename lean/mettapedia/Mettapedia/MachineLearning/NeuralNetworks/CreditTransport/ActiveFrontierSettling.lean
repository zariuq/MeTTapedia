import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectionalTaskDescent
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SafeguardedCompositeBlock

/-!
# Active-frontier settling

Sparse settling may update only a selected coordinate frontier.  This module
separates the retained coordinates from the discarded tail by an exact
Euclidean split.  Captured squared mass yields a tail-squared budget, while the
tail norm is exactly the error between the full direction and its frontier
restriction.  That error feeds the existing finite task-descent theorem.

Selection itself remains an external obligation.  A negative fixture shows
that a frontier which misses the active coordinate can stall completely.
Changing a frontier or using a higher-order proposal still requires the
endpoint safeguard supplied by `SafeguardedCompositeBlock`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ActiveFrontierSettling

open scoped InnerProductSpace
open DirectionalTaskDescent

noncomputable section

variable {Active Tail : Type*}
  [NormedAddCommGroup Active] [NormedAddCommGroup Tail]

/-- Exact Euclidean split between a selected frontier and its discarded
coordinate tail. -/
abbrev SplitDirection (Active Tail : Type*)
    [NormedAddCommGroup Active] [NormedAddCommGroup Tail] :=
  WithLp 2 (Active × Tail)

/-- Retain the selected frontier and zero every discarded coordinate. -/
def keepActive (direction : SplitDirection Active Tail) :
    SplitDirection Active Tail :=
  WithLp.toLp 2 (direction.fst, 0)

/-- Retain only the discarded tail. -/
def keepTail (direction : SplitDirection Active Tail) :
    SplitDirection Active Tail :=
  WithLp.toLp 2 (0, direction.snd)

@[simp] theorem norm_keepActive (direction : SplitDirection Active Tail) :
    ‖keepActive direction‖ = ‖direction.fst‖ := by
  exact WithLp.norm_toLp_fst 2 _ _ direction.fst

@[simp] theorem norm_keepTail (direction : SplitDirection Active Tail) :
    ‖keepTail direction‖ = ‖direction.snd‖ := by
  exact WithLp.norm_toLp_snd 2 _ _ direction.snd

theorem keepActive_add_keepTail (direction : SplitDirection Active Tail) :
    keepActive direction + keepTail direction = direction := by
  apply WithLp.ofLp_injective 2
  simp only [keepActive, keepTail, WithLp.ofLp_add, Prod.mk_add_mk,
    add_zero, zero_add]
  exact Prod.eta _

/-- Restricting to the frontier makes exactly the discarded tail error. -/
theorem norm_keepActive_sub_eq_tail
    (direction : SplitDirection Active Tail) :
    ‖keepActive direction - direction‖ = ‖keepTail direction‖ := by
  have hdifference :
      keepActive direction - direction = -keepTail direction := by
    calc
      keepActive direction - direction =
          keepActive direction -
            (keepActive direction + keepTail direction) := by
        rw [keepActive_add_keepTail]
      _ = -keepTail direction := by abel
  rw [hdifference, norm_neg]

/-- The full squared norm decomposes into selected and discarded mass. -/
theorem norm_sq_eq_active_add_tail
    (direction : SplitDirection Active Tail) :
    ‖direction‖ ^ 2 =
      ‖keepActive direction‖ ^ 2 + ‖keepTail direction‖ ^ 2 := by
  simpa using WithLp.prod_norm_sq_eq_of_L2 direction

/-- A measured lower bound on the fraction of squared update mass retained by
the selected frontier. -/
structure SquaredMassCapture
    (direction : SplitDirection Active Tail) (fraction : ℝ) : Prop where
  fraction_nonneg : 0 ≤ fraction
  fraction_le_one : fraction ≤ 1
  captured :
    fraction * ‖direction‖ ^ 2 ≤ ‖keepActive direction‖ ^ 2

/-- Captured mass converts exactly into an upper bound on discarded squared
mass. -/
theorem SquaredMassCapture.tail_sq_le_uncaptured
    {direction : SplitDirection Active Tail} {fraction : ℝ}
    (certificate : SquaredMassCapture direction fraction) :
    ‖keepTail direction‖ ^ 2 ≤
      (1 - fraction) * ‖direction‖ ^ 2 := by
  have decomposition := norm_sq_eq_active_add_tail direction
  nlinarith [certificate.captured]

/-- Exact binary32 squared masses share the dyadic denominator `2^298`.
The structure is more general in the denominator exponent so other finite
formats can use the same bridge. -/
structure DyadicSquaredMassReport
    (direction : SplitDirection Active Tail) where
  denominatorPower : ℕ
  totalNumerator : ℕ
  selectedNumerator : ℕ
  tailNumerator : ℕ
  total_pos : 0 < totalNumerator
  selected_add_tail :
    selectedNumerator + tailNumerator = totalNumerator
  full_mass :
    ‖direction‖ ^ 2 =
      (totalNumerator : ℝ) / 2 ^ denominatorPower
  selected_mass :
    ‖keepActive direction‖ ^ 2 =
      (selectedNumerator : ℝ) / 2 ^ denominatorPower

/-- The exact selected-mass fraction carried by a nonzero dyadic report. -/
def DyadicSquaredMassReport.capturedFraction
    {direction : SplitDirection Active Tail}
    (report : DyadicSquaredMassReport direction) : ℝ :=
  (report.selectedNumerator : ℝ) / report.totalNumerator

theorem DyadicSquaredMassReport.selected_le_total
    {direction : SplitDirection Active Tail}
    (report : DyadicSquaredMassReport direction) :
    report.selectedNumerator ≤ report.totalNumerator := by
  have decomposition := report.selected_add_tail
  omega

/-- Exact dyadic numerator accounting produces the abstract mass-capture
certificate consumed by the descent theorem. -/
def DyadicSquaredMassReport.toSquaredMassCapture
    {direction : SplitDirection Active Tail}
    (report : DyadicSquaredMassReport direction) :
    SquaredMassCapture direction report.capturedFraction where
  fraction_nonneg := by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  fraction_le_one := by
    rw [DyadicSquaredMassReport.capturedFraction]
    exact (div_le_one (by exact_mod_cast report.total_pos)).2
      (by exact_mod_cast report.selected_le_total)
  captured := by
    have total_ne :
        (report.totalNumerator : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt report.total_pos)
    rw [DyadicSquaredMassReport.capturedFraction, report.full_mass,
      report.selected_mass]
    field_simp [total_ne]
    exact le_rfl

/-- The discarded dyadic numerator is exactly the squared tail mass. -/
theorem DyadicSquaredMassReport.tail_mass
    {direction : SplitDirection Active Tail}
    (report : DyadicSquaredMassReport direction) :
    ‖keepTail direction‖ ^ 2 =
      (report.tailNumerator : ℝ) / 2 ^ report.denominatorPower := by
  have decomposition := norm_sq_eq_active_add_tail direction
  have numerator_decomposition :
      (report.selectedNumerator : ℝ) + report.tailNumerator =
        report.totalNumerator := by
    exact_mod_cast report.selected_add_tail
  rw [report.full_mass, report.selected_mass] at decomposition
  calc
    ‖keepTail direction‖ ^ 2 =
        (report.totalNumerator : ℝ) / 2 ^ report.denominatorPower -
          report.selectedNumerator / 2 ^ report.denominatorPower := by
      linarith
    _ = (report.tailNumerator : ℝ) / 2 ^ report.denominatorPower := by
      rw [← numerator_decomposition]
      ring

variable [InnerProductSpace ℝ Active] [InnerProductSpace ℝ Tail]

/-- Any explicit tail bound gives the conservative first-order margin for the
frontier-restricted direction. -/
theorem activeDirection_inner_lower
    (direction : SplitDirection Active Tail) (error : ℝ)
    (htail : ‖keepTail direction‖ ≤ error) :
    ‖direction‖ * (‖direction‖ - error) ≤
      ⟪direction, keepActive direction⟫_ℝ := by
  apply approximateDirection_inner_lower direction (keepActive direction) error
  simpa [norm_keepActive_sub_eq_tail] using htail

/-- A frontier tail certificate feeds the existing smooth-task descent gate.
This theorem certifies a finite parameter step, not the frontier-selection
heuristic. -/
theorem strictTaskDescent_of_tail_bound
    {loss : SplitDirection Active Tail → ℝ}
    {parameter direction : SplitDirection Active Tail}
    {beta error step : ℝ}
    (certificate :
      HasSmoothTaskUpperModelAt loss parameter direction beta)
    (htail : ‖keepTail direction‖ ≤ error)
    (hbeta : 0 ≤ beta) (hstep : 0 < step)
    (hrelative : error < ‖direction‖)
    (htrust :
      beta * step * (‖direction‖ + error) ^ 2 / 2 <
        ‖direction‖ * (‖direction‖ - error)) :
    loss (parameter - step • keepActive direction) < loss parameter := by
  have herror :
      ‖keepActive direction - direction‖ ≤ error := by
    rw [norm_keepActive_sub_eq_tail]
    exact htail
  exact smoothTask_strict_descent_of_norm_error
    certificate herror hbeta hstep hrelative htrust

/-! ## Exact scalar fixtures -/

abbrev ScalarSplit := SplitDirection ℝ ℝ

/-- Three units retained and four discarded: full norm five. -/
def threeFourDirection : ScalarSplit :=
  WithLp.toLp 2 (3, 4)

theorem threeFourDirection_norm : ‖threeFourDirection‖ = 5 := by
  rw [WithLp.prod_norm_eq_of_L2]
  norm_num [threeFourDirection, Real.norm_eq_abs]

theorem threeFourDirection_active_norm :
    ‖keepActive threeFourDirection‖ = 3 := by
  norm_num [threeFourDirection, Real.norm_eq_abs]

theorem threeFourDirection_tail_norm :
    ‖keepTail threeFourDirection‖ = 4 := by
  norm_num [threeFourDirection, Real.norm_eq_abs]

/-- The retained coordinate carries exactly nine twenty-fifths of the squared
mass. -/
def threeFourCapture :
    SquaredMassCapture threeFourDirection (9 / 25 : ℝ) where
  fraction_nonneg := by norm_num
  fraction_le_one := by norm_num
  captured := by
    rw [threeFourDirection_norm, threeFourDirection_active_norm]
    norm_num

theorem threeFourCapture_tail_bound_exact :
    ‖keepTail threeFourDirection‖ ^ 2 =
      (1 - (9 / 25 : ℝ)) * ‖threeFourDirection‖ ^ 2 := by
  rw [threeFourDirection_tail_norm, threeFourDirection_norm]
  norm_num

/-- The same fixture in the exact dyadic-numerator interface emitted by the
runtime probe. -/
def threeFourDyadicReport :
    DyadicSquaredMassReport threeFourDirection where
  denominatorPower := 0
  totalNumerator := 25
  selectedNumerator := 9
  tailNumerator := 16
  total_pos := by norm_num
  selected_add_tail := by norm_num
  full_mass := by
    rw [threeFourDirection_norm]
    norm_num
  selected_mass := by
    rw [threeFourDirection_active_norm]
    norm_num

theorem threeFourDyadicReport_fraction :
    threeFourDyadicReport.capturedFraction = 9 / 25 := by
  norm_num [threeFourDyadicReport, DyadicSquaredMassReport.capturedFraction]

theorem threeFourDyadicReport_tail_mass :
    ‖keepTail threeFourDirection‖ ^ 2 = 16 := by
  simpa [threeFourDyadicReport] using threeFourDyadicReport.tail_mass

/-- Negative fixture: selecting the first coordinate misses a direction that
lives entirely in the tail. -/
def missedDirection : ScalarSplit :=
  WithLp.toLp 2 (0, 1)

theorem keepActive_missedDirection : keepActive missedDirection = 0 := by
  rfl

theorem missed_frontier_has_no_positive_alignment :
    ¬ 0 < ⟪missedDirection, keepActive missedDirection⟫_ℝ := by
  rw [keepActive_missedDirection]
  simp

#print axioms norm_keepActive_sub_eq_tail
#print axioms norm_sq_eq_active_add_tail
#print axioms SquaredMassCapture.tail_sq_le_uncaptured
#print axioms DyadicSquaredMassReport.toSquaredMassCapture
#print axioms DyadicSquaredMassReport.tail_mass
#print axioms activeDirection_inner_lower
#print axioms strictTaskDescent_of_tail_bound
#print axioms threeFourCapture_tail_bound_exact
#print axioms threeFourDyadicReport_fraction
#print axioms threeFourDyadicReport_tail_mass
#print axioms missed_frontier_has_no_positive_alignment

end

end ActiveFrontierSettling

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
