import Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.Basic
import Mathlib.Order.Filter.Extr

/-!
# Task pressure, certified comparisons and finite Gibbs laws

Two cross-comparisons suffice to bound the change in achieved utility and
regularization. No convexity, smoothness or Gaussian assumption is used.
Approximate comparisons expose their errors explicitly. The constructed
finite Gibbs optimizer is an actual consumer of these abstract bounds.

The exact comparison specializes Proposition 5.3 of Goertzel, *Trajectory
Free Energy and Integrated Organization* (2026).
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy

universe u

def pressureObjective {Choice : Type u} (regularizer utility : Choice → ℝ)
    (pressure : ℝ) (choice : Choice) : ℝ := regularizer choice - pressure * utility choice

theorem two_pressure_cross_bounds {Choice : Type u} (regularizer utility : Choice → ℝ)
    (first second : Choice) (low high errorLow errorHigh : ℝ)
    (firstComparison : pressureObjective regularizer utility low first ≤
      pressureObjective regularizer utility low second + errorLow)
    (secondComparison : pressureObjective regularizer utility high second ≤
      pressureObjective regularizer utility high first + errorHigh) :
    low * (utility second - utility first) - errorLow ≤ regularizer second - regularizer first ∧
      regularizer second - regularizer first ≤ high * (utility second - utility first) + errorHigh := by
  unfold pressureObjective at firstComparison secondComparison
  constructor <;> nlinarith

theorem two_pressure_approximate {Choice : Type u} (regularizer utility : Choice → ℝ)
    (first second : Choice) (low high errorLow errorHigh : ℝ) (increase : low < high)
    (firstComparison : pressureObjective regularizer utility low first ≤
      pressureObjective regularizer utility low second + errorLow)
    (secondComparison : pressureObjective regularizer utility high second ≤
      pressureObjective regularizer utility high first + errorHigh) :
    -(errorLow + errorHigh) / (high - low) ≤ utility second - utility first := by
  rw [div_le_iff₀ (sub_pos.mpr increase)]
  have bounds := two_pressure_cross_bounds regularizer utility first second low high errorLow errorHigh
    firstComparison secondComparison
  nlinarith [bounds.1, bounds.2]

theorem two_pressure_exact {Choice : Type u} (regularizer utility : Choice → ℝ)
    (first second : Choice) (low high : ℝ) (increase : low < high)
    (firstComparison : pressureObjective regularizer utility low first ≤
      pressureObjective regularizer utility low second)
    (secondComparison : pressureObjective regularizer utility high second ≤
      pressureObjective regularizer utility high first) :
    0 ≤ utility second - utility first ∧
      low * (utility second - utility first) ≤ regularizer second - regularizer first ∧
      regularizer second - regularizer first ≤ high * (utility second - utility first) := by
  have firstBound := two_pressure_cross_bounds regularizer utility first second low high 0 0
    (by simpa only [add_zero] using firstComparison) (by simpa only [add_zero] using secondComparison)
  have utilityBound := two_pressure_approximate regularizer utility first second low high 0 0 increase
    (by simpa only [add_zero] using firstComparison) (by simpa only [add_zero] using secondComparison)
  simpa only [add_zero, neg_zero, zero_div, sub_zero] using And.intro utilityBound firstBound

theorem two_pressure_minima {Choice : Type u} (admissible : Set Choice) (regularizer utility : Choice → ℝ)
    (first second : Choice) (firstMember : first ∈ admissible) (secondMember : second ∈ admissible)
    (low high : ℝ) (increase : low < high)
    (firstMinimum : IsMinOn (pressureObjective regularizer utility low) admissible first)
    (secondMinimum : IsMinOn (pressureObjective regularizer utility high) admissible second) :
    0 ≤ utility second - utility first ∧
      low * (utility second - utility first) ≤ regularizer second - regularizer first ∧
      regularizer second - regularizer first ≤ high * (utility second - utility first) :=
  two_pressure_exact regularizer utility first second low high increase
    (firstMinimum secondMember) (secondMinimum firstMember)

noncomputable section

open scoped BigOperators
open Mettapedia.InformationTheory Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.BayesianInference

variable {Ω : Type*} [Fintype Ω]

def pressureGibbs (reference : Prob Ω) (utility : Ω → ℝ) (pressure : ℝ) : Prob Ω :=
  gibbs reference (fun x => -pressure * utility x) 1 (by norm_num)

theorem pressureGibbs_supported (reference : Prob Ω) (utility : Ω → ℝ) (pressure : ℝ) :
    SupportedBy (pressureGibbs reference utility pressure) reference.1 :=
  gibbs_supported reference _ 1 (by norm_num)

theorem pressure_objective_eq (reference law : Prob Ω) (utility : Ω → ℝ) (pressure : ℝ) :
    pressureObjective (fun candidate : Prob Ω => klSum candidate.1 reference.1)
      (fun candidate => expectedCost candidate utility) pressure law =
        freeEnergy reference (fun x => -pressure * utility x) 1 law := by
  have scaled : expectedCost law (fun x => -pressure * utility x) = -pressure * expectedCost law utility := by
    unfold expectedCost
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [pressureObjective, freeEnergy, scaled, one_mul]
  ring

theorem pressureGibbs_minimum (reference : Prob Ω) (utility : Ω → ℝ) (pressure : ℝ) :
    IsMinOn (pressureObjective (fun law : Prob Ω => klSum law.1 reference.1)
      (fun law => expectedCost law utility) pressure) {law | SupportedBy law reference.1}
      (pressureGibbs reference utility pressure) := by
  rw [isMinOn_iff]
  intro law supported
  rw [pressure_objective_eq, pressure_objective_eq]
  exact gibbs_minimizes reference law _ 1 (by norm_num) supported

theorem pressureGibbs_comparison (reference : Prob Ω) (utility : Ω → ℝ)
    (low high : ℝ) (increase : low < high) :
    0 ≤ expectedCost (pressureGibbs reference utility high) utility -
        expectedCost (pressureGibbs reference utility low) utility ∧
      low * (expectedCost (pressureGibbs reference utility high) utility -
        expectedCost (pressureGibbs reference utility low) utility) ≤
          klSum (pressureGibbs reference utility high).1 reference.1 -
            klSum (pressureGibbs reference utility low).1 reference.1 ∧
      klSum (pressureGibbs reference utility high).1 reference.1 -
        klSum (pressureGibbs reference utility low).1 reference.1 ≤
          high * (expectedCost (pressureGibbs reference utility high) utility -
            expectedCost (pressureGibbs reference utility low) utility) :=
  two_pressure_minima {law : Prob Ω | SupportedBy law reference.1}
    (fun law => klSum law.1 reference.1) (fun law => expectedCost law utility) _ _
    (pressureGibbs_supported reference utility low) (pressureGibbs_supported reference utility high)
    low high increase (pressureGibbs_minimum reference utility low) (pressureGibbs_minimum reference utility high)

theorem pressureGibbs_divergence_mono (reference : Prob Ω) (utility : Ω → ℝ)
    (low high : ℝ) (nonnegative : 0 ≤ low) (increase : low < high) :
    klSum (pressureGibbs reference utility low).1 reference.1 ≤
      klSum (pressureGibbs reference utility high).1 reference.1 := by
  have compared := pressureGibbs_comparison reference utility low high increase
  have lower := mul_nonneg nonnegative compared.1
  linarith [compared.2.1]

end

end Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy
