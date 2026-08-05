import Mathlib.Tactic

/-!
# Value-of-information bounds for metalevel computation

This module isolates the deterministic order-theoretic core of Theorem 5 in
Hay, Russell, Tolpin, and Shimony, *Selecting Computations: Theory and
Applications* (arXiv:1207.5879).  A metalevel policy pays a positive cost for
each computation and eventually receives an object-level terminal value.  If
the policy is at least as good as stopping immediately, while its expected
terminal value is no greater than perfect information, then its expected
computation count is bounded by value of perfect information divided by cost.

The theorem is stated over real-valued expectations.  Constructing those
expectations from a probability model, and proving almost-sure termination
from integrability, remain separate measure-theoretic obligations.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
namespace MetalevelComputationBudget

/-- Net metalevel value: expected terminal object-level value minus expected
computation cost. -/
def netValue (expectedTerminal cost expectedComputations : ℝ) : ℝ :=
  expectedTerminal - cost * expectedComputations

/-- Evidence needed for the value-of-perfect-information computation bound.
The fields separate policy quality, terminal-value optimism, and accounting;
none of them presupposes the desired bound. -/
structure Certificate where
  cost : ℝ
  expectedComputations : ℝ
  stopValue : ℝ
  expectedTerminal : ℝ
  perfectInformationValue : ℝ
  cost_pos : 0 < cost
  expectedComputations_nonneg : 0 ≤ expectedComputations
  stop_le_netValue :
    stopValue ≤ netValue expectedTerminal cost expectedComputations
  terminal_le_perfect : expectedTerminal ≤ perfectInformationValue

/-- Value of perfect information relative to stopping immediately. -/
def valueOfPerfectInformation (certificate : Certificate) : ℝ :=
  certificate.perfectInformationValue - certificate.stopValue

/-- The value of perfect information in any certificate is nonnegative. -/
theorem valueOfPerfectInformation_nonneg (certificate : Certificate) :
    0 ≤ valueOfPerfectInformation certificate := by
  unfold valueOfPerfectInformation
  have hstopTerminal :
      certificate.stopValue ≤ certificate.expectedTerminal := by
    calc
      certificate.stopValue
          ≤ netValue certificate.expectedTerminal certificate.cost
              certificate.expectedComputations :=
        certificate.stop_le_netValue
      _ ≤ certificate.expectedTerminal := by
        unfold netValue
        have hcost :
            0 ≤ certificate.cost * certificate.expectedComputations :=
          mul_nonneg certificate.cost_pos.le
            certificate.expectedComputations_nonneg
        linarith
  linarith [certificate.terminal_le_perfect]

/-- Expected computation is bounded by value of perfect information divided
by the positive per-computation cost. -/
theorem expectedComputations_le_valueOfPerfectInformation_div
    (certificate : Certificate) :
    certificate.expectedComputations ≤
      valueOfPerfectInformation certificate / certificate.cost := by
  apply (le_div_iff₀ certificate.cost_pos).2
  have hnet := certificate.stop_le_netValue
  rw [netValue] at hnet
  unfold valueOfPerfectInformation
  nlinarith [certificate.terminal_le_perfect]

/-- Equivalent multiplicative form, useful when a runtime records cost and
work but avoids division. -/
theorem expectedCost_le_valueOfPerfectInformation
    (certificate : Certificate) :
    certificate.cost * certificate.expectedComputations ≤
      valueOfPerfectInformation certificate := by
  have hnet := certificate.stop_le_netValue
  rw [netValue] at hnet
  unfold valueOfPerfectInformation
  linarith [certificate.terminal_le_perfect]

/-- If perfect information cannot improve on stopping, every certified policy
performs zero expected computation. -/
theorem expectedComputations_eq_zero_of_no_information_value
    (certificate : Certificate)
    (hzero : valueOfPerfectInformation certificate = 0) :
    certificate.expectedComputations = 0 := by
  apply le_antisymm
  · simpa [hzero] using
      expectedComputations_le_valueOfPerfectInformation_div certificate
  · exact certificate.expectedComputations_nonneg

/-! ## Positive and negative boundary fixtures -/

/-- A nontrivial certificate attaining the bound exactly. -/
def tightCertificate : Certificate where
  cost := 2
  expectedComputations := 3
  stopValue := 4
  expectedTerminal := 10
  perfectInformationValue := 10
  cost_pos := by norm_num
  expectedComputations_nonneg := by norm_num
  stop_le_netValue := by norm_num [netValue]
  terminal_le_perfect := by norm_num

theorem tightCertificate_attains_bound :
    tightCertificate.expectedComputations =
      valueOfPerfectInformation tightCertificate / tightCertificate.cost := by
  norm_num [tightCertificate, valueOfPerfectInformation]

/-- Without positive cost, the other accounting conditions permit an
arbitrarily large computation count.  This witnesses why `cost_pos` is a real
hypothesis rather than a removable technicality. -/
theorem zero_cost_allows_arbitrary_expectedComputations
    (computations : ℝ) (hcomputations : 0 ≤ computations) :
    let expectedTerminal : ℝ := 1
    let stopValue : ℝ := 1
    0 ≤ computations ∧
      stopValue ≤ netValue expectedTerminal 0 computations ∧
        expectedTerminal ≤ 1 := by
  simpa [netValue] using hcomputations

/-- An alleged policy whose net value is below immediate stopping cannot
provide a certificate, even when its terminal value is perfect. -/
theorem losing_policy_has_no_certificate
    (cost computations : ℝ) (hcost : 0 < cost)
    (hcomputations : 0 < computations) :
    ¬ (1 : ℝ) ≤ netValue 1 cost computations := by
  unfold netValue
  nlinarith

#print axioms valueOfPerfectInformation_nonneg
#print axioms expectedComputations_le_valueOfPerfectInformation_div
#print axioms expectedCost_le_valueOfPerfectInformation
#print axioms expectedComputations_eq_zero_of_no_information_value
#print axioms tightCertificate_attains_bound
#print axioms zero_cost_allows_arbitrary_expectedComputations
#print axioms losing_policy_has_no_certificate

end MetalevelComputationBudget
end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
