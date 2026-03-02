import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mettapedia.Logic.PremiseSelectionCoverage

/-!
# Coverage-Objective Counterexamples

This file records finite counterexamples showing limits of the pure dependency-coverage
surrogate used in premise selection.

Main message:
- Two selectors can have identical `(coverage, cardinality)` statistics,
- yet induce different downstream false-positive risk.

So coverage (even with fixed budget/cardinality) is not enough to recover risk-sensitive
selection quality.
-/

namespace Mettapedia.Logic.PremiseSelection
open scoped BigOperators

abbrev Fact3 := Fin 3

def D_cov : Finset Fact3 := {0}
def S_cov_lowRisk : Finset Fact3 := {0, 1}
def S_cov_highRisk : Finset Fact3 := {0, 2}

def riskWeight : Fact3 → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 5

/-- Sum of risk weights on selected false positives (`S \ D`). -/
def falsePositiveRisk (D S : Finset Fact3) : Nat :=
  Finset.sum (S \ D) riskWeight

lemma falsePositiveRisk_lowRisk :
    falsePositiveRisk D_cov S_cov_lowRisk = 0 := by
  simp [falsePositiveRisk, D_cov, S_cov_lowRisk, riskWeight]

lemma falsePositiveRisk_highRisk :
    falsePositiveRisk D_cov S_cov_highRisk = 5 := by
  have hdiff : S_cov_highRisk \ D_cov = ({2} : Finset Fact3) := by
    ext x
    fin_cases x <;> simp [S_cov_highRisk, D_cov]
  simp [falsePositiveRisk, hdiff, riskWeight]

theorem coverage_counterexample_values :
    dependencyCoverage D_cov S_cov_lowRisk = 1
      ∧ dependencyCoverage D_cov S_cov_highRisk = 1
      ∧ S_cov_lowRisk.card = 2
      ∧ S_cov_highRisk.card = 2
      ∧ falsePositiveRisk D_cov S_cov_lowRisk = 0
      ∧ falsePositiveRisk D_cov S_cov_highRisk = 5 := by
  refine ⟨by decide, by decide, by decide, by decide, falsePositiveRisk_lowRisk, falsePositiveRisk_highRisk⟩

/-- Same `(coverage, card)` statistics can hide different false-positive risk. -/
theorem sameCoverageAndCard_differentFalsePositiveRisk :
    dependencyCoverage D_cov S_cov_lowRisk = dependencyCoverage D_cov S_cov_highRisk
      ∧ S_cov_lowRisk.card = S_cov_highRisk.card
      ∧ falsePositiveRisk D_cov S_cov_lowRisk ≠ falsePositiveRisk D_cov S_cov_highRisk := by
  rcases coverage_counterexample_values with ⟨hCovLow, hCovHigh, hCardLow, hCardHigh, hRiskLow, hRiskHigh⟩
  refine ⟨hCovLow.trans hCovHigh.symm, hCardLow.trans hCardHigh.symm, ?_⟩
  intro hEq
  simp [hRiskLow, hRiskHigh] at hEq

/-- No universal predictor from `(coverage, card)` can recover false-positive risk. -/
theorem no_universal_risk_predictor_from_coverage_and_card :
    ¬ ∃ F : Nat → Nat → Nat,
        ∀ S : Finset Fact3,
          falsePositiveRisk D_cov S = F (dependencyCoverage D_cov S) S.card := by
  intro h
  rcases h with ⟨F, hF⟩
  have hLow := hF S_cov_lowRisk
  have hHigh := hF S_cov_highRisk
  have hCov :
      dependencyCoverage D_cov S_cov_lowRisk = dependencyCoverage D_cov S_cov_highRisk := by
    exact (sameCoverageAndCard_differentFalsePositiveRisk).1
  have hCard : S_cov_lowRisk.card = S_cov_highRisk.card := by
    exact (sameCoverageAndCard_differentFalsePositiveRisk).2.1
  have hEqRisk :
      falsePositiveRisk D_cov S_cov_lowRisk = falsePositiveRisk D_cov S_cov_highRisk := by
    calc
      falsePositiveRisk D_cov S_cov_lowRisk
          = F (dependencyCoverage D_cov S_cov_lowRisk) S_cov_lowRisk.card := hLow
      _ = F (dependencyCoverage D_cov S_cov_highRisk) S_cov_highRisk.card := by
        simp [hCov, hCard]
      _ = falsePositiveRisk D_cov S_cov_highRisk := hHigh.symm
  have hNe :
      falsePositiveRisk D_cov S_cov_lowRisk ≠ falsePositiveRisk D_cov S_cov_highRisk := by
    exact (sameCoverageAndCard_differentFalsePositiveRisk).2.2
  exact hNe hEqRisk

end Mettapedia.Logic.PremiseSelection
