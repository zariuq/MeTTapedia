import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic

/-!
# Precise vs Imprecise Probability: When Decisions Differ

This file provides a **fully formal** example showing when precise and imprecise
probability lead to different decisions.

## The Setup

A decision problem with:
- 3 states of the world: Safe, Risky, Catastrophic
- 2 actions: Normal, Cautious
- Asymmetric payoffs (catastrophic outcome is very bad)

## Key Results

1. With precise probability, the optimal action depends sensitively on P(Catastrophic)
2. With imprecise probability + maximin, the decision is robust
3. There exist probability ranges where EU and maximin disagree

## The Point

When you genuinely don't know P(Catastrophic), imprecise probability + maximin
gives a robust answer without forcing you to pretend you know.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Examples.PreciseVsImprecise

/-! ## §1: The Decision Problem -/

/-- States of the world -/
inductive State
  | safe        -- Everything is fine
  | risky       -- Some problems, manageable
  | catastrophic -- Very bad outcome
  deriving DecidableEq

/-- Available actions -/
inductive Action
  | normal   -- Business as usual
  | cautious -- Safety-first
  deriving DecidableEq

open State Action

/-! ## §2: Payoff Matrix (using rationals for exact computation) -/

/-- Payoff matrix using rationals for exact arithmetic.

| Action   | Safe | Risky | Catastrophic |
|----------|------|-------|--------------|
| Normal   | 100  | 50    | -1000        |
| Cautious | 80   | 70    | 60           |
-/
def payoff : Action → State → ℚ
  | normal, safe => 100
  | normal, risky => 50
  | normal, catastrophic => -1000
  | cautious, safe => 80
  | cautious, risky => 70
  | cautious, catastrophic => 60

/-! ## §3: Precise Probability -/

/-- A precise probability distribution over states (using rationals) -/
structure PreciseProb where
  pSafe : ℚ
  pRisky : ℚ
  pCatastrophic : ℚ
  nonneg_safe : 0 ≤ pSafe
  nonneg_risky : 0 ≤ pRisky
  nonneg_cat : 0 ≤ pCatastrophic
  sum_one : pSafe + pRisky + pCatastrophic = 1

namespace PreciseProb

/-- Expected utility of an action under a precise distribution -/
def expectedUtility (P : PreciseProb) (a : Action) : ℚ :=
  P.pSafe * payoff a safe + P.pRisky * payoff a risky + P.pCatastrophic * payoff a catastrophic

/-- Normal is better iff EU(normal) > EU(cautious) -/
def normalIsBetter (P : PreciseProb) : Prop :=
  P.expectedUtility normal > P.expectedUtility cautious

/-- Cautious is better iff EU(cautious) > EU(normal) -/
def cautiousIsBetter (P : PreciseProb) : Prop :=
  P.expectedUtility cautious > P.expectedUtility normal

/-- EU difference formula -/
theorem EU_diff_formula (P : PreciseProb) :
    P.expectedUtility normal - P.expectedUtility cautious =
    20 * P.pSafe - 20 * P.pRisky - 1060 * P.pCatastrophic := by
  simp only [expectedUtility, payoff]
  ring

end PreciseProb

/-! ## §4: Example Distributions -/

/-- Low catastrophic risk: P(Cat) = 1/200 = 0.5% -/
def lowRiskDist : PreciseProb where
  pSafe := 179/200      -- 0.895
  pRisky := 1/10        -- 0.1
  pCatastrophic := 1/200  -- 0.005
  nonneg_safe := by norm_num
  nonneg_risky := by norm_num
  nonneg_cat := by norm_num
  sum_one := by norm_num

/-- High catastrophic risk: P(Cat) = 1/20 = 5% -/
def highRiskDist : PreciseProb where
  pSafe := 17/20        -- 0.85
  pRisky := 1/10        -- 0.1
  pCatastrophic := 1/20   -- 0.05
  nonneg_safe := by norm_num
  nonneg_risky := by norm_num
  nonneg_cat := by norm_num
  sum_one := by norm_num

/-- At low risk, Normal wins -/
theorem lowRisk_normal_wins : lowRiskDist.normalIsBetter := by
  unfold PreciseProb.normalIsBetter PreciseProb.expectedUtility payoff lowRiskDist
  norm_num

/-- At high risk, Cautious wins -/
theorem highRisk_cautious_wins : highRiskDist.cautiousIsBetter := by
  unfold PreciseProb.cautiousIsBetter PreciseProb.expectedUtility payoff highRiskDist
  norm_num

/-! ## §5: Imprecise Probability -/

/-- Imprecise probability: intervals for state probabilities -/
structure ImpreciseProb where
  pSafe_lo : ℚ
  pSafe_hi : ℚ
  pRisky_lo : ℚ
  pRisky_hi : ℚ
  pCat_lo : ℚ
  pCat_hi : ℚ
  safe_valid : pSafe_lo ≤ pSafe_hi
  risky_valid : pRisky_lo ≤ pRisky_hi
  cat_valid : pCat_lo ≤ pCat_hi
  all_nonneg : 0 ≤ pSafe_lo ∧ 0 ≤ pRisky_lo ∧ 0 ≤ pCat_lo

namespace ImpreciseProb

/-- Worst-case utility for Normal action.
    Normal's payoff in catastrophic state is -1000 (worst).
    So worst case maximizes pCatastrophic and minimizes good states. -/
def worstCase_normal (I : ImpreciseProb) : ℚ :=
  I.pSafe_lo * 100 + I.pRisky_lo * 50 + I.pCat_hi * (-1000)

/-- Worst-case utility for Cautious action.
    Cautious has positive payoffs everywhere (60, 70, 80).
    Worst case minimizes all (uses lowest probabilities for highest payoffs). -/
def worstCase_cautious (I : ImpreciseProb) : ℚ :=
  I.pSafe_lo * 80 + I.pRisky_lo * 70 + I.pCat_hi * 60

/-- Maximin prefers Cautious if worst(Cautious) > worst(Normal) -/
def maximinPrefersCautious (I : ImpreciseProb) : Prop :=
  I.worstCase_cautious > I.worstCase_normal

end ImpreciseProb

/-! ## §6: The Key Example -/

/-- Uncertainty range: P(Cat) ∈ [0.5%, 5%] = [1/200, 1/20] -/
def uncertaintyRange : ImpreciseProb where
  pSafe_lo := 17/20     -- 0.85 (when pCat is high)
  pSafe_hi := 179/200   -- 0.895 (when pCat is low)
  pRisky_lo := 1/10
  pRisky_hi := 1/10
  pCat_lo := 1/200      -- 0.5%
  pCat_hi := 1/20       -- 5%
  safe_valid := by norm_num
  risky_valid := by norm_num
  cat_valid := by norm_num
  all_nonneg := by norm_num

/-- Compute worst case for Normal under uncertainty -/
theorem normal_worst_case_val :
    uncertaintyRange.worstCase_normal = 17/20 * 100 + 1/10 * 50 + 1/20 * (-1000) := rfl

/-- Compute worst case for Cautious under uncertainty -/
theorem cautious_worst_case_val :
    uncertaintyRange.worstCase_cautious = 17/20 * 80 + 1/10 * 70 + 1/20 * 60 := rfl

/-- Worst case Normal = 85 + 5 - 50 = 40 -/
theorem normal_worst_simplified : uncertaintyRange.worstCase_normal = 40 := by
  unfold ImpreciseProb.worstCase_normal uncertaintyRange
  norm_num

/-- Worst case Cautious = 68 + 7 + 3 = 78 -/
theorem cautious_worst_simplified : uncertaintyRange.worstCase_cautious = 78 := by
  unfold ImpreciseProb.worstCase_cautious uncertaintyRange
  norm_num

/-- **Main Result**: Maximin prefers Cautious (78 > 40) -/
theorem maximin_prefers_cautious : uncertaintyRange.maximinPrefersCautious := by
  unfold ImpreciseProb.maximinPrefersCautious
  rw [normal_worst_simplified, cautious_worst_simplified]
  norm_num

/-! ## §7: The Central Theorem -/

/-- **Decisions Differ**: EU and Maximin give different answers depending on
    where in the uncertainty range the true probability lies.

    - At P(Cat) = 0.5%: EU prefers Normal
    - At P(Cat) = 5%: EU prefers Cautious
    - Maximin: Always prefers Cautious (robust to uncertainty)
-/
theorem decisions_differ :
    lowRiskDist.normalIsBetter ∧
    highRiskDist.cautiousIsBetter ∧
    uncertaintyRange.maximinPrefersCautious :=
  ⟨lowRisk_normal_wins, highRisk_cautious_wins, maximin_prefers_cautious⟩

/-! ## §8: The Breakeven Point -/

/-- The breakeven probability where EU(Normal) = EU(Cautious).

From EU_diff_formula: 20*pSafe - 20*pRisky - 1060*pCat = 0
With pRisky = 0.1 and pSafe = 0.9 - pCat:
  20*(0.9 - pCat) - 20*0.1 - 1060*pCat = 0
  18 - 2 - 20*pCat - 1060*pCat = 0
  16 = 1080*pCat
  pCat = 16/1080 = 2/135 ≈ 0.0148 ≈ 1.48%
-/
def breakeven_pCat : ℚ := 2/135

/-- Verify: At breakeven, EU difference is zero -/
def breakevenDist : PreciseProb where
  pSafe := 1 - 1/10 - 2/135  -- = 121/135 - 1/10 = (1210 - 135)/1350 = 1075/1350
  pRisky := 1/10
  pCatastrophic := 2/135
  nonneg_safe := by norm_num
  nonneg_risky := by norm_num
  nonneg_cat := by norm_num
  sum_one := by norm_num

theorem breakeven_EU_equal :
    breakevenDist.expectedUtility normal = breakevenDist.expectedUtility cautious := by
  unfold PreciseProb.expectedUtility payoff breakevenDist
  norm_num

/-! ## Summary

This example formally proves:

1. **Precise probability is fragile**: The optimal action flips at P(Cat) ≈ 1.48%

2. **Imprecise probability is robust**: Maximin chooses Cautious for any
   P(Cat) ∈ [0.5%, 5%], without needing the exact value

3. **The gap is significant**:
   - Worst case Normal: 40
   - Worst case Cautious: 78
   - Ratio: nearly 2x better worst-case for Cautious

4. **When to use which**:
   - If you KNOW P(Cat) < 1.48%: Normal is optimal (higher EU)
   - If you KNOW P(Cat) > 1.48%: Cautious is optimal
   - If you DON'T KNOW: Maximin says Cautious (robust choice)

This is the formal basis for why imprecise probability + maximin is appropriate
for existential risk: we genuinely don't know P(x-risk), and the asymmetric
payoffs make the robust choice (safety) clearly preferable under maximin.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Examples.PreciseVsImprecise
