import Mettapedia.Logic.PLNFirstOrder.FuzzyITVBridge
import Mettapedia.Logic.PLNIndefiniteTruth

/-!
# Chapter 11 Worked Examples (Canary Theorems)

This module provides theorem-level canaries aligned with the Chapter-11 narrative:

1. A "crooked lottery"-style case where only a minority are near-certain winners.
2. A fuzzy syllogism-style case where composed scores stay in a "many" interval.
3. Explicit non-equivalence witness for the Ch.11 rule-4 shape on an ITV-based path.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open Mettapedia.Logic.PLNIndefiniteTruth

/-- Shared ε=0.1 fixture with AFew-like interval `[0.4,0.6]` and strong `PCL=0.9`. -/
def ch11AFewParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.4
  UPC := 0.6
  PCL := 0.9
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with MANY-like interval `[0.4,0.95]`. -/
def ch11ManyParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.4
  UPC := 0.95
  PCL := 0.4
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- One high-probability witness, one low-probability witness. -/
def oneHighOneLow : Bool → ℝ :=
  fun b => if b then 0.95 else 0.05

/-- Both witnesses high. -/
def bothHigh : Bool → ℝ :=
  fun _ => 0.95

/-- Both witnesses low. -/
def bothLow : Bool → ℝ :=
  fun _ => 0.05

/-- Shared ε=0.1 fixture with MOST-like interval `[0.7,0.9]`. -/
def ch11MostParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.7
  UPC := 0.9
  PCL := 0.7
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with FEW-like interval `[0.1,0.3]`. -/
def ch11FewParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.1
  UPC := 0.3
  PCL := 0.1
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with ALMOST-ALL-like interval `[0.75,1.0]`. -/
def ch11AlmostAllParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.75
  UPC := 1
  PCL := 0.75
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with ABOUT-HALF-like interval `[0.45,0.55]`. -/
def ch11AboutHalfParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.45
  UPC := 0.55
  PCL := 0.45
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with PROBABLY-like interval `[0.66,0.85]`. -/
def ch11ProbablyParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.66
  UPC := 0.85
  PCL := 0.66
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with MAYBE/POSSIBLY-like interval `[0.3,0.7]`. -/
def ch11MaybeParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.3
  UPC := 0.7
  PCL := 0.3
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with ALMOST-NONE-like interval `[0.0,0.2]`. -/
def ch11AlmostNoneParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0
  UPC := 0.2
  PCL := 0
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with MANY-BUT-NOT-MOST interval `[0.4,0.69]`. -/
def ch11ManyNotMostParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.4
  UPC := 0.69
  PCL := 0.4
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Finite fixture with exactly 3 near-one witnesses out of 4. -/
def threeHighOneLow : Fin 4 → ℝ := fun u => if u = 0 then 0.05 else 0.95

/-- Finite fixture with exactly 1 near-one witness out of 4. -/
def oneHighThreeLow : Fin 4 → ℝ := fun u => if u = 0 then 0.95 else 0.05

/-- Finite-5 fixture with exactly 1 near-one witness out of 5. -/
def oneHighFourLowFin5 : Fin 5 → ℝ := fun u => if u = 0 then 0.95 else 0.05

/-- Finite-5 fixture with exactly 3 near-one witnesses out of 5. -/
def threeHighTwoLowFin5 : Fin 5 → ℝ :=
  fun u => if u = 0 ∨ u = 1 ∨ u = 2 then 0.95 else 0.05

/-- Crooked-lottery canary:
`AFew` holds while strict `ForAll` (via `PCL=0.9`) does not. -/
theorem canary_ch11_crookedLottery_afew_not_forall :
    fuzzyIntervalHolds ch11AFewParams oneHighOneLow ∧
      ¬ fuzzyForAllHolds ch11AFewParams oneHighOneLow := by
  have hfrac : nearOneFraction ch11AFewParams oneHighOneLow = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11AFewParams (oneHighOneLow u)) =
          (fun u => u = true) := by
      funext u
      cases u <;> simp [nearOne, oneHighOneLow, ch11AFewParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  constructor
  · unfold fuzzyIntervalHolds
    rw [hfrac]
    norm_num [ch11AFewParams]
  · unfold fuzzyForAllHolds
    rw [hfrac]
    norm_num [ch11AFewParams]

/-- Fuzzy-syllogism canary:
with "many women are beautiful" and "almost all beautiful bring happiness"
encoded as near-one fractions `1/2` and `1`, the composed score remains "many". -/
theorem canary_ch11_fuzzySyllogism_many :
    ch11ManyParams.LPC ≤
        nearOneFraction ch11ManyParams oneHighOneLow *
          nearOneFraction ch11ManyParams bothHigh ∧
      nearOneFraction ch11ManyParams oneHighOneLow *
          nearOneFraction ch11ManyParams bothHigh ≤
        ch11ManyParams.UPC := by
  have hWB : nearOneFraction ch11ManyParams oneHighOneLow = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11ManyParams (oneHighOneLow u)) =
          (fun u => u = true) := by
      funext u
      cases u <;> simp [nearOne, oneHighOneLow, ch11ManyParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  have hBH : nearOneFraction ch11ManyParams bothHigh = (1 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11ManyParams (bothHigh u)) = (fun _ => True) := by
      funext u
      cases u <;> simp [nearOne, bothHigh, ch11ManyParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  rw [hWB, hBH]
  norm_num [ch11ManyParams]

/-- Positive fixture: all-high profile satisfies strict fuzzy `ForAll` under AFew parameters. -/
theorem canary_ch11_allHigh_forall :
    fuzzyForAllHolds ch11AFewParams bothHigh := by
  have hBH : nearOneFraction ch11AFewParams bothHigh = (1 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11AFewParams (bothHigh u)) = (fun _ => True) := by
      funext u
      cases u <;> simp [nearOne, bothHigh, ch11AFewParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  unfold fuzzyForAllHolds
  rw [hBH]
  norm_num [ch11AFewParams]

/-- Negative fixture: all-low profile fails fuzzy `ThereExists` under AFew parameters. -/
theorem canary_ch11_allLow_not_thereExists :
    ¬ fuzzyThereExistsHolds ch11AFewParams bothLow := by
  have hBZ : nearZeroFraction ch11AFewParams bothLow = (1 : ℝ) := by
    have hpred :
        (fun u : Bool => nearZero ch11AFewParams (bothLow u)) = (fun _ => True) := by
      funext u
      cases u <;> simp [nearZero, bothLow, ch11AFewParams] <;> norm_num
    unfold nearZeroFraction
    simp [hpred, witnessFraction, witnessCount]
  unfold fuzzyThereExistsHolds
  rw [hBZ]
  norm_num [ch11AFewParams]

/-- MOST fixture canary: expected near-one fraction is exactly `3/4`. -/
theorem canary_ch11_most_fraction_threeQuarters :
    nearOneFraction ch11MostParams threeHighOneLow = (3 / 4 : ℝ) := by
  have hpred :
      (fun u : Fin 4 => nearOne ch11MostParams (threeHighOneLow u)) = (fun u => u ≠ 0) := by
    funext u
    fin_cases u <;> simp [nearOne, threeHighOneLow, ch11MostParams] <;> norm_num
  unfold nearOneFraction
  simp [hpred, witnessFraction, witnessCount]

/-- FEW fixture canary: expected near-one fraction is exactly `1/4`. -/
theorem canary_ch11_few_fraction_oneQuarter :
    nearOneFraction ch11FewParams oneHighThreeLow = (1 / 4 : ℝ) := by
  have hpred :
      (fun u : Fin 4 => nearOne ch11FewParams (oneHighThreeLow u)) = (fun u => u = 0) := by
    funext u
    fin_cases u <;> simp [nearOne, oneHighThreeLow, ch11FewParams] <;> norm_num
  unfold nearOneFraction
  simp [hpred, witnessFraction, witnessCount]

/-- MOST positive + FEW negative on the same `3/4` fixture. -/
theorem canary_ch11_most_vs_few_split_on_threeQuarters :
    fuzzyIntervalHolds ch11MostParams threeHighOneLow ∧
      ¬ fuzzyIntervalHolds ch11FewParams threeHighOneLow := by
  have hfrac : nearOneFraction ch11MostParams threeHighOneLow = (3 / 4 : ℝ) := by
    exact canary_ch11_most_fraction_threeQuarters
  constructor
  · unfold fuzzyIntervalHolds
    rw [hfrac]
    norm_num [ch11MostParams]
  · unfold fuzzyIntervalHolds
    have hfracFew : nearOneFraction ch11FewParams threeHighOneLow = (3 / 4 : ℝ) := by
      have hpred :
          (fun u : Fin 4 => nearOne ch11FewParams (threeHighOneLow u)) = (fun u => u ≠ 0) := by
        funext u
        fin_cases u <;> simp [nearOne, threeHighOneLow, ch11FewParams] <;> norm_num
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount]
    rw [hfracFew]
    norm_num [ch11FewParams]

/-- ALMOST-ALL fixture canary: expected near-one fraction is exactly `3/4`. -/
theorem canary_ch11_almostAll_fraction_threeQuarters :
    nearOneFraction ch11AlmostAllParams threeHighOneLow = (3 / 4 : ℝ) := by
  have hpred :
      (fun u : Fin 4 => nearOne ch11AlmostAllParams (threeHighOneLow u)) = (fun u => u ≠ 0) := by
    funext u
    fin_cases u <;> simp [nearOne, threeHighOneLow, ch11AlmostAllParams] <;> norm_num
  unfold nearOneFraction
  simp [hpred, witnessFraction, witnessCount]

/-- ALMOST-ALL positive canary on the `3/4` fixture. -/
theorem canary_ch11_almostAll_holds_on_threeQuarters :
    fuzzyIntervalHolds ch11AlmostAllParams threeHighOneLow := by
  unfold fuzzyIntervalHolds
  rw [canary_ch11_almostAll_fraction_threeQuarters]
  norm_num [ch11AlmostAllParams]

/-- ABOUT-HALF fixture canary: expected near-one fraction is exactly `1/2`. -/
theorem canary_ch11_aboutHalf_fraction_oneHalf :
    nearOneFraction ch11AboutHalfParams oneHighOneLow = (1 / 2 : ℝ) := by
  have hpred :
      (fun u : Bool => nearOne ch11AboutHalfParams (oneHighOneLow u)) = (fun u => u = true) := by
    funext u
    cases u <;> simp [nearOne, oneHighOneLow, ch11AboutHalfParams] <;> norm_num
  unfold nearOneFraction
  simp [hpred, witnessFraction, witnessCount]

/-- ABOUT-HALF split canary:
the `1/2` fixture is accepted while an all-high profile is rejected. -/
theorem canary_ch11_aboutHalf_positive_negative_split :
    fuzzyIntervalHolds ch11AboutHalfParams oneHighOneLow ∧
      ¬ fuzzyIntervalHolds ch11AboutHalfParams bothHigh := by
  constructor
  · unfold fuzzyIntervalHolds
    rw [canary_ch11_aboutHalf_fraction_oneHalf]
    norm_num [ch11AboutHalfParams]
  · unfold fuzzyIntervalHolds
    have hAll : nearOneFraction ch11AboutHalfParams bothHigh = (1 : ℝ) := by
      have hpred :
          (fun u : Bool => nearOne ch11AboutHalfParams (bothHigh u)) = (fun _ => True) := by
        funext u
        cases u <;> simp [nearOne, bothHigh, ch11AboutHalfParams] <;> norm_num
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount]
    rw [hAll]
    norm_num [ch11AboutHalfParams]

/-- PROBABLY positive + negative split:
`3/4` is accepted, while `1/2` is rejected. -/
theorem canary_ch11_probably_positive_negative_split :
    fuzzyIntervalHolds ch11ProbablyParams threeHighOneLow ∧
      ¬ fuzzyIntervalHolds ch11ProbablyParams oneHighOneLow := by
  constructor
  · unfold fuzzyIntervalHolds
    have hThreeQuarter : nearOneFraction ch11ProbablyParams threeHighOneLow = (3 / 4 : ℝ) := by
      have hpred :
          (fun u : Fin 4 => nearOne ch11ProbablyParams (threeHighOneLow u)) = (fun u => u ≠ 0) := by
        funext u
        fin_cases u <;> simp [nearOne, threeHighOneLow, ch11ProbablyParams] <;> norm_num
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount]
    rw [hThreeQuarter]
    norm_num [ch11ProbablyParams]
  · unfold fuzzyIntervalHolds
    have hHalf : nearOneFraction ch11ProbablyParams oneHighOneLow = (1 / 2 : ℝ) := by
      have hpred :
          (fun u : Bool => nearOne ch11ProbablyParams (oneHighOneLow u)) = (fun u => u = true) := by
        funext u
        cases u <;> simp [nearOne, oneHighOneLow, ch11ProbablyParams] <;> norm_num
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount]
    rw [hHalf]
    norm_num [ch11ProbablyParams]

/-- MAYBE/POSSIBLY positive + negative split:
`1/2` is accepted, while certainty (`1`) is rejected. -/
theorem canary_ch11_maybe_positive_negative_split :
    fuzzyIntervalHolds ch11MaybeParams oneHighOneLow ∧
      ¬ fuzzyIntervalHolds ch11MaybeParams bothHigh := by
  constructor
  · unfold fuzzyIntervalHolds
    have hHalf : nearOneFraction ch11MaybeParams oneHighOneLow = (1 / 2 : ℝ) := by
      have hpred :
          (fun u : Bool => nearOne ch11MaybeParams (oneHighOneLow u)) = (fun u => u = true) := by
        funext u
        cases u <;> simp [nearOne, oneHighOneLow, ch11MaybeParams] <;> norm_num
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount]
    rw [hHalf]
    norm_num [ch11MaybeParams]
  · unfold fuzzyIntervalHolds
    have hAll : nearOneFraction ch11MaybeParams bothHigh = (1 : ℝ) := by
      have hpred :
          (fun u : Bool => nearOne ch11MaybeParams (bothHigh u)) = (fun _ => True) := by
        funext u
        cases u <;> simp [nearOne, bothHigh, ch11MaybeParams] <;> norm_num
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount]
    rw [hAll]
    norm_num [ch11MaybeParams]

/-- ALMOST-NONE fixture canary: expected near-one fraction is exactly `1/5`. -/
theorem canary_ch11_almostNone_fraction_oneFifth :
    nearOneFraction ch11AlmostNoneParams oneHighFourLowFin5 = (1 / 5 : ℝ) := by
  have hpred :
      (fun u : Fin 5 => nearOne ch11AlmostNoneParams (oneHighFourLowFin5 u)) = (fun u => u = 0) := by
    funext u
    fin_cases u <;> simp [nearOne, oneHighFourLowFin5, ch11AlmostNoneParams] <;> norm_num
  unfold nearOneFraction
  simp [hpred, witnessFraction, witnessCount]

/-- ALMOST-NONE positive canary on the finite-5 `1/5` fixture. -/
theorem canary_ch11_almostNone_holds_on_oneFifth :
    fuzzyIntervalHolds ch11AlmostNoneParams oneHighFourLowFin5 := by
  unfold fuzzyIntervalHolds
  rw [canary_ch11_almostNone_fraction_oneFifth]
  norm_num [ch11AlmostNoneParams]

/-- MANY-BUT-NOT-MOST fixture canary: expected near-one fraction is exactly `3/5`. -/
theorem canary_ch11_manyNotMost_fraction_threeFifths :
    nearOneFraction ch11ManyNotMostParams threeHighTwoLowFin5 = (3 / 5 : ℝ) := by
  have hpred :
      (fun u : Fin 5 => nearOne ch11ManyNotMostParams (threeHighTwoLowFin5 u)) =
        (fun u => u = 0 ∨ u = 1 ∨ u = 2) := by
    funext u
    fin_cases u <;> simp [nearOne, threeHighTwoLowFin5, ch11ManyNotMostParams] <;> norm_num
  have hcount : Fintype.card {u : Fin 5 // u = 0 ∨ u = 1 ∨ u = 2} = 3 := by
    decide
  unfold nearOneFraction
  simp [hpred, witnessFraction, witnessCount, hcount]

/-- MANY-BUT-NOT-MOST split canary:
the `3/5` fixture satisfies many-but-not-most, but not MOST. -/
theorem canary_ch11_manyNotMost_vs_most_split :
    fuzzyIntervalHolds ch11ManyNotMostParams threeHighTwoLowFin5 ∧
      ¬ fuzzyIntervalHolds ch11MostParams threeHighTwoLowFin5 := by
  constructor
  · unfold fuzzyIntervalHolds
    rw [canary_ch11_manyNotMost_fraction_threeFifths]
    norm_num [ch11ManyNotMostParams]
  · unfold fuzzyIntervalHolds
    have hMostFrac : nearOneFraction ch11MostParams threeHighTwoLowFin5 = (3 / 5 : ℝ) := by
      have hpred :
          (fun u : Fin 5 => nearOne ch11MostParams (threeHighTwoLowFin5 u)) =
            (fun u => u = 0 ∨ u = 1 ∨ u = 2) := by
        funext u
        fin_cases u <;> simp [nearOne, threeHighTwoLowFin5, ch11MostParams] <;> norm_num
      have hcount : Fintype.card {u : Fin 5 // u = 0 ∨ u = 1 ∨ u = 2} = 3 := by
        decide
      unfold nearOneFraction
      simp [hpred, witnessFraction, witnessCount, hcount]
    rw [hMostFrac]
    norm_num [ch11MostParams]

/-- ITV fixtures for explicit rule-4 non-equivalence witness. -/
def itvHi : ITV where
  lower := 0.9
  upper := 1
  credibility := 0.8
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

def itvLo : ITV where
  lower := 0
  upper := 0.2
  credibility := 0.8
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

def itvG : ITV where
  lower := 0.55
  upper := 0.65
  credibility := 0.9
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

/-- ε=0.2 makes "near one" mean `x ≥ 0.8`. -/
def ch11Rule4Params : FuzzyQuantifierParams where
  ε := 0.2
  LPC := 0
  UPC := 1
  PCL := 0
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Profile induced by ITV midpoint strengths. -/
noncomputable def rule4Profile : Bool → ℝ :=
  fun b => (if b then itvHi else itvLo).strength

/-- Concrete ITV-valued finite fixture used by coordinate bridge canaries. -/
def rule4ITVProfile : Bool → ITV :=
  fun b => if b then itvHi else itvLo

/-- Ch.11 Rule-4 non-equivalence witness on an ITV-based path:

`∃x (G ∧ F(x))` score is not equal to `G ∧ ∃x F(x)` score under proxy-threshold
aggregation. -/
theorem canary_ch11_rule4_not_equivalent_itvPath :
    fuzzyExistsScore ch11Rule4Params
      (conjoinProfile itvG.strength rule4Profile)
      ≠
    min itvG.strength (fuzzyExistsScore ch11Rule4Params rule4Profile) := by
  have hLeft :
      fuzzyExistsScore ch11Rule4Params (conjoinProfile itvG.strength rule4Profile) = (0 : ℝ) := by
    unfold fuzzyExistsScore nearOneFraction witnessFraction witnessCount nearOne
    unfold conjoinProfile rule4Profile ch11Rule4Params
    norm_num [ITV.strength, itvG, itvHi, itvLo]
  have hScore :
      fuzzyExistsScore ch11Rule4Params rule4Profile = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11Rule4Params (rule4Profile u)) =
          (fun u => u = true) := by
      funext u
      cases u <;>
        simp [nearOne, rule4Profile, ch11Rule4Params, ITV.strength, itvHi, itvLo] <;> norm_num
    unfold fuzzyExistsScore nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  have hRight :
      min itvG.strength (fuzzyExistsScore ch11Rule4Params rule4Profile) = (1 / 2 : ℝ) := by
    rw [hScore]
    norm_num [ITV.strength, itvG]
  rw [hLeft, hRight]
  norm_num

/-- ITV-coordinate bridge canary:
lower/upper fuzzy-interval truth transfers to strength-profile truth. -/
theorem canary_ch11_itv_strength_interval_of_lower_upper :
    fuzzyIntervalHolds ch11ManyParams (itvLowerProfile rule4ITVProfile) ∧
      fuzzyIntervalHolds ch11ManyParams (itvUpperProfile rule4ITVProfile) ∧
      fuzzyIntervalHolds ch11ManyParams (itvStrengthProfile rule4ITVProfile) := by
  have hLowerFrac : nearOneFraction ch11ManyParams (itvLowerProfile rule4ITVProfile) = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11ManyParams ((itvLowerProfile rule4ITVProfile) u)) =
          (fun u => u = true) := by
      funext u
      cases u <;>
        simp [nearOne, itvLowerProfile, rule4ITVProfile, itvHi, itvLo, ch11ManyParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  have hUpperFrac : nearOneFraction ch11ManyParams (itvUpperProfile rule4ITVProfile) = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11ManyParams ((itvUpperProfile rule4ITVProfile) u)) =
          (fun u => u = true) := by
      funext u
      cases u <;>
        simp [nearOne, itvUpperProfile, rule4ITVProfile, itvHi, itvLo, ch11ManyParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  have hLower : fuzzyIntervalHolds ch11ManyParams (itvLowerProfile rule4ITVProfile) := by
    unfold fuzzyIntervalHolds
    rw [hLowerFrac]
    norm_num [ch11ManyParams]
  have hUpper : fuzzyIntervalHolds ch11ManyParams (itvUpperProfile rule4ITVProfile) := by
    unfold fuzzyIntervalHolds
    rw [hUpperFrac]
    norm_num [ch11ManyParams]
  refine ⟨hLower, hUpper, ?_⟩
  exact fuzzyIntervalHolds_strength_of_lower_upper ch11ManyParams rule4ITVProfile hLower hUpper

end Mettapedia.Logic.PLNFirstOrder
