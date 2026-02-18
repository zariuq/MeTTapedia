import Mettapedia.Logic.MarkovDeFinettiHardApprox
import Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
import Mettapedia.Logic.MarkovDeFinettiHardExcursions
import Mettapedia.Logic.MarkovDeFinettiHardBEST

/-!
# Markov de Finetti (Hard Direction) — Good‑state bound (bridge)

This file resolves the import cycle between `HardApprox` and `ExcursionModel` by
importing both.  It proves the Diaconis–Freedman **good‑state bound**: on evidence
states with `M` returns to the start, the per‑state approximation error is `O(1/M)`.

The proof strategy:
1. Each trajectory in the fiber at horizon `N` decomposes into `≈ M` excursions.
2. The prefix coefficient `prefixCoeff` equals the *without‑replacement* probability
   of the first `m` excursions matching a given pattern.
3. `W(empiricalParam s)` equals the *with‑replacement* probability under the same
   excursion empirical distribution.
4. The difference is bounded by `4m²/R` via `abs_excursion_wor_wr_le_take`,
   where `R ≈ M` and `m` depends only on `(k, n)`.

## Lemmas moved here from `HardApprox`

- `good_state_bound`
- `abs_weightedDiffCore_le`
- `weightedDiffCore_tendsto_zero`
- `weightedDiff_tendsto_zero`
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHard

open MeasureTheory

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence
open Mettapedia.Logic.EvidenceDirichlet
open Mettapedia.Logic.MarkovDeFinettiHardExcursions
open Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
open Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacement
open Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacementModel
open Mettapedia.Logic.MarkovDeFinettiHardBEST

variable {k : ℕ}

/--
Explicit semantic-core interface for the hard excursion bridge.

For each state `s` at each horizon `N`, this supplies a semantic package proving
that the classwise WR/WOR discrepancy is controlled by the collision term once
the residual alignment gap (`εW + εPC`) is discharged.
-/
def HasExcursionBiapproxCore
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) : Prop :=
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      ExcursionBiapproxPackage (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s)

/--
Pattern-level surrogate interface: provide a pattern law `q` with WR/WOR residual
bounds and a nonpositive residual gap.
-/
def HasPatternSurrogateAlignment
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) : Prop :=
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      ∃ q : ExcursionList k → ℝ,
        ∃ εW εPC : ℝ,
          (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
            |(wrPatternMass (k := k) hk n e s p).toReal - q p| ≤ εW) ∧
          (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
            |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC) ∧
          εW + εPC ≤ 0

/--
Canonical WR-surrogate interface: control `W` by a scalar surrogate and control the
canonical short-pattern mass against WOR masses.
-/
def HasCanonicalWRSurrogateAlignment
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) : Prop :=
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      ∃ wSurrogate εW εPC : ℝ,
        |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
          wSurrogate| ≤ εW ∧
        (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
            (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC) ∧
        εW + εPC ≤ 0

/--
Pattern-level surrogate interface without forcing a zero total residual.
-/
def HasPatternSurrogateResidualAlignment
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) : Prop :=
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      ∃ q : ExcursionList k → ℝ,
        ∃ εW εPC : ℝ,
          (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
            |(wrPatternMass (k := k) hk n e s p).toReal - q p| ≤ εW) ∧
          (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
            |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC)

/--
Canonical WR-surrogate interface without forcing a zero total residual.
-/
def HasCanonicalWRSurrogateResidualAlignment
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) : Prop :=
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      ∃ wSurrogate εW εPC : ℝ,
        |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
          wSurrogate| ≤ εW ∧
        (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
            (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC)

/--
Statewise decomposition bound with explicit nonnegative residual terms.
-/
def HasExcursionResidualBound
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) : Prop :=
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      ∃ εW εPC : ℝ,
        0 ≤ εW ∧ 0 ≤ εPC ∧
        |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
            - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
          εW + εPC

/--
Rate-bearing residual interface: the WR/WOR mismatch is bounded by
statewise nonnegative residuals whose sum is `O(1 / returnsToStart)`.
-/
def HasExcursionResidualBoundRate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (C : ℝ) : Prop :=
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      0 < returnsToStart (k := k) s →
        ∃ εW εPC : ℝ,
          0 ≤ εW ∧ 0 ≤ εPC ∧
          εW + εPC ≤ C / (returnsToStart (k := k) s : ℝ) ∧
          |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
              - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
            εW + εPC

/--
Pattern-level residual alignment with explicit `O(1 / returnsToStart)` rate.
-/
def HasPatternSurrogateResidualAlignmentRate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (C : ℝ) : Prop :=
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      0 < returnsToStart (k := k) s →
        ∃ q : ExcursionList k → ℝ,
          ∃ εW εPC : ℝ,
            (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
              |(wrPatternMass (k := k) hk n e s p).toReal - q p| ≤ εW) ∧
            (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
              |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC) ∧
            εW + εPC ≤ C / (returnsToStart (k := k) s : ℝ)

/--
Canonical WR-surrogate residual alignment with explicit `O(1 / returnsToStart)` rate.
-/
def HasCanonicalWRSurrogateResidualAlignmentRate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (C : ℝ) : Prop :=
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      0 < returnsToStart (k := k) s →
        ∃ wSurrogate εW εPC : ℝ,
          |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
            wSurrogate| ≤ εW ∧
          (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
            |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
              (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC) ∧
          εW + εPC ≤ C / (returnsToStart (k := k) s : ℝ)


/--
WR-side smoothing residual rate:
for each state, there is a scalar surrogate with error at most `Cw / R`.
-/
def HasCanonicalWRSmoothingRate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ) : Prop :=
  ∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      0 < returnsToStart (k := k) s →
        ∃ wSurrogate εW : ℝ,
          |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
            wSurrogate| ≤ εW ∧
          εW ≤ Cw / (returnsToStart (k := k) s : ℝ)

/--
WOR-side transport residual rate relative to a chosen WR scalar surrogate.
-/
def HasCanonicalWORTransportRate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw Cpc : ℝ) : Prop :=
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      0 < returnsToStart (k := k) s →
        ∀ wSurrogate : ℝ,
          |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
            wSurrogate| ≤ Cw / (returnsToStart (k := k) s : ℝ) →
            ∃ εPC : ℝ,
              (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
                |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
                  (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC) ∧
              εPC ≤ Cpc / (returnsToStart (k := k) s : ℝ)

/--
Direct WR/WOR pattern discrepancy rate:
for each state, the summed pattern-mass gap is bounded by `Cdf / returnsToStart`.
-/
def HasPatternWRWORRate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cdf : ℝ) : Prop :=
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      0 < returnsToStart (k := k) s →
        (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
          Cdf / (returnsToStart (k := k) s : ℝ)

/-- Two-regime constructor for direct WR/WOR pattern rates.

- Small-`R` branch (`returnsToStart ≤ R0`): uses the coarse universal bound
  `sum_abs_wr_wor_patternMass_toReal_le_two`.
- Large-`R` branch (`R0 < returnsToStart`): supplied by a problem-specific
  asymptotic bound `hlarge`.

This isolates the remaining math to proving only the large-`R` estimate. -/
theorem hasPatternWRWORRate_of_smallR_largeR
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (R0 : ℕ) (Clarge : ℝ)
    (hlarge :
      ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
        s ∈ stateFinset k N →
          0 < returnsToStart (k := k) s →
          R0 < returnsToStart (k := k) s →
            (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
              |(wrPatternMass (k := k) hk n e s p).toReal -
                (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
              Clarge / (returnsToStart (k := k) s : ℝ)) :
    HasPatternWRWORRate (k := k) hk n e (max (2 * (R0 : ℝ)) Clarge) := by
  intro N hN s hs hRpos
  let R : ℕ := returnsToStart (k := k) s
  by_cases hsmall : R ≤ R0
  · have hcoarse :
      (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤ 2 :=
      sum_abs_wr_wor_patternMass_toReal_le_two
        (k := k) (hk := hk) (hN := hN) (e := e) (s := s) hs
    have hRreal : (0 : ℝ) < (R : ℝ) := by
      exact_mod_cast hRpos
    have hsmall_real : (R : ℝ) ≤ (R0 : ℝ) := by
      exact_mod_cast hsmall
    have htwo_le :
        (2 : ℝ) ≤ (2 * (R0 : ℝ)) / (R : ℝ) := by
      rw [le_div_iff₀ hRreal]
      nlinarith
    have hdiv_le :
        (2 * (R0 : ℝ)) / (R : ℝ) ≤
          (max (2 * (R0 : ℝ)) Clarge) / (R : ℝ) := by
      exact
        div_le_div_of_nonneg_right
          (le_max_left (2 * (R0 : ℝ)) Clarge)
          (by exact_mod_cast (Nat.zero_le R))
    calc
      (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤ 2 := hcoarse
      _ ≤ (2 * (R0 : ℝ)) / (R : ℝ) := htwo_le
      _ ≤ (max (2 * (R0 : ℝ)) Clarge) / (R : ℝ) := hdiv_le
      _ = (max (2 * (R0 : ℝ)) Clarge) / (returnsToStart (k := k) s : ℝ) := by
          simp [R]
  · have hRlarge : R0 < returnsToStart (k := k) s := by
      exact Nat.lt_of_not_ge hsmall
    have hlarge_bound :
        (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
          Clarge / (returnsToStart (k := k) s : ℝ) :=
      hlarge hN s hs hRpos hRlarge
    have hdiv_le :
        Clarge / (returnsToStart (k := k) s : ℝ) ≤
          (max (2 * (R0 : ℝ)) Clarge) / (returnsToStart (k := k) s : ℝ) := by
      exact
        div_le_div_of_nonneg_right
          (le_max_right (2 * (R0 : ℝ)) Clarge)
          (by exact_mod_cast (Nat.zero_le (returnsToStart (k := k) s)))
    exact le_trans hlarge_bound hdiv_le

/-- Legacy (collision-only) family-level positive-return pattern obligation.
Use `HasPatternWRWORRate` / split-rate constructors instead. -/
def HasPatternCollisionPosAll : Prop :=
  ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
    ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
      s ∈ stateFinset k N →
        0 < returnsToStart (k := k) s →
          (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
            |(wrPatternMass (k := k) hk n e s p).toReal -
              (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
            (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
              (returnsToStart (k := k) s : ℝ)

/-- Legacy (collision-only) family-level zero-return pattern discrepancy obligation.
Use `HasPatternWRWORRate` route instead. -/
def HasPatternCollisionZeroAll : Prop :=
  ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
    ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
      s ∈ stateFinset k N →
        returnsToStart (k := k) s = 0 →
          (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
            |(wrPatternMass (k := k) hk n e s p).toReal -
              (worPatternMass (k := k) (hN := hN) e s p).toReal|) = 0

private lemma fiber_eq_empty_of_not_mem_stateFinset
    {n : ℕ} (e : MarkovState k)
    (he : e ∉ stateFinset k n) :
    fiber k n e = ∅ := by
  ext xs
  constructor
  · intro hxs
    have hxstate : stateOfTraj (k := k) xs = e := (Finset.mem_filter.1 hxs).2
    have hxmem : stateOfTraj (k := k) xs ∈ stateFinset k n :=
      stateOfTraj_mem_stateFinset (k := k) xs
    exact (he (by simpa [hxstate] using hxmem)).elim
  · intro h
    simp at h

/-- If `e` is not realizable at short horizon `Nat.succ n`, then the pattern
index set is empty and the direct WR/WOR pattern discrepancy rate is `0`. -/
theorem hasPatternWRWORRate_zero_of_not_mem_shortStateFinset
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (he : e ∉ stateFinset k (Nat.succ n)) :
    HasPatternWRWORRate (k := k) hk n e 0 := by
  intro N hN s hs hRpos
  have hfiber_empty :
      fiber k (Nat.succ n) e = ∅ :=
    fiber_eq_empty_of_not_mem_stateFinset (k := k) (n := Nat.succ n) e he
  have hPempty :
      excursionPatternSet (k := k) (hN := hN) e s = ∅ := by
    rw [excursionPatternSet_eq_shortImage (k := k) (hN := hN) (e := e) (s := s)]
    simp [hfiber_empty]
  simp [hPempty]

/-- Non-assumptive family constructor on the unrealizable short-state branch:
if `e ∉ stateFinset k (n+1)`, then the direct WR/WOR pattern discrepancy rate
holds with constant `Cdf = 0`. -/
theorem hasPatternWRWORRate_family_unrealizable_shortState
    (hk : 0 < k) (n : ℕ) :
    ∀ e : MarkovState k,
      e ∉ stateFinset k (Nat.succ n) →
        ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf := by
  intro e he
  refine ⟨0, le_rfl, ?_⟩
  exact
    hasPatternWRWORRate_zero_of_not_mem_shortStateFinset
      (k := k) (hk := hk) (n := n) (e := e) he

namespace FixedPatternWRWORRateWitness

abbrev kFix : ℕ := 2
abbrev nFix : ℕ := 1
lemma hkFix : 0 < kFix := by decide

/-- Concrete non-realizable short-horizon state for `k=2`, `n=1`:
all transition counts are zero at horizon `Nat.succ nFix = 2`. -/
def eImpossible : MarkovState kFix := ⟨0, (0 : TransCounts kFix), 0⟩

lemma eImpossible_not_mem_stateFinset :
    eImpossible ∉ stateFinset kFix (Nat.succ nFix) := by
  native_decide

/-- Concrete non-assumptive BEST-side witness (fixed `hk,n,e`):
the pattern discrepancy bound holds with constant `Cdf = 0`. -/
theorem hasPatternWRWORRate_fixed :
    HasPatternWRWORRate (k := kFix) hkFix nFix eImpossible 0 := by
  exact
    hasPatternWRWORRate_zero_of_not_mem_shortStateFinset
      (k := kFix) (hk := hkFix) (n := nFix) (e := eImpossible)
      eImpossible_not_mem_stateFinset

/-- Concrete non-assumptive fixed witness exported at namespace level. -/
theorem hasPatternWRWORRate_fixed_witness :
    ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := kFix) hkFix nFix eImpossible Cdf := by
  refine ⟨0, le_rfl, ?_⟩
  exact hasPatternWRWORRate_fixed

end FixedPatternWRWORRateWitness

/-- BEST-side representative-multiset bound for fixed `(hk,n,e)`. -/
def HasBestReprBound
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) : Prop :=
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      let P := excursionPatternSet (k := k) (hN := hN) e s
      let repr : Multiset (ExcursionType k) → ExcursionList k := fun mset =>
        if hm : ∃ p ∈ P, Multiset.ofList p = mset then (Classical.choose hm) else []
      (∑ mset ∈ P.image Multiset.ofList,
        (((P.filter (fun p => Multiset.ofList p = mset)).card : ℝ) *
          |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
            (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal|))
        ≤
          (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
            (returnsToStart (k := k) s : ℝ)

/-- BEST-side representative-multiset bound family used to build the strict
core package. -/
def HasBestReprBoundAll : Prop :=
  ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
    ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
      s ∈ stateFinset k N →
        let P := excursionPatternSet (k := k) (hN := hN) e s
        let repr : Multiset (ExcursionType k) → ExcursionList k := fun mset =>
          if hm : ∃ p ∈ P, Multiset.ofList p = mset then (Classical.choose hm) else []
        (∑ mset ∈ P.image Multiset.ofList,
          (((P.filter (fun p => Multiset.ofList p = mset)).card : ℝ) *
            |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
              (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal|))
          ≤
            (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
              (returnsToStart (k := k) s : ℝ)

/-- If `e` is not realizable at short horizon `Nat.succ n`, then the BEST
representative bound is trivial (empty pattern index set). -/
theorem hasBestReprBound_zero_of_not_mem_shortStateFinset
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (he : e ∉ stateFinset k (Nat.succ n)) :
    HasBestReprBound (k := k) hk n e := by
  intro N hN s hs
  have hfiber_empty :
      fiber k (Nat.succ n) e = ∅ :=
    fiber_eq_empty_of_not_mem_stateFinset (k := k) (n := Nat.succ n) e he
  have hPempty :
      excursionPatternSet (k := k) (hN := hN) e s = ∅ := by
    rw [excursionPatternSet_eq_shortImage (k := k) (hN := hN) (e := e) (s := s)]
    simp [hfiber_empty]
  have hrhs_nonneg :
      0 ≤
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
    have hnum_nonneg :
        0 ≤ (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) := by positivity
    have hden_nonneg : 0 ≤ (returnsToStart (k := k) s : ℝ) := by
      exact_mod_cast (Nat.zero_le (returnsToStart (k := k) s))
    exact div_nonneg hnum_nonneg hden_nonneg
  simpa [hPempty] using hrhs_nonneg

/-- To prove `HasBestReprBoundAll`, it suffices to prove `HasBestReprBound` on
realizable short states `e ∈ stateFinset k (n+1)`. Unrealizable short states
are discharged by `hasBestReprBound_zero_of_not_mem_shortStateFinset`. -/
theorem hasBestReprBoundAll_of_realizable_shortState
    (hrealBest :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          HasBestReprBound (k := k) hk n e) :
    HasBestReprBoundAll (k := k) := by
  intro hk n e
  by_cases he : e ∈ stateFinset k (Nat.succ n)
  · exact hrealBest hk n e he
  · exact
      hasBestReprBound_zero_of_not_mem_shortStateFinset
        (k := k) (hk := hk) (n := n) (e := e) he

/--
Statewise WR representation-rate witness via a concrete long-fiber trajectory family.

This is the constructive witness shape consumed by
`hasCanonicalWRSmoothingRate_of_fiber_trajectory_family`.
-/
def HasFiberTrajectoryWRReprRate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ) : Prop :=
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      0 < returnsToStart (k := k) s →
        ∃ xs : Traj k N, xs ∈ fiber k N s ∧
          |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
            excursionWithReplacementProb (k := k)
              (excursionListOfTraj (k := k) xs)
              ((excursionListOfTraj (k := k) xs).take
                (prefixExcursionCount (k := k) hN xs))| ≤
            Cw / (returnsToStart (k := k) s : ℝ)

/--
Scalar WR crux shape: statewise `O(1 / returnsToStart)` closeness of
`W(empiricalParam)` to `W(empiricalParamStartTarget)`.
-/
def HasStatewiseStartTargetWClose
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ) : Prop :=
  ∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      0 < returnsToStart (k := k) s →
        |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
          (W (k := k) (Nat.succ n) e (empiricalParamStartTarget (k := k) hk s)).toReal| ≤
            Cw / (returnsToStart (k := k) s : ℝ)

/-- Expand `W.toReal` into a finite real-valued sum over the evidence fiber. -/
private lemma W_toReal_eq_sum_wordProb_toReal
    (n : ℕ) (e : MarkovState k) (θ : MarkovParam k) :
    (W (k := k) n e θ).toReal =
      ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
        (wordProb (k := k) θ (trajToList (k := k) xs)).toReal := by
  classical
  unfold W
  refine ENNReal.toReal_sum ?_
  intro xs hx
  simp [wordProb]

/-- `W.toReal` expansion specialized to `empiricalParam`. -/
private lemma W_toReal_eq_sum_wordProb_toReal_empiricalParam
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) :
    (W (k := k) n e (empiricalParam (k := k) hk s)).toReal =
      ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
        (wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) xs)).toReal := by
  simpa using
    (W_toReal_eq_sum_wordProb_toReal (k := k) (n := n) (e := e)
      (θ := empiricalParam (k := k) hk s))

/-- `W.toReal` expansion specialized to `empiricalParamStartTarget`. -/
private lemma W_toReal_eq_sum_wordProb_toReal_empiricalParamStartTarget
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) :
    (W (k := k) n e (empiricalParamStartTarget (k := k) hk s)).toReal =
      ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
        (wordProb (k := k) (empiricalParamStartTarget (k := k) hk s)
          (trajToList (k := k) xs)).toReal := by
  simpa using
    (W_toReal_eq_sum_wordProb_toReal (k := k) (n := n) (e := e)
      (θ := empiricalParamStartTarget (k := k) hk s))

/-- Transition probability masses are in `[0, 1]` after casting to `ℝ`. -/
private lemma stepProb_toReal_nonneg (θ : MarkovParam k) (a b : Fin k) :
    0 ≤ (stepProb (k := k) θ a b : ℝ) := by
  positivity

/-- Transition probability masses are in `[0, 1]` after casting to `ℝ`. -/
private lemma stepProb_toReal_le_one (θ : MarkovParam k) (a b : Fin k) :
    (stepProb (k := k) θ a b : ℝ) ≤ 1 := by
  have hmonoENN : ((stepProb (k := k) θ a b : ENNReal) ≤ (1 : ENNReal)) := by
    unfold stepProb
    have hsubset : (Set.singleton b : Set (Fin k)) ⊆ Set.univ := by
      intro x hx
      simp
    have hle :
        ((θ.trans a : MeasureTheory.Measure (Fin k)) (Set.singleton b)) ≤
          ((θ.trans a : MeasureTheory.Measure (Fin k)) Set.univ) :=
      MeasureTheory.measure_mono hsubset
    simpa using hle
  exact_mod_cast hmonoENN

/-- Finite singleton partition of a probability measure sums to `1`. -/
private lemma sum_singleton_eq_one (μ0 : MeasureTheory.ProbabilityMeasure (Fin k)) :
    (∑ a : Fin k, μ0 (Set.singleton a)) = 1 := by
  classical
  let μ : Measure (Fin k) := (μ0 : Measure (Fin k))
  have hsum0 :
      (∑ a ∈ (Finset.univ : Finset (Fin k)), μ (Set.singleton a)) =
        μ (Finset.univ : Finset (Fin k)) :=
    (MeasureTheory.sum_measure_singleton (μ := μ) (s := (Finset.univ : Finset (Fin k))))
  have hsum :
      (∑ a : Fin k, μ (Set.singleton a)) = μ Set.univ := by
    simpa [μ, Finset.coe_univ] using hsum0
  have hμuniv : μ Set.univ = 1 := by
    simp [μ]
  have hsum1 : (∑ a : Fin k, μ (Set.singleton a)) = (1 : ENNReal) := by
    simpa [hμuniv] using hsum
  have hf :
      ∀ a ∈ (Finset.univ : Finset (Fin k)), μ (Set.singleton a) ≠ (⊤ : ENNReal) := by
    intro a ha
    simp [μ]
  have htoNN :
      ENNReal.toNNReal (∑ a : Fin k, μ (Set.singleton a)) =
        ∑ a : Fin k, ENNReal.toNNReal (μ (Set.singleton a)) := by
    simpa using
      (ENNReal.toNNReal_sum (s := (Finset.univ : Finset (Fin k)))
        (f := fun a : Fin k => μ (Set.singleton a)) hf)
  have hpm :
      (∑ a : Fin k, μ0 (Set.singleton a)) =
        ∑ a : Fin k, ENNReal.toNNReal (μ (Set.singleton a)) := by
    simp [MeasureTheory.ProbabilityMeasure.coeFn_def, μ]
  calc
    (∑ a : Fin k, μ0 (Set.singleton a))
        = ∑ a : Fin k, ENNReal.toNNReal (μ (Set.singleton a)) := hpm
    _ = ENNReal.toNNReal (∑ a : Fin k, μ (Set.singleton a)) := by
          exact htoNN.symm
    _ = ENNReal.toNNReal (1 : ENNReal) := by
          simp [hsum1]
    _ = 1 := by simp

/-- Transition rows sum to one after casting to `ℝ`. -/
private lemma sum_stepProb_toReal_eq_one (θ : MarkovParam k) (prev : Fin k) :
    (∑ next : Fin k, (stepProb (k := k) θ prev next : ℝ)) = 1 := by
  have hnn : (∑ next : Fin k, stepProb (k := k) θ prev next) = 1 := by
    simpa [stepProb] using sum_singleton_eq_one (k := k) (μ0 := θ.trans prev)
  exact_mod_cast hnn

/-- Initial masses are in `[0, 1]` after casting to `ℝ`. -/
private lemma initProb_toReal_nonneg (θ : MarkovParam k) (a : Fin k) :
    0 ≤ (initProb (k := k) θ a : ℝ) := by
  positivity

/-- Initial masses are in `[0, 1]` after casting to `ℝ`. -/
private lemma initProb_toReal_le_one (θ : MarkovParam k) (a : Fin k) :
    (initProb (k := k) θ a : ℝ) ≤ 1 := by
  have hmonoENN : ((initProb (k := k) θ a : ENNReal) ≤ (1 : ENNReal)) := by
    unfold initProb
    have hsubset : (Set.singleton a : Set (Fin k)) ⊆ Set.univ := by
      intro x hx
      simp
    have hle :
        ((θ.init : MeasureTheory.Measure (Fin k)) (Set.singleton a)) ≤
          ((θ.init : MeasureTheory.Measure (Fin k)) Set.univ) :=
      MeasureTheory.measure_mono hsubset
    simpa using hle
  exact_mod_cast hmonoENN

/-- Tail Markov word-probability factors are nonnegative after casting to `ℝ`. -/
private lemma wordProbAux_toReal_nonneg (θ : MarkovParam k) (prev : Fin k) :
    ∀ xs : List (Fin k), 0 ≤ (wordProbAux (k := k) θ prev xs : ℝ) := by
  intro xs
  induction xs generalizing prev with
  | nil =>
      simp [wordProbAux]
  | cons b xs ih =>
      have hstep_nonneg : 0 ≤ (stepProb (k := k) θ prev b : ℝ) :=
        stepProb_toReal_nonneg (k := k) θ prev b
      have htail_nonneg : 0 ≤ (wordProbAux (k := k) θ b xs : ℝ) := ih (prev := b)
      simpa [wordProbAux] using mul_nonneg hstep_nonneg htail_nonneg

/-- Tail Markov word-probability factors are at most `1` after casting to `ℝ`. -/
private lemma wordProbAux_toReal_le_one (θ : MarkovParam k) (prev : Fin k) :
    ∀ xs : List (Fin k), (wordProbAux (k := k) θ prev xs : ℝ) ≤ 1 := by
  intro xs
  induction xs generalizing prev with
  | nil =>
      simp [wordProbAux]
  | cons b xs ih =>
      have hstep_nonneg : 0 ≤ (stepProb (k := k) θ prev b : ℝ) :=
        stepProb_toReal_nonneg (k := k) θ prev b
      have hstep_le : (stepProb (k := k) θ prev b : ℝ) ≤ 1 :=
        stepProb_toReal_le_one (k := k) θ prev b
      have htail_nonneg : 0 ≤ (wordProbAux (k := k) θ b xs : ℝ) :=
        wordProbAux_toReal_nonneg (k := k) θ b xs
      have htail_le : (wordProbAux (k := k) θ b xs : ℝ) ≤ 1 := ih (prev := b)
      have hmul_le_one :
          (stepProb (k := k) θ prev b : ℝ) *
            (wordProbAux (k := k) θ b xs : ℝ) ≤ 1 := by
        nlinarith
      simpa [wordProbAux] using hmul_le_one

/-- Pointwise step discrepancy between `empiricalParam` and `empiricalParamStartTarget`.
Outside the start row this is exactly `0`; at the start row it is `O(k / R)`. -/
private lemma abs_stepProb_empiricalParam_sub_startTarget_any_le_k_div_returnsToStart
    (hk : 0 < k) {N : ℕ} {s : MarkovState k}
    (hs : s ∈ stateFinset k N)
    (hRpos : 0 < returnsToStart (k := k) s)
    (prev next : Fin k) :
    |(stepProb (k := k) (empiricalParam (k := k) hk s) prev next : ℝ) -
        (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) prev next : ℝ)| ≤
      (k : ℝ) / (returnsToStart (k := k) s : ℝ) := by
  by_cases hprev : prev = s.start
  · subst hprev
    simpa using
      (abs_stepProb_empiricalParam_sub_startTarget_le_k_div_returnsToStart
        (k := k) (hk := hk) (s := s) (hs := hs) (hRpos := hRpos) (next := next))
  · have hstepEq :
        (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) prev next : ℝ) =
          empiricalStepProb (k := k) hk s.counts prev next := by
      have h :=
        stepProb_empiricalParamStartTarget (k := k) (hk := hk) (s := s) (a := prev) (b := next)
      simp [hprev, empiricalStepProb] at h
      exact h
    have hempEq :
        (stepProb (k := k) (empiricalParam (k := k) hk s) prev next : ℝ) =
          empiricalStepProb (k := k) hk s.counts prev next := by
      simpa using
        (stepProb_empiricalParam (k := k) (hk := hk) (s := s) (a := prev) (b := next))
    have heq :
        (stepProb (k := k) (empiricalParam (k := k) hk s) prev next : ℝ) =
          (stepProb (k := k) (empiricalParamStartTarget (k := k) hk s) prev next : ℝ) := by
      simpa [hstepEq] using hempEq
    have hbound_nonneg :
        0 ≤ (k : ℝ) / (returnsToStart (k := k) s : ℝ) := by
      have hk_nonneg : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
      have hR_nonneg : 0 ≤ (returnsToStart (k := k) s : ℝ) := by
        exact_mod_cast (Nat.zero_le (returnsToStart (k := k) s))
      exact div_nonneg hk_nonneg hR_nonneg
    simpa [heq] using hbound_nonneg

/-- Trajectory-level auxiliary recursion bound:
per-step discrepancy `O(k / R)` lifts linearly in list length. -/
private lemma abs_wordProbAux_empiricalParam_sub_startTarget_le_length_mul
    (hk : 0 < k) {N : ℕ} {s : MarkovState k}
    (hs : s ∈ stateFinset k N)
    (hRpos : 0 < returnsToStart (k := k) s) :
    ∀ prev : Fin k, ∀ xs : List (Fin k),
      |(wordProbAux (k := k) (empiricalParam (k := k) hk s) prev xs : ℝ) -
          (wordProbAux (k := k) (empiricalParamStartTarget (k := k) hk s) prev xs : ℝ)| ≤
        (xs.length : ℝ) * ((k : ℝ) / (returnsToStart (k := k) s : ℝ)) := by
  intro prev xs
  induction xs generalizing prev with
  | nil =>
      simp [wordProbAux]
  | cons b xs ih =>
      let θ₁ : MarkovParam k := empiricalParam (k := k) hk s
      let θ₂ : MarkovParam k := empiricalParamStartTarget (k := k) hk s
      let ε : ℝ := (k : ℝ) / (returnsToStart (k := k) s : ℝ)
      have hstep :
          |(stepProb (k := k) θ₁ prev b : ℝ) -
              (stepProb (k := k) θ₂ prev b : ℝ)| ≤ ε := by
        simpa [θ₁, θ₂, ε] using
          (abs_stepProb_empiricalParam_sub_startTarget_any_le_k_div_returnsToStart
            (k := k) (hk := hk) (s := s) (hs := hs) (hRpos := hRpos) (prev := prev) (next := b))
      have htail :
          |(wordProbAux (k := k) θ₁ b xs : ℝ) -
              (wordProbAux (k := k) θ₂ b xs : ℝ)| ≤ (xs.length : ℝ) * ε := by
        simpa [θ₁, θ₂, ε] using ih (prev := b)
      have haux1_nonneg : 0 ≤ (wordProbAux (k := k) θ₁ b xs : ℝ) :=
        wordProbAux_toReal_nonneg (k := k) θ₁ b xs
      have haux1_le_one : (wordProbAux (k := k) θ₁ b xs : ℝ) ≤ 1 :=
        wordProbAux_toReal_le_one (k := k) θ₁ b xs
      have hstep2_nonneg : 0 ≤ (stepProb (k := k) θ₂ prev b : ℝ) :=
        stepProb_toReal_nonneg (k := k) θ₂ prev b
      have hstep2_le_one : (stepProb (k := k) θ₂ prev b : ℝ) ≤ 1 :=
        stepProb_toReal_le_one (k := k) θ₂ prev b
      have htri :
          |(stepProb (k := k) θ₁ prev b : ℝ) * (wordProbAux (k := k) θ₁ b xs : ℝ) -
              (stepProb (k := k) θ₂ prev b : ℝ) * (wordProbAux (k := k) θ₂ b xs : ℝ)| ≤
            |(stepProb (k := k) θ₁ prev b : ℝ) * (wordProbAux (k := k) θ₁ b xs : ℝ) -
              (stepProb (k := k) θ₂ prev b : ℝ) * (wordProbAux (k := k) θ₁ b xs : ℝ)| +
            |(stepProb (k := k) θ₂ prev b : ℝ) * (wordProbAux (k := k) θ₁ b xs : ℝ) -
              (stepProb (k := k) θ₂ prev b : ℝ) * (wordProbAux (k := k) θ₂ b xs : ℝ)| := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (abs_sub_le
            ((stepProb (k := k) θ₁ prev b : ℝ) * (wordProbAux (k := k) θ₁ b xs : ℝ))
            ((stepProb (k := k) θ₂ prev b : ℝ) * (wordProbAux (k := k) θ₁ b xs : ℝ))
            ((stepProb (k := k) θ₂ prev b : ℝ) * (wordProbAux (k := k) θ₂ b xs : ℝ)))
      have hfirst :
          |(stepProb (k := k) θ₁ prev b : ℝ) * (wordProbAux (k := k) θ₁ b xs : ℝ) -
              (stepProb (k := k) θ₂ prev b : ℝ) * (wordProbAux (k := k) θ₁ b xs : ℝ)| ≤ ε := by
        calc
          |(stepProb (k := k) θ₁ prev b : ℝ) * (wordProbAux (k := k) θ₁ b xs : ℝ) -
              (stepProb (k := k) θ₂ prev b : ℝ) * (wordProbAux (k := k) θ₁ b xs : ℝ)|
              = |((stepProb (k := k) θ₁ prev b : ℝ) -
                    (stepProb (k := k) θ₂ prev b : ℝ)) *
                  (wordProbAux (k := k) θ₁ b xs : ℝ)| := by ring_nf
          _ = |((stepProb (k := k) θ₁ prev b : ℝ) -
                  (stepProb (k := k) θ₂ prev b : ℝ))| *
                |(wordProbAux (k := k) θ₁ b xs : ℝ)| := by rw [abs_mul]
          _ = |((stepProb (k := k) θ₁ prev b : ℝ) -
                  (stepProb (k := k) θ₂ prev b : ℝ))| *
                (wordProbAux (k := k) θ₁ b xs : ℝ) := by
                  rw [abs_of_nonneg haux1_nonneg]
          _ ≤ ε * 1 := by gcongr
          _ = ε := by ring
      have hsecond :
          |(stepProb (k := k) θ₂ prev b : ℝ) * (wordProbAux (k := k) θ₁ b xs : ℝ) -
              (stepProb (k := k) θ₂ prev b : ℝ) * (wordProbAux (k := k) θ₂ b xs : ℝ)| ≤
            (xs.length : ℝ) * ε := by
        calc
          |(stepProb (k := k) θ₂ prev b : ℝ) * (wordProbAux (k := k) θ₁ b xs : ℝ) -
              (stepProb (k := k) θ₂ prev b : ℝ) * (wordProbAux (k := k) θ₂ b xs : ℝ)|
              = |(stepProb (k := k) θ₂ prev b : ℝ) *
                  ((wordProbAux (k := k) θ₁ b xs : ℝ) -
                    (wordProbAux (k := k) θ₂ b xs : ℝ))| := by ring_nf
          _ = |(stepProb (k := k) θ₂ prev b : ℝ)| *
                |(wordProbAux (k := k) θ₁ b xs : ℝ) -
                  (wordProbAux (k := k) θ₂ b xs : ℝ)| := by rw [abs_mul]
          _ = (stepProb (k := k) θ₂ prev b : ℝ) *
                |(wordProbAux (k := k) θ₁ b xs : ℝ) -
                  (wordProbAux (k := k) θ₂ b xs : ℝ)| := by
                  rw [abs_of_nonneg hstep2_nonneg]
          _ ≤ 1 * ((xs.length : ℝ) * ε) := by gcongr
          _ = (xs.length : ℝ) * ε := by ring
      have hsum :
          |(stepProb (k := k) θ₁ prev b : ℝ) * (wordProbAux (k := k) θ₁ b xs : ℝ) -
              (stepProb (k := k) θ₂ prev b : ℝ) * (wordProbAux (k := k) θ₂ b xs : ℝ)| ≤
            ε + (xs.length : ℝ) * ε := by
        linarith [htri, hfirst, hsecond]
      have hlen : ε + (xs.length : ℝ) * ε = ((List.length (b :: xs) : ℕ) : ℝ) * ε := by
        calc
          ε + (xs.length : ℝ) * ε = ((xs.length : ℝ) + 1) * ε := by ring
          _ = ((xs.length + 1 : ℕ) : ℝ) * ε := by norm_num
          _ = ((List.length (b :: xs) : ℕ) : ℝ) * ε := by simp
      simpa [wordProbAux, θ₁, θ₂, ε, hlen] using hsum

/-- Pathwise `wordProb` discrepancy at horizon `m` from the start-target perturbation. -/
private lemma abs_wordProb_toReal_empiricalParam_sub_startTarget_of_traj
    (hk : 0 < k) {N : ℕ} {s : MarkovState k}
    (hs : s ∈ stateFinset k N)
    (hRpos : 0 < returnsToStart (k := k) s)
    {m : ℕ} (xs : Traj k m) :
    |(wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) xs)).toReal -
        (wordProb (k := k) (empiricalParamStartTarget (k := k) hk s) (trajToList (k := k) xs)).toReal| ≤
      (m : ℝ) * ((k : ℝ) / (returnsToStart (k := k) s : ℝ)) := by
  let θ₁ : MarkovParam k := empiricalParam (k := k) hk s
  let θ₂ : MarkovParam k := empiricalParamStartTarget (k := k) hk s
  let tail : List (Fin k) := List.ofFn (fun i : Fin m => xs i.succ)
  have htail :
      |(wordProbAux (k := k) θ₁ (xs 0) tail : ℝ) -
          (wordProbAux (k := k) θ₂ (xs 0) tail : ℝ)| ≤
        (tail.length : ℝ) * ((k : ℝ) / (returnsToStart (k := k) s : ℝ)) := by
    simpa [tail, θ₁, θ₂] using
      (abs_wordProbAux_empiricalParam_sub_startTarget_le_length_mul
        (k := k) (hk := hk) (s := s) (hs := hs) (hRpos := hRpos) (prev := xs 0) (xs := tail))
  have htail_len : tail.length = m := by
    simp [tail]
  have hinit_eq :
      (initProb (k := k) θ₁ (xs 0) : ℝ) = (initProb (k := k) θ₂ (xs 0) : ℝ) := by
    simp [θ₁, θ₂, initProb, empiricalParamStartTarget, empiricalParam]
  have hinit_nonneg : 0 ≤ (initProb (k := k) θ₂ (xs 0) : ℝ) :=
    initProb_toReal_nonneg (k := k) θ₂ (xs 0)
  have hinit_le_one : (initProb (k := k) θ₂ (xs 0) : ℝ) ≤ 1 :=
    initProb_toReal_le_one (k := k) θ₂ (xs 0)
  calc
    |(wordProb (k := k) θ₁ (trajToList (k := k) xs)).toReal -
        (wordProb (k := k) θ₂ (trajToList (k := k) xs)).toReal|
        = |(initProb (k := k) θ₁ (xs 0) : ℝ) * (wordProbAux (k := k) θ₁ (xs 0) tail : ℝ) -
            (initProb (k := k) θ₂ (xs 0) : ℝ) * (wordProbAux (k := k) θ₂ (xs 0) tail : ℝ)| := by
              simp [wordProb, wordProbNN, trajToList, List.ofFn_succ, tail]
    _ = |(initProb (k := k) θ₂ (xs 0) : ℝ) *
          ((wordProbAux (k := k) θ₁ (xs 0) tail : ℝ) -
            (wordProbAux (k := k) θ₂ (xs 0) tail : ℝ))| := by
              rw [hinit_eq]
              ring_nf
    _ = |(initProb (k := k) θ₂ (xs 0) : ℝ)| *
          |(wordProbAux (k := k) θ₁ (xs 0) tail : ℝ) -
            (wordProbAux (k := k) θ₂ (xs 0) tail : ℝ)| := by
              rw [abs_mul]
    _ = (initProb (k := k) θ₂ (xs 0) : ℝ) *
          |(wordProbAux (k := k) θ₁ (xs 0) tail : ℝ) -
            (wordProbAux (k := k) θ₂ (xs 0) tail : ℝ)| := by
              rw [abs_of_nonneg hinit_nonneg]
    _ ≤ 1 *
          ((tail.length : ℝ) * ((k : ℝ) /
            (returnsToStart (k := k) s : ℝ))) := by
              gcongr
    _ = (tail.length : ℝ) * ((k : ℝ) / (returnsToStart (k := k) s : ℝ)) := by
          ring
    _ = (m : ℝ) * ((k : ℝ) / (returnsToStart (k := k) s : ℝ)) := by
          simp [htail_len]

/-- `wordProb` on `trajSnoc` factors as horizon-`m` mass times the last step probability. -/
private lemma wordProb_toReal_trajSnoc_eq_mul_stepProb
    (θ : MarkovParam k) {m : ℕ} (ys : Traj k m) (x : Fin k) :
    (wordProb (k := k) θ (trajToList (k := k) (trajSnoc (k := k) ys x))).toReal =
      (wordProb (k := k) θ (trajToList (k := k) ys)).toReal *
        (stepProb (k := k) θ (ys (Fin.last m)) x : ℝ) := by
  have haux_tail :
      wordProbAux (k := k) θ (ys 0) ((List.ofFn (fun i : Fin m => ys i.succ)) ++ [x]) =
        wordProbAux (k := k) θ (ys 0) (List.ofFn (fun i : Fin m => ys i.succ)) *
          stepProb (k := k) θ (ys (Fin.last m)) x := by
    induction m with
    | zero =>
        simp [wordProbAux]
    | succ m ih =>
        let ysTail : Traj k m := fun i => ys i.succ
        have htail :
            wordProbAux (k := k) θ (ys 1) ((List.ofFn (fun i : Fin m => ys i.succ.succ)) ++ [x]) =
              wordProbAux (k := k) θ (ys 1) (List.ofFn (fun i : Fin m => ys i.succ.succ)) *
                stepProb (k := k) θ (ys (Fin.last (Nat.succ m))) x := by
          simpa [ysTail] using ih (ys := ysTail)
        calc
          wordProbAux (k := k) θ (ys 0) ((List.ofFn (fun i : Fin (Nat.succ m) => ys i.succ)) ++ [x])
              = wordProbAux (k := k) θ (ys 0)
                  (ys 1 :: ((List.ofFn (fun i : Fin m => ys i.succ.succ)) ++ [x])) := by
                    simp [List.ofFn_succ]
          _ = stepProb (k := k) θ (ys 0) (ys 1) *
                wordProbAux (k := k) θ (ys 1) ((List.ofFn (fun i : Fin m => ys i.succ.succ)) ++ [x]) := by
                  simp [wordProbAux]
          _ = stepProb (k := k) θ (ys 0) (ys 1) *
                (wordProbAux (k := k) θ (ys 1) (List.ofFn (fun i : Fin m => ys i.succ.succ)) *
                  stepProb (k := k) θ (ys (Fin.last (Nat.succ m))) x) := by
                    rw [htail]
          _ = (stepProb (k := k) θ (ys 0) (ys 1) *
                wordProbAux (k := k) θ (ys 1) (List.ofFn (fun i : Fin m => ys i.succ.succ))) *
                  stepProb (k := k) θ (ys (Fin.last (Nat.succ m))) x := by ring
          _ = wordProbAux (k := k) θ (ys 0) (List.ofFn (fun i : Fin (Nat.succ m) => ys i.succ)) *
                  stepProb (k := k) θ (ys (Fin.last (Nat.succ m))) x := by
                simp [List.ofFn_succ, wordProbAux]
  have hlist : trajToList (k := k) (trajSnoc (k := k) ys x) = trajToList (k := k) ys ++ [x] :=
    trajToList_trajSnoc (k := k) (xs := ys) (x := x)
  cases hys : trajToList (k := k) ys with
  | nil =>
      simp [trajToList] at hys
  | cons a l =>
      have htail : (List.ofFn fun i : Fin m => ys i.succ) = l := by
        simpa [trajToList, List.ofFn_succ] using congrArg List.tail hys
      have hhead : ys 0 = a := by
        have hh := congrArg List.head? hys
        simpa [trajToList, List.ofFn_succ] using hh
      have haux' : wordProbAux (k := k) θ a (l ++ [x]) =
          wordProbAux (k := k) θ a l * stepProb (k := k) θ (ys (Fin.last m)) x := by
        simpa [hhead, htail] using haux_tail
      simp [wordProb, wordProbNN, hys, hlist, haux', mul_assoc]

/-- Event-sum helper: bound a filtered discrepancy sum by the full-space `L1` sum.
This avoids introducing a raw `card` factor at the summation step. -/
private lemma abs_sum_filter_sub_le_sum_abs_univ
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p]
    (f g : α → ℝ) :
    abs ((s.filter p).sum (fun x => f x - g x)) ≤ s.sum (fun x => |f x - g x|) := by
  have hfilter_abs :
      abs ((s.filter p).sum (fun x => f x - g x)) ≤
        (s.filter p).sum (fun x => |f x - g x|) := by
    simpa using
      (Finset.abs_sum_le_sum_abs
        (s := s.filter p)
        (f := fun x => f x - g x))
  have hfilter_le_univ :
      (s.filter p).sum (fun x => |f x - g x|) ≤ s.sum (fun x => |f x - g x|) := by
    calc
      (s.filter p).sum (fun x => |f x - g x|)
          = s.sum (fun x => if p x then |f x - g x| else 0) := by
            simp [Finset.sum_filter]
      _ ≤ s.sum (fun x => |f x - g x|) := by
            refine Finset.sum_le_sum ?_
            intro x hx
            by_cases hpx : p x
            · simp [hpx]
            · have hnonneg : 0 ≤ |f x - g x| := abs_nonneg _
              simp [hpx, hnonneg]
  exact le_trans hfilter_abs hfilter_le_univ

/-- Event-level discrepancy for `W.toReal`: absolute difference is bounded by
the `L1` sum over the same filtered event fiber. -/
private lemma abs_W_toReal_sub_le_filtered_trajL1
    (n : ℕ) (e : MarkovState k) (θ₁ θ₂ : MarkovParam k) :
    |(W (k := k) n e θ₁).toReal - (W (k := k) n e θ₂).toReal| ≤
      Finset.sum ((trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e))
        (fun xs =>
          |(wordProb (k := k) θ₁ (trajToList (k := k) xs)).toReal -
            (wordProb (k := k) θ₂ (trajToList (k := k) xs)).toReal|) := by
  classical
  let S : Finset (Traj k n) := (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e)
  let f : Traj k n → ℝ := fun xs => (wordProb (k := k) θ₁ (trajToList (k := k) xs)).toReal
  let g : Traj k n → ℝ := fun xs => (wordProb (k := k) θ₂ (trajToList (k := k) xs)).toReal
  have hW1 :
      (W (k := k) n e θ₁).toReal = Finset.sum S f := by
    simp [S, f, W_toReal_eq_sum_wordProb_toReal]
  have hW2 :
      (W (k := k) n e θ₂).toReal = Finset.sum S g := by
    simp [S, g, W_toReal_eq_sum_wordProb_toReal]
  calc
    |(W (k := k) n e θ₁).toReal - (W (k := k) n e θ₂).toReal|
        = |Finset.sum S f - Finset.sum S g| := by simp [hW1, hW2]
    _ = |Finset.sum S (fun xs => f xs - g xs)| := by simp [Finset.sum_sub_distrib]
    _ ≤ Finset.sum S (fun xs => |f xs - g xs|) := by
          simpa using
            (Finset.abs_sum_le_sum_abs (s := S) (f := fun xs => f xs - g xs))
    _ =
      Finset.sum ((trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e))
        (fun xs =>
          |(wordProb (k := k) θ₁ (trajToList (k := k) xs)).toReal -
            (wordProb (k := k) θ₂ (trajToList (k := k) xs)).toReal|) := by
          simp [S, f, g]

/-- Event-level discrepancy for `W.toReal` is bounded by the global trajectory `L1`
distance via `abs_sum_filter_sub_le_sum_abs_univ`. -/
private lemma abs_W_toReal_sub_le_global_trajL1
    (n : ℕ) (e : MarkovState k) (θ₁ θ₂ : MarkovParam k) :
    |(W (k := k) n e θ₁).toReal - (W (k := k) n e θ₂).toReal| ≤
      Finset.sum (trajFinset k n)
        (fun xs =>
          |(wordProb (k := k) θ₁ (trajToList (k := k) xs)).toReal -
            (wordProb (k := k) θ₂ (trajToList (k := k) xs)).toReal|) := by
  classical
  let S : Finset (Traj k n) := trajFinset k n
  let P : Traj k n → Prop := fun xs => stateOfTraj (k := k) xs = e
  let f : Traj k n → ℝ := fun xs => (wordProb (k := k) θ₁ (trajToList (k := k) xs)).toReal
  let g : Traj k n → ℝ := fun xs => (wordProb (k := k) θ₂ (trajToList (k := k) xs)).toReal
  have hW1 :
      (W (k := k) n e θ₁).toReal = Finset.sum (S.filter P) f := by
    simp [S, P, f, W_toReal_eq_sum_wordProb_toReal]
  have hW2 :
      (W (k := k) n e θ₂).toReal = Finset.sum (S.filter P) g := by
    simp [S, P, g, W_toReal_eq_sum_wordProb_toReal]
  calc
    |(W (k := k) n e θ₁).toReal - (W (k := k) n e θ₂).toReal|
        = |Finset.sum (S.filter P) f - Finset.sum (S.filter P) g| := by simp [hW1, hW2]
    _ = abs ((S.filter P).sum (fun xs => f xs - g xs)) := by simp [Finset.sum_sub_distrib]
    _ ≤ S.sum (fun xs => |f xs - g xs|) := by
          exact
            abs_sum_filter_sub_le_sum_abs_univ
              (s := S) (p := P) (f := f) (g := g)
    _ =
      Finset.sum (trajFinset k n)
        (fun xs =>
          |(wordProb (k := k) θ₁ (trajToList (k := k) xs)).toReal -
            (wordProb (k := k) θ₂ (trajToList (k := k) xs)).toReal|) := by
          simp [S, f, g]

/-- Global trajectory `L1` distance at fixed horizon `n`. -/
def trajL1 (n : ℕ) (θ₁ θ₂ : MarkovParam k) : ℝ :=
  Finset.sum (trajFinset k n)
    (fun xs =>
      |(wordProb (k := k) θ₁ (trajToList (k := k) xs)).toReal -
        (wordProb (k := k) θ₂ (trajToList (k := k) xs)).toReal|)

/-- Event-mass discrepancy for `W.toReal` is bounded by global trajectory `L1`. -/
lemma abs_W_toReal_sub_le_trajL1
    (n : ℕ) (e : MarkovState k) (θ₁ θ₂ : MarkovParam k) :
    |(W (k := k) n e θ₁).toReal - (W (k := k) n e θ₂).toReal| ≤
      trajL1 (k := k) n θ₁ θ₂ := by
  simpa [trajL1] using
    (abs_W_toReal_sub_le_global_trajL1
      (k := k) (n := n) (e := e) (θ₁ := θ₁) (θ₂ := θ₂))

private lemma sum_wordProb_toReal_eq_one (θ : MarkovParam k) (n : ℕ) :
    Finset.sum (trajFinset k n)
      (fun xs => (wordProb (k := k) θ (trajToList (k := k) xs)).toReal) = 1 := by
  have hsumENN :
      (∑ xs : Traj k n, wordProb (k := k) θ (trajToList (k := k) xs)) = 1 := by
    simpa [sum_W_eq_one (k := k) (n := n) (θ := θ)] using
      (sum_W_eq_one' (k := k) (n := n) (θ := θ))
  have htoReal :
      (Finset.sum (trajFinset k n)
        (fun xs => wordProb (k := k) θ (trajToList (k := k) xs))).toReal =
      Finset.sum (trajFinset k n)
        (fun xs => (wordProb (k := k) θ (trajToList (k := k) xs)).toReal) := by
    refine ENNReal.toReal_sum ?_
    intro xs hx
    simp [wordProb]
  calc
    Finset.sum (trajFinset k n)
        (fun xs => (wordProb (k := k) θ (trajToList (k := k) xs)).toReal)
        =
      (Finset.sum (trajFinset k n)
        (fun xs => wordProb (k := k) θ (trajToList (k := k) xs))).toReal := htoReal.symm
    _ = (∑ xs : Traj k n, wordProb (k := k) θ (trajToList (k := k) xs)).toReal := by
          simp [trajFinset]
    _ = (1 : ENNReal).toReal := by simp [hsumENN]
    _ = 1 := by simp

private lemma trajL1_succ_le_trajL1_add_rowBound
    (θ₁ θ₂ : MarkovParam k) (n : ℕ) (δ : ℝ)
    (hrow :
      ∀ prev : Fin k,
        (∑ next : Fin k,
          |(stepProb (k := k) θ₁ prev next : ℝ) -
            (stepProb (k := k) θ₂ prev next : ℝ)|) ≤ δ) :
    trajL1 (k := k) (Nat.succ n) θ₁ θ₂ ≤ trajL1 (k := k) n θ₁ θ₂ + δ := by
  let F : Traj k (Nat.succ n) → ℝ := fun xs =>
    |(wordProb (k := k) θ₁ (trajToList (k := k) xs)).toReal -
      (wordProb (k := k) θ₂ (trajToList (k := k) xs)).toReal|
  have hrewrite :
      (∑ xs : Traj k (Nat.succ n), F xs) =
        ∑ p : (Fin k) × (Traj k n), F (trajSnoc (k := k) p.2 p.1) := by
    have hEquiv :
        (∑ p : (Fin k) × (Traj k n), F (trajSnoc (k := k) p.2 p.1)) =
          (∑ xs : Traj k (Nat.succ n), F xs) := by
      refine (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 2) => Fin k))
        (fun p => F (trajSnoc (k := k) p.2 p.1))
        (fun xs => F xs) ?_)
      intro p
      rfl
    exact hEquiv.symm
  calc
    trajL1 (k := k) (Nat.succ n) θ₁ θ₂
        = (∑ xs : Traj k (Nat.succ n), F xs) := by
            simp [trajL1, trajFinset, F]
    _ = ∑ p : (Fin k) × (Traj k n), F (trajSnoc (k := k) p.2 p.1) := hrewrite
    _ = ∑ ys : Traj k n,
          ∑ x : Fin k,
            |(wordProb (k := k) θ₁ (trajToList (k := k) (trajSnoc (k := k) ys x))).toReal -
              (wordProb (k := k) θ₂ (trajToList (k := k) (trajSnoc (k := k) ys x))).toReal| := by
          simp [F, Fintype.sum_prod_type_right]
    _ ≤ ∑ ys : Traj k n,
          (|(wordProb (k := k) θ₁ (trajToList (k := k) ys)).toReal -
              (wordProb (k := k) θ₂ (trajToList (k := k) ys)).toReal| +
            (wordProb (k := k) θ₂ (trajToList (k := k) ys)).toReal * δ) := by
          refine Finset.sum_le_sum ?_
          intro ys hys
          let A1 : ℝ := (wordProb (k := k) θ₁ (trajToList (k := k) ys)).toReal
          let A2 : ℝ := (wordProb (k := k) θ₂ (trajToList (k := k) ys)).toReal
          let s1 : Fin k → ℝ := fun x => (stepProb (k := k) θ₁ (ys (Fin.last n)) x : ℝ)
          let s2 : Fin k → ℝ := fun x => (stepProb (k := k) θ₂ (ys (Fin.last n)) x : ℝ)
          have hsnoc1 : ∀ x : Fin k,
              (wordProb (k := k) θ₁ (trajToList (k := k) (trajSnoc (k := k) ys x))).toReal = A1 * s1 x := by
            intro x
            simpa [A1, s1] using
              (wordProb_toReal_trajSnoc_eq_mul_stepProb (k := k) (θ := θ₁) (ys := ys) (x := x))
          have hsnoc2 : ∀ x : Fin k,
              (wordProb (k := k) θ₂ (trajToList (k := k) (trajSnoc (k := k) ys x))).toReal = A2 * s2 x := by
            intro x
            simpa [A2, s2] using
              (wordProb_toReal_trajSnoc_eq_mul_stepProb (k := k) (θ := θ₂) (ys := ys) (x := x))
          have hA2_nonneg : 0 ≤ A2 := by
            unfold A2
            positivity
          have hs1_nonneg : ∀ x : Fin k, 0 ≤ s1 x := by
            intro x
            unfold s1
            positivity
          have hsum1 : (∑ x : Fin k, s1 x) = 1 := by
            simpa [s1] using sum_stepProb_toReal_eq_one (k := k) (θ := θ₁) (prev := ys (Fin.last n))
          have hsplit :
              (∑ x : Fin k, |A1 * s1 x - A2 * s2 x|)
                ≤ |A1 - A2| + A2 * δ := by
            have htri :
                (∑ x : Fin k, |A1 * s1 x - A2 * s2 x|)
                  ≤ (∑ x : Fin k, |A1 * s1 x - A2 * s1 x|) +
                    (∑ x : Fin k, |A2 * s1 x - A2 * s2 x|) := by
              calc
                (∑ x : Fin k, |A1 * s1 x - A2 * s2 x|)
                    ≤ ∑ x : Fin k, (|A1 * s1 x - A2 * s1 x| + |A2 * s1 x - A2 * s2 x|) := by
                        refine Finset.sum_le_sum ?_
                        intro x hx
                        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                          (abs_sub_le (A1 * s1 x) (A2 * s1 x) (A2 * s2 x))
                _ = (∑ x : Fin k, |A1 * s1 x - A2 * s1 x|) +
                      (∑ x : Fin k, |A2 * s1 x - A2 * s2 x|) := by
                        simp [Finset.sum_add_distrib]
            have hfirst :
                (∑ x : Fin k, |(A1 - A2) * s1 x|) = |A1 - A2| := by
              calc
                (∑ x : Fin k, |(A1 - A2) * s1 x|)
                    = (∑ x : Fin k, |A1 - A2| * s1 x) := by
                        refine Fintype.sum_congr (fun x => |(A1 - A2) * s1 x|) (fun x => |A1 - A2| * s1 x) ?_
                        intro x
                        simp [abs_mul, abs_of_nonneg (hs1_nonneg x)]
                _ = |A1 - A2| * (∑ x : Fin k, s1 x) := by
                      exact (Finset.mul_sum (s := Finset.univ) (f := fun x => s1 x) (a := |A1 - A2|)).symm
                _ = |A1 - A2| := by simp [hsum1]
            have hsecond :
                (∑ x : Fin k, |A2 * (s1 x - s2 x)|) ≤ A2 * δ := by
              calc
                (∑ x : Fin k, |A2 * (s1 x - s2 x)|)
                    = A2 * (∑ x : Fin k, |s1 x - s2 x|) := by
                        calc
                          (∑ x : Fin k, |A2 * (s1 x - s2 x)|)
                              = (∑ x : Fin k, |A2| * |s1 x - s2 x|) := by
                                  refine Fintype.sum_congr (fun x => |A2 * (s1 x - s2 x)|)
                                    (fun x => |A2| * |s1 x - s2 x|) ?_
                                  intro x
                                  simp [abs_mul]
                          _ = (∑ x : Fin k, A2 * |s1 x - s2 x|) := by
                                refine Fintype.sum_congr (fun x => |A2| * |s1 x - s2 x|)
                                  (fun x => A2 * |s1 x - s2 x|) ?_
                                intro x
                                rw [abs_of_nonneg hA2_nonneg]
                          _ = A2 * (∑ x : Fin k, |s1 x - s2 x|) := by
                                exact (Finset.mul_sum (s := Finset.univ) (f := fun x => |s1 x - s2 x|) (a := A2)).symm
                _ ≤ A2 * δ := by
                      gcongr
                      simpa [s1, s2] using hrow (ys (Fin.last n))
            have hfirst_rewrite :
                (∑ x : Fin k, |A1 * s1 x - A2 * s1 x|) = (∑ x : Fin k, |(A1 - A2) * s1 x|) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring_nf
            have hsecond_rewrite :
                (∑ x : Fin k, |A2 * s1 x - A2 * s2 x|) = (∑ x : Fin k, |A2 * (s1 x - s2 x)|) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring_nf
            linarith [htri, hfirst, hsecond, hfirst_rewrite, hsecond_rewrite]
          calc
            (∑ x : Fin k,
              |(wordProb (k := k) θ₁ (trajToList (k := k) (trajSnoc (k := k) ys x))).toReal -
                (wordProb (k := k) θ₂ (trajToList (k := k) (trajSnoc (k := k) ys x))).toReal|)
                = (∑ x : Fin k, |A1 * s1 x - A2 * s2 x|) := by
                    refine Fintype.sum_congr (fun x =>
                      |(wordProb (k := k) θ₁ (trajToList (k := k) (trajSnoc (k := k) ys x))).toReal -
                        (wordProb (k := k) θ₂ (trajToList (k := k) (trajSnoc (k := k) ys x))).toReal|)
                      (fun x => |A1 * s1 x - A2 * s2 x|) ?_
                    intro x
                    simp [hsnoc1 x, hsnoc2 x]
            _ ≤ |A1 - A2| + A2 * δ := hsplit
            _ = (|(wordProb (k := k) θ₁ (trajToList (k := k) ys)).toReal -
                    (wordProb (k := k) θ₂ (trajToList (k := k) ys)).toReal| +
                  (wordProb (k := k) θ₂ (trajToList (k := k) ys)).toReal * δ) := by
                    simp [A1, A2]
    _ = trajL1 (k := k) n θ₁ θ₂ +
          (∑ ys : Traj k n, (wordProb (k := k) θ₂ (trajToList (k := k) ys)).toReal) * δ := by
          simp [trajL1, trajFinset, Finset.sum_add_distrib, Finset.sum_mul]
    _ = trajL1 (k := k) n θ₁ θ₂ + 1 * δ := by
          have hsum1' :
              (∑ ys : Traj k n, (wordProb (k := k) θ₂ (trajToList (k := k) ys)).toReal) = 1 := by
            simpa [trajFinset] using sum_wordProb_toReal_eq_one (k := k) (θ := θ₂) (n := n)
          simp [hsum1']
    _ = trajL1 (k := k) n θ₁ θ₂ + δ := by ring

private lemma trajL1_empiricalParam_startTarget_le_length_mul_rowBound
    (hk : 0 < k) {N : ℕ} {s : MarkovState k}
    (hs : s ∈ stateFinset k N)
    (hRpos : 0 < returnsToStart (k := k) s)
    (n : ℕ) :
    trajL1 (k := k) (Nat.succ n)
      (empiricalParam (k := k) hk s)
      (empiricalParamStartTarget (k := k) hk s)
      ≤
      (Nat.succ n : ℝ) *
        (((k : ℝ) * (k : ℝ)) / (returnsToStart (k := k) s : ℝ)) := by
  let θ₁ : MarkovParam k := empiricalParam (k := k) hk s
  let θ₂ : MarkovParam k := empiricalParamStartTarget (k := k) hk s
  let δ : ℝ := ((k : ℝ) * (k : ℝ)) / (returnsToStart (k := k) s : ℝ)
  have hδnonneg : 0 ≤ δ := by
    unfold δ
    have hk_nonneg : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    have hR_nonneg : 0 ≤ (returnsToStart (k := k) s : ℝ) := by
      exact_mod_cast (Nat.zero_le (returnsToStart (k := k) s))
    exact div_nonneg (mul_nonneg hk_nonneg hk_nonneg) hR_nonneg
  have hrow :
      ∀ prev : Fin k,
        (∑ next : Fin k,
          |(stepProb (k := k) θ₁ prev next : ℝ) -
            (stepProb (k := k) θ₂ prev next : ℝ)|) ≤ δ := by
    intro prev
    simpa [θ₁, θ₂, δ] using
      (sum_abs_stepProb_empiricalParam_sub_startTarget_row_le_k_sq_div_returnsToStart
        (k := k) (hk := hk) (s := s) (hs := hs) (hRpos := hRpos) (prev := prev))
  have hbase0 :
      trajL1 (k := k) 0 θ₁ θ₂ = 0 := by
    unfold trajL1 trajFinset
    refine Finset.sum_eq_zero ?_
    intro xs hx
    have hterm :
        |(wordProb (k := k) θ₁ (trajToList (k := k) xs)).toReal -
          (wordProb (k := k) θ₂ (trajToList (k := k) xs)).toReal|
          ≤
        (0 : ℝ) * ((k : ℝ) / (returnsToStart (k := k) s : ℝ)) := by
      simpa [θ₁, θ₂] using
        (abs_wordProb_toReal_empiricalParam_sub_startTarget_of_traj
          (k := k) (hk := hk) (s := s) (hs := hs) (hRpos := hRpos) (m := 0) xs)
    have hnonneg :
        0 ≤ |(wordProb (k := k) θ₁ (trajToList (k := k) xs)).toReal -
              (wordProb (k := k) θ₂ (trajToList (k := k) xs)).toReal| := by
      exact abs_nonneg _
    have hzero :
        |(wordProb (k := k) θ₁ (trajToList (k := k) xs)).toReal -
          (wordProb (k := k) θ₂ (trajToList (k := k) xs)).toReal| = 0 := by
      linarith
    simp [hzero]
  have hrec :
      ∀ m : ℕ, trajL1 (k := k) m θ₁ θ₂ ≤ (m : ℝ) * δ := by
    intro m
    induction m with
    | zero =>
        rw [hbase0]
        nlinarith [hδnonneg]
    | succ m ihm =>
        have hstep :
            trajL1 (k := k) (Nat.succ m) θ₁ θ₂ ≤ trajL1 (k := k) m θ₁ θ₂ + δ :=
          trajL1_succ_le_trajL1_add_rowBound
            (k := k) (θ₁ := θ₁) (θ₂ := θ₂) (n := m) (δ := δ) hrow
        calc
          trajL1 (k := k) (Nat.succ m) θ₁ θ₂ ≤ trajL1 (k := k) m θ₁ θ₂ + δ := hstep
          _ ≤ (m : ℝ) * δ + δ := by gcongr
          _ = (Nat.succ m : ℝ) * δ := by
                calc
                  (m : ℝ) * δ + δ = (m : ℝ) * δ + 1 * δ := by ring
                  _ = ((m : ℝ) + 1) * δ := by ring
                  _ = (Nat.succ m : ℝ) * δ := by norm_num
  simpa [θ₁, θ₂, δ] using hrec (Nat.succ n)

/-- First nontrivial WR-rate theorem for the start-target scalar surrogate:
statewise `W` discrepancy is `O(1 / returnsToStart)` with explicit constant. -/
theorem hasStatewiseStartTargetWClose_of_rowL1
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) :
    HasStatewiseStartTargetWClose (k := k) hk n e
      ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))) := by
  intro N hN s hs hRpos
  let θ₁ : MarkovParam k := empiricalParam (k := k) hk s
  let θ₂ : MarkovParam k := empiricalParamStartTarget (k := k) hk s
  let Cw : ℝ := (Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))
  have hWglobal :
      |(W (k := k) (Nat.succ n) e θ₁).toReal - (W (k := k) (Nat.succ n) e θ₂).toReal| ≤
        trajL1 (k := k) (Nat.succ n) θ₁ θ₂ := by
    simpa [θ₁, θ₂] using
      (abs_W_toReal_sub_le_trajL1
        (k := k) (n := Nat.succ n) (e := e) (θ₁ := θ₁) (θ₂ := θ₂))
  have htrajL1 :
      trajL1 (k := k) (Nat.succ n) θ₁ θ₂ ≤
        Cw / (returnsToStart (k := k) s : ℝ) := by
    have hbound :=
      trajL1_empiricalParam_startTarget_le_length_mul_rowBound
        (k := k) (hk := hk) (s := s) (hs := hs) (hRpos := hRpos) (n := n)
    have hsplit :
        (Nat.succ n : ℝ) * (((k : ℝ) * (k : ℝ)) / (returnsToStart (k := k) s : ℝ))
          = Cw / (returnsToStart (k := k) s : ℝ) := by
      simp [Cw]
      ring
    calc
      trajL1 (k := k) (Nat.succ n) θ₁ θ₂
          ≤ (Nat.succ n : ℝ) * (((k : ℝ) * (k : ℝ)) / (returnsToStart (k := k) s : ℝ)) := hbound
      _ = Cw / (returnsToStart (k := k) s : ℝ) := hsplit
  calc
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        (W (k := k) (Nat.succ n) e (empiricalParamStartTarget (k := k) hk s)).toReal|
        = |(W (k := k) (Nat.succ n) e θ₁).toReal - (W (k := k) (Nat.succ n) e θ₂).toReal| := by
            simp [θ₁, θ₂]
    _ ≤ trajL1 (k := k) (Nat.succ n) θ₁ θ₂ := hWglobal
    _ ≤ Cw / (returnsToStart (k := k) s : ℝ) := htrajL1

/--
Statewise WR excursion-target witness with explicit `Crepr`/`Cstep` rates.

This names the core WR-side semantic obligation so callers can target one
predicate instead of repeating a large dependent witness type.
-/
def HasStatewiseExcursionTargetRates
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ) : Prop :=
  ∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
    s ∈ stateFinset k N →
      0 < returnsToStart (k := k) s →
        ∃ elist pref : ExcursionList k,
          ∃ target : ExcursionType k → ℝ,
            ∃ Crepr Cstep : ℝ,
              |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
                excursionWithReplacementProb (k := k) elist pref| ≤
                  Crepr / (returnsToStart (k := k) s : ℝ) ∧
              (∀ a ∈ pref,
                |empiricalExcursionProb (k := k) elist a - target a| ≤
                  Cstep / (returnsToStart (k := k) s : ℝ)) ∧
              (∀ a ∈ pref, 0 ≤ target a ∧ target a ≤ 1) ∧
              Crepr + (pref.length : ℝ) * Cstep ≤ Cw

lemma pattern_alignment_residuals_nonneg
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (q : ExcursionList k → ℝ) (εW εPC : ℝ)
    (hwr_q :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal - q p| ≤ εW)
    (hq_wor :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC) :
    0 ≤ εW ∧ 0 ≤ εPC := by
  have hwr_nonneg :
      0 ≤ ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal - q p| := by
    refine Finset.sum_nonneg ?_
    intro p hp
    exact abs_nonneg _
  have hq_nonneg :
      0 ≤ ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal| := by
    refine Finset.sum_nonneg ?_
    intro p hp
    exact abs_nonneg _
  exact ⟨le_trans hwr_nonneg hwr_q, le_trans hq_nonneg hq_wor⟩

lemma pattern_alignment_witness_forces_zero_residuals
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (q : ExcursionList k → ℝ) (εW εPC : ℝ)
    (hwr_q :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal - q p| ≤ εW)
    (hq_wor :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC)
    (hgap : εW + εPC ≤ 0) :
    εW = 0 ∧ εPC = 0 := by
  rcases pattern_alignment_residuals_nonneg
      (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s)
      (q := q) (εW := εW) (εPC := εPC) hwr_q hq_wor with ⟨hWnonneg, hPCnonneg⟩
  have hWnonpos : εW ≤ 0 := by linarith
  have hPCnonpos : εPC ≤ 0 := by linarith
  exact ⟨le_antisymm hWnonpos hWnonneg, le_antisymm hPCnonpos hPCnonneg⟩

lemma canonical_alignment_witness_forces_zero_residuals
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (wSurrogate εW εPC : ℝ)
    (hWsurrogate :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        wSurrogate| ≤ εW)
    (hq_wor :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC)
    (hgap : εW + εPC ≤ 0) :
    εW = 0 ∧ εPC = 0 := by
  have hwr_q :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          canonicalWRSurrogateMass (k := k) n e wSurrogate p| ≤ εW :=
    sum_abs_wrPatternMass_toReal_sub_canonicalWRSurrogateMass_le
      (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
      (wSurrogate := wSurrogate) (εW := εW) (hWsurrogate := hWsurrogate)
  exact
    pattern_alignment_witness_forces_zero_residuals
      (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s)
      (q := canonicalWRSurrogateMass (k := k) n e wSurrogate)
      (εW := εW) (εPC := εPC)
      hwr_q hq_wor hgap

lemma hasCanonicalWRSurrogateAlignment_forces_zero_residuals
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hcanon : HasCanonicalWRSurrogateAlignment (k := k) hk n e) :
    ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
      s ∈ stateFinset k N →
        ∃ wSurrogate εW εPC : ℝ,
          |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
            wSurrogate| ≤ εW ∧
          (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
            |canonicalWRSurrogateMass (k := k) n e wSurrogate p -
              (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤ εPC) ∧
          εW + εPC ≤ 0 ∧ εW = 0 ∧ εPC = 0 := by
  intro N hN s hs
  rcases hcanon hN s hs with ⟨wSurrogate, εW, εPC, hWsurrogate, hq_wor, hgap⟩
  have hzero :=
    canonical_alignment_witness_forces_zero_residuals
      (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s)
      (wSurrogate := wSurrogate) (εW := εW) (εPC := εPC)
      hWsurrogate hq_wor hgap
  exact ⟨wSurrogate, εW, εPC, hWsurrogate, hq_wor, hgap, hzero.1, hzero.2⟩

lemma hasPatternSurrogateAlignment_of_canonical
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hcanon : HasCanonicalWRSurrogateAlignment (k := k) hk n e) :
    HasPatternSurrogateAlignment (k := k) hk n e := by
  intro N hN s hs
  rcases hcanon hN s hs with ⟨wSurrogate, εW, εPC, hWsurrogate, hq_wor, hgap⟩
  refine ⟨canonicalWRSurrogateMass (k := k) n e wSurrogate, εW, εPC, ?_, hq_wor, hgap⟩
  exact
    sum_abs_wrPatternMass_toReal_sub_canonicalWRSurrogateMass_le
      (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
      (wSurrogate := wSurrogate) (εW := εW) (hWsurrogate := hWsurrogate)

lemma hasExcursionBiapproxCore_of_patternSurrogateAlignment
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (halign : HasPatternSurrogateAlignment (k := k) hk n e) :
    HasExcursionBiapproxCore (k := k) hk n e := by
  intro N hN s hs
  rcases halign hN s hs with ⟨q, εW, εPC, hwr_q, hq_wor, hgap⟩
  exact
    excursionBiapproxPackage_of_pattern_surrogate
      (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s)
      (q := q) (εW := εW) (εPC := εPC)
      hwr_q hq_wor hgap

lemma hasExcursionBiapproxCore_of_canonical
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hcanon : HasCanonicalWRSurrogateAlignment (k := k) hk n e) :
    HasExcursionBiapproxCore (k := k) hk n e := by
  exact
    hasExcursionBiapproxCore_of_patternSurrogateAlignment
      (k := k) (hk := hk) (n := n) (e := e)
      (hasPatternSurrogateAlignment_of_canonical
        (k := k) (hk := hk) (n := n) (e := e) hcanon)

/-- BEST-side counting constructor for the strict core package.

The only remaining obligation is the representative-partition bound in
`hreprBound`, with collision RHS. -/
theorem hasExcursionBiapproxCore_of_best_repr_bound
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hreprBound :
      ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
        s ∈ stateFinset k N →
          let P := excursionPatternSet (k := k) (hN := hN) e s
          let repr : Multiset (ExcursionType k) → ExcursionList k := fun mset =>
            if hm : ∃ p ∈ P, Multiset.ofList p = mset then (Classical.choose hm) else []
          (∑ mset ∈ P.image Multiset.ofList,
            (((P.filter (fun p => Multiset.ofList p = mset)).card : ℝ) *
              |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
                (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal|))
            ≤
              (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
                (returnsToStart (k := k) s : ℝ)) :
    HasExcursionBiapproxCore (k := k) hk n e := by
  intro N hN s hs
  exact
    excursionBiapproxPackage_of_repr_bound
      (k := k) (hk := hk) (n := n) (e := e)
      (hN := hN) (s := s) (hs := hs)
      (bound :=
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ))
      (hbound_repr := hreprBound hN s hs)
      (hbound_le_collision := le_rfl)

/-- Alias-wrapper version of `hasExcursionBiapproxCore_of_best_repr_bound`. -/
theorem hasExcursionBiapproxCore_of_bestReprBound
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hreprBound : HasBestReprBound (k := k) hk n e) :
    HasExcursionBiapproxCore (k := k) hk n e := by
  exact hasExcursionBiapproxCore_of_best_repr_bound
    (k := k) (hk := hk) (n := n) (e := e) hreprBound

/-- Family-level version of `hasExcursionBiapproxCore_of_best_repr_bound`. -/
theorem hasExcursionBiapproxCoreAll_of_best_repr_boundAll
    (hreprBoundAll :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
          s ∈ stateFinset k N →
            let P := excursionPatternSet (k := k) (hN := hN) e s
            let repr : Multiset (ExcursionType k) → ExcursionList k := fun mset =>
              if hm : ∃ p ∈ P, Multiset.ofList p = mset then (Classical.choose hm) else []
            (∑ mset ∈ P.image Multiset.ofList,
              (((P.filter (fun p => Multiset.ofList p = mset)).card : ℝ) *
                |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
                  (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal|))
              ≤
                (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
                  (returnsToStart (k := k) s : ℝ)) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e := by
  intro hk n e
  exact
    hasExcursionBiapproxCore_of_best_repr_bound
      (k := k) (hk := hk) (n := n) (e := e)
      (hreprBound := hreprBoundAll hk n e)

/-- Alias-wrapper version of `hasExcursionBiapproxCoreAll_of_best_repr_boundAll`. -/
theorem hasExcursionBiapproxCoreAll_of_bestReprBoundAll
    (hreprBoundAll : HasBestReprBoundAll (k := k)) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e := by
  exact hasExcursionBiapproxCoreAll_of_best_repr_boundAll
    (k := k) hreprBoundAll

/-- Build the strict core package from a direct pattern-sum collision bound
on positive-return states, plus an explicit zero-return case.

This isolates the last semantic/combinatorial obligations into two concrete
statewise statements while keeping the downstream hard-direction pipeline
unchanged. -/
theorem hasExcursionBiapproxCore_of_patternCollision_and_zeroCase
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hpos :
      ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
        s ∈ stateFinset k N →
          0 < returnsToStart (k := k) s →
            (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
              |(wrPatternMass (k := k) hk n e s p).toReal -
                (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
              (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
                (returnsToStart (k := k) s : ℝ))
    (hzero :
      ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
        s ∈ stateFinset k N →
          returnsToStart (k := k) s = 0 →
            (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
              |(wrPatternMass (k := k) hk n e s p).toReal -
                (worPatternMass (k := k) (hN := hN) e s p).toReal|) = 0) :
    HasExcursionBiapproxCore (k := k) hk n e := by
  intro N hN s hs
  let P := excursionPatternSet (k := k) (hN := hN) e s
  let collision : ℝ :=
    (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
      (returnsToStart (k := k) s : ℝ)
  have hpart :
      (∑ p ∈ P,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
      (∑ mset ∈ P.image Multiset.ofList,
        ∑ p ∈ P with Multiset.ofList p = mset,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal|) := by
    simpa [P] using
      (sum_abs_wr_wor_patternMass_partition_by_excursionMultiset
        (k := k) (hN := hN) (hk := hk) (e := e) (s := s))
  have hsum_part_le_collision :
      (∑ mset ∈ P.image Multiset.ofList,
        ∑ p ∈ P with Multiset.ofList p = mset,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
      collision := by
    by_cases hRpos : 0 < returnsToStart (k := k) s
    · have hsum_pos :
        (∑ p ∈ P,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
          collision := by
        simpa [P, collision] using hpos hN s hs hRpos
      calc
        (∑ mset ∈ P.image Multiset.ofList,
          ∑ p ∈ P with Multiset.ofList p = mset,
            |(wrPatternMass (k := k) hk n e s p).toReal -
              (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
          (∑ p ∈ P,
            |(wrPatternMass (k := k) hk n e s p).toReal -
              (worPatternMass (k := k) (hN := hN) e s p).toReal|) := by
                simpa using hpart.symm
        _ ≤ collision := hsum_pos
    · have hRzero : returnsToStart (k := k) s = 0 := Nat.eq_zero_of_not_pos hRpos
      have hsum_zero :
          (∑ p ∈ P,
            |(wrPatternMass (k := k) hk n e s p).toReal -
              (worPatternMass (k := k) (hN := hN) e s p).toReal|) = 0 := by
        simpa [P] using hzero hN s hs hRzero
      have hcollision_zero : collision = 0 := by
        simp [collision, hRzero]
      have hsum_part_zero :
          (∑ mset ∈ P.image Multiset.ofList,
            ∑ p ∈ P with Multiset.ofList p = mset,
              |(wrPatternMass (k := k) hk n e s p).toReal -
                (worPatternMass (k := k) (hN := hN) e s p).toReal|) = 0 := by
        calc
          (∑ mset ∈ P.image Multiset.ofList,
            ∑ p ∈ P with Multiset.ofList p = mset,
              |(wrPatternMass (k := k) hk n e s p).toReal -
                (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
            (∑ p ∈ P,
              |(wrPatternMass (k := k) hk n e s p).toReal -
                (worPatternMass (k := k) (hN := hN) e s p).toReal|) := by
                  simpa using hpart.symm
          _ = 0 := hsum_zero
      calc
        (∑ mset ∈ P.image Multiset.ofList,
          ∑ p ∈ P with Multiset.ofList p = mset,
            |(wrPatternMass (k := k) hk n e s p).toReal -
              (worPatternMass (k := k) (hN := hN) e s p).toReal|) = 0 := hsum_part_zero
        _ ≤ collision := by simp [hcollision_zero]
  refine ⟨0, 0, ?_, by simp⟩
  simpa [collision] using hsum_part_le_collision

/-- Family-level version of
`hasExcursionBiapproxCore_of_patternCollision_and_zeroCase`. -/
theorem hasExcursionBiapproxCoreAll_of_patternCollision_and_zeroCaseAll
    (hposAll :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
          s ∈ stateFinset k N →
            0 < returnsToStart (k := k) s →
              (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
                |(wrPatternMass (k := k) hk n e s p).toReal -
                  (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
                (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
                  (returnsToStart (k := k) s : ℝ))
    (hzeroAll :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
          s ∈ stateFinset k N →
            returnsToStart (k := k) s = 0 →
              (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
                |(wrPatternMass (k := k) hk n e s p).toReal -
                  (worPatternMass (k := k) (hN := hN) e s p).toReal|) = 0) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e := by
  intro hk n e
  exact
    hasExcursionBiapproxCore_of_patternCollision_and_zeroCase
      (k := k) (hk := hk) (n := n) (e := e)
      (hpos := hposAll hk n e)
      (hzero := hzeroAll hk n e)

lemma hasPatternSurrogateResidualAlignment_of_canonicalResidual
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hcanon : HasCanonicalWRSurrogateResidualAlignment (k := k) hk n e) :
    HasPatternSurrogateResidualAlignment (k := k) hk n e := by
  intro N hN s hs
  rcases hcanon hN s hs with ⟨wSurrogate, εW, εPC, hWsurrogate, hq_wor⟩
  refine ⟨canonicalWRSurrogateMass (k := k) n e wSurrogate, εW, εPC, ?_, hq_wor⟩
  exact
    sum_abs_wrPatternMass_toReal_sub_canonicalWRSurrogateMass_le
      (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
      (wSurrogate := wSurrogate) (εW := εW) (hWsurrogate := hWsurrogate)

lemma hasExcursionResidualBound_of_patternSurrogateResidualAlignment
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (halign : HasPatternSurrogateResidualAlignment (k := k) hk n e) :
    HasExcursionResidualBound (k := k) hk n e := by
  intro N hN s hs
  rcases halign hN s hs with ⟨q, εW, εPC, hwr_q, hq_wor⟩
  rcases pattern_alignment_residuals_nonneg
      (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s)
      (q := q) (εW := εW) (εPC := εPC) hwr_q hq_wor with ⟨hWnonneg, hPCnonneg⟩
  refine ⟨εW, εPC, hWnonneg, hPCnonneg, ?_⟩
  exact
    excursion_bound_from_decomposition_biapprox
      (k := k) (hk := hk) (n := n) (e := e)
      (hN := hN) (s := s) (hs := hs)
      (q := q) (εW := εW) (εPC := εPC)
      hwr_q hq_wor

lemma hasExcursionResidualBound_of_canonicalResidual
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hcanon : HasCanonicalWRSurrogateResidualAlignment (k := k) hk n e) :
    HasExcursionResidualBound (k := k) hk n e := by
  exact
    hasExcursionResidualBound_of_patternSurrogateResidualAlignment
      (k := k) (hk := hk) (n := n) (e := e)
      (hasPatternSurrogateResidualAlignment_of_canonicalResidual
        (k := k) (hk := hk) (n := n) (e := e) hcanon)

lemma hasPatternSurrogateResidualAlignmentRate_of_canonicalResidualRate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (C : ℝ)
    (hcanon : HasCanonicalWRSurrogateResidualAlignmentRate (k := k) hk n e C) :
    HasPatternSurrogateResidualAlignmentRate (k := k) hk n e C := by
  intro N hN s hs hRpos
  rcases hcanon hN s hs hRpos with
    ⟨wSurrogate, εW, εPC, hWsurrogate, hq_wor, hrate⟩
  refine ⟨canonicalWRSurrogateMass (k := k) n e wSurrogate, εW, εPC, ?_, hq_wor, hrate⟩
  exact
    sum_abs_wrPatternMass_toReal_sub_canonicalWRSurrogateMass_le
      (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
      (wSurrogate := wSurrogate) (εW := εW) (hWsurrogate := hWsurrogate)

lemma hasExcursionResidualBoundRate_of_patternSurrogateResidualAlignmentRate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (C : ℝ)
    (halign : HasPatternSurrogateResidualAlignmentRate (k := k) hk n e C) :
    HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro N hN s hs hRpos
  rcases halign hN s hs hRpos with ⟨q, εW, εPC, hwr_q, hq_wor, hrate⟩
  rcases pattern_alignment_residuals_nonneg
      (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s)
      (q := q) (εW := εW) (εPC := εPC) hwr_q hq_wor with ⟨hWnonneg, hPCnonneg⟩
  refine ⟨εW, εPC, hWnonneg, hPCnonneg, hrate, ?_⟩
  exact
    excursion_bound_from_decomposition_biapprox
      (k := k) (hk := hk) (n := n) (e := e)
      (hN := hN) (s := s) (hs := hs)
      (q := q) (εW := εW) (εPC := εPC)
      hwr_q hq_wor

lemma hasExcursionResidualBoundRate_of_canonicalResidualRate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (C : ℝ)
    (hcanon : HasCanonicalWRSurrogateResidualAlignmentRate (k := k) hk n e C) :
    HasExcursionResidualBoundRate (k := k) hk n e C := by
  exact
    hasExcursionResidualBoundRate_of_patternSurrogateResidualAlignmentRate
      (k := k) (hk := hk) (n := n) (e := e) (C := C)
      (hasPatternSurrogateResidualAlignmentRate_of_canonicalResidualRate
        (k := k) (hk := hk) (n := n) (e := e) (C := C) hcanon)


lemma hasCanonicalWRSurrogateResidualAlignmentRate_of_splitRates
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw Cpc : ℝ)
    (hWR : HasCanonicalWRSmoothingRate (k := k) hk n e Cw)
    (hWOR : HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    HasCanonicalWRSurrogateResidualAlignmentRate (k := k) hk n e (Cw + Cpc) := by
  intro N hN s hs hRpos
  rcases hWR hN s hs hRpos with ⟨wSurrogate, εW, hWsurrogate, hWrate⟩
  have hwclose :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        wSurrogate| ≤ Cw / (returnsToStart (k := k) s : ℝ) :=
    le_trans hWsurrogate hWrate
  rcases hWOR hN s hs hRpos wSurrogate hwclose with ⟨εPC, hq_wor, hPCrate⟩
  refine ⟨wSurrogate, εW, εPC, hWsurrogate, hq_wor, ?_⟩
  have hsum : εW + εPC ≤
      Cw / (returnsToStart (k := k) s : ℝ) + Cpc / (returnsToStart (k := k) s : ℝ) :=
    add_le_add hWrate hPCrate
  have hsplit :
      Cw / (returnsToStart (k := k) s : ℝ) + Cpc / (returnsToStart (k := k) s : ℝ) =
        (Cw + Cpc) / (returnsToStart (k := k) s : ℝ) := by
    ring
  simpa [hsplit] using hsum

lemma hasExcursionResidualBoundRate_of_splitRates
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw Cpc : ℝ)
    (hWR : HasCanonicalWRSmoothingRate (k := k) hk n e Cw)
    (hWOR : HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    HasExcursionResidualBoundRate (k := k) hk n e (Cw + Cpc) := by
  exact
    hasExcursionResidualBoundRate_of_canonicalResidualRate
      (k := k) (hk := hk) (n := n) (e := e) (C := Cw + Cpc)
      (hasCanonicalWRSurrogateResidualAlignmentRate_of_splitRates
        (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc)
        hWR hWOR)

lemma hasCanonicalWRSmoothingRate_of_statewise_close
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ)
    (hclose :
      ∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
        s ∈ stateFinset k N →
          0 < returnsToStart (k := k) s →
            ∃ wSurrogate : ℝ,
              |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
                wSurrogate| ≤ Cw / (returnsToStart (k := k) s : ℝ)) :
    HasCanonicalWRSmoothingRate (k := k) hk n e Cw := by
  intro N hN s hs hRpos
  rcases hclose hN s hs hRpos with ⟨wSurrogate, hWclose⟩
  refine ⟨wSurrogate, Cw / (returnsToStart (k := k) s : ℝ), hWclose, le_rfl⟩

/-- Build statewise scalar WR closeness by freezing the surrogate to
`W(empiricalParamStartTarget).toReal`. -/
lemma statewise_close_of_startTargetWClose
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ)
    (hcloseStart : HasStatewiseStartTargetWClose (k := k) hk n e Cw) :
    ∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
      s ∈ stateFinset k N →
        0 < returnsToStart (k := k) s →
          ∃ wSurrogate : ℝ,
            |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
              wSurrogate| ≤ Cw / (returnsToStart (k := k) s : ℝ) := by
  intro N hN s hs hRpos
  refine ⟨(W (k := k) (Nat.succ n) e (empiricalParamStartTarget (k := k) hk s)).toReal, ?_⟩
  exact hcloseStart hN s hs hRpos

/-- Package `HasStatewiseStartTargetWClose` into `HasCanonicalWRSmoothingRate`. -/
lemma hasCanonicalWRSmoothingRate_of_startTargetWClose
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ)
    (hcloseStart : HasStatewiseStartTargetWClose (k := k) hk n e Cw) :
    HasCanonicalWRSmoothingRate (k := k) hk n e Cw := by
  exact
    hasCanonicalWRSmoothingRate_of_statewise_close
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw)
      (statewise_close_of_startTargetWClose
        (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) hcloseStart)

/-- Coarse but explicit WR smoothing rate obtained directly from start-target row-`L1`
step control. -/
lemma hasCanonicalWRSmoothingRate_of_rowL1StartTarget
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) :
    HasCanonicalWRSmoothingRate (k := k) hk n e
      ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))) := by
  exact
    hasCanonicalWRSmoothingRate_of_startTargetWClose
      (k := k) (hk := hk) (n := n) (e := e)
      (Cw := ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))))
      (hasStatewiseStartTargetWClose_of_rowL1 (k := k) (hk := hk) (n := n) (e := e))



/-- Build `HasCanonicalWRSmoothingRate` from a statewise excursion-target witness
with explicit `O(1 / returnsToStart)` rates. -/
lemma hasCanonicalWRSmoothingRate_of_excursion_target_rates
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ)
    (hstate : HasStatewiseExcursionTargetRates (k := k) hk n e Cw) :
    HasCanonicalWRSmoothingRate (k := k) hk n e Cw := by
  intro N hN s hs hRpos
  rcases hstate hN s hs hRpos with
    ⟨elist, pref, target, Crepr, Cstep, hrepr, hstep, hrange, hCw⟩
  refine ⟨excursionsProb (k := k) target pref,
    (Crepr + (pref.length : ℝ) * Cstep) / (returnsToStart (k := k) s : ℝ), ?_, ?_⟩
  · exact
      wr_scalar_smoothing_rate_via_excursion_target
        (k := k) (hk := hk) (n := n) (e := e) (s := s)
        (elist := elist) (pref := pref) (target := target)
        (Crepr := Crepr) (Cstep := Cstep)
        hrepr hstep hrange
  · have hRnonneg : 0 ≤ (returnsToStart (k := k) s : ℝ) := by
      exact_mod_cast (Nat.zero_le (returnsToStart (k := k) s))
    exact div_le_div_of_nonneg_right hCw hRnonneg

/-- Scalar-surrogate WR closeness derived from excursion-target rates.

This is the direct "statewise-close" form used by the robust split-rate route. -/
lemma statewise_close_of_excursion_target_rates
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ)
    (hstate : HasStatewiseExcursionTargetRates (k := k) hk n e Cw) :
    ∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
      s ∈ stateFinset k N →
        0 < returnsToStart (k := k) s →
          ∃ wSurrogate : ℝ,
            |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
              wSurrogate| ≤ Cw / (returnsToStart (k := k) s : ℝ) := by
  intro N hN s hs hRpos
  rcases hstate hN s hs hRpos with
    ⟨elist, pref, target, Crepr, Cstep, hrepr, hstep, hrange, hCw⟩
  refine ⟨excursionsProb (k := k) target pref, ?_⟩
  have hscalar :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        excursionsProb (k := k) target pref| ≤
      (Crepr + (pref.length : ℝ) * Cstep) / (returnsToStart (k := k) s : ℝ) :=
    wr_scalar_smoothing_rate_via_excursion_target
      (k := k) (hk := hk) (n := n) (e := e) (s := s)
      (elist := elist) (pref := pref) (target := target)
      (Crepr := Crepr) (Cstep := Cstep)
      hrepr hstep hrange
  have hRnonneg : 0 ≤ (returnsToStart (k := k) s : ℝ) := by
    exact_mod_cast (Nat.zero_le (returnsToStart (k := k) s))
  have hrate :
      (Crepr + (pref.length : ℝ) * Cstep) / (returnsToStart (k := k) s : ℝ) ≤
        Cw / (returnsToStart (k := k) s : ℝ) :=
    div_le_div_of_nonneg_right hCw hRnonneg
  exact le_trans hscalar hrate

/-- Concrete statewise excursion-target witness from a WR representation-rate hypothesis:
choose `target = empiricalExcursionProb` and `Cstep = 0`. -/
lemma excursion_target_statewise_witness_of_wr_repr_rate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ)
    (hrepr :
      ∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
        s ∈ stateFinset k N →
          0 < returnsToStart (k := k) s →
            ∃ elist pref : ExcursionList k,
              ∃ Crepr : ℝ,
                |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
                  excursionWithReplacementProb (k := k) elist pref| ≤
                    Crepr / (returnsToStart (k := k) s : ℝ) ∧
                Crepr ≤ Cw) :
    ∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
      s ∈ stateFinset k N →
        0 < returnsToStart (k := k) s →
          ∃ elist pref : ExcursionList k,
            ∃ target : ExcursionType k → ℝ,
              ∃ Crepr Cstep : ℝ,
                |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
                  excursionWithReplacementProb (k := k) elist pref| ≤
                    Crepr / (returnsToStart (k := k) s : ℝ) ∧
                (∀ a ∈ pref,
                  |empiricalExcursionProb (k := k) elist a - target a| ≤
                    Cstep / (returnsToStart (k := k) s : ℝ)) ∧
                (∀ a ∈ pref, 0 ≤ target a ∧ target a ≤ 1) ∧
                Crepr + (pref.length : ℝ) * Cstep ≤ Cw := by
  intro N hN s hs hRpos
  rcases hrepr hN s hs hRpos with ⟨elist, pref, Crepr, hreprBound, hCrepr⟩
  refine ⟨elist, pref, empiricalExcursionProb (k := k) elist, Crepr, 0, hreprBound, ?_, ?_, ?_⟩
  · intro a ha
    have h0nonneg : (0 : ℝ) ≤ (0 : ℝ) / (returnsToStart (k := k) s : ℝ) := by
      positivity
    have habs :
        |empiricalExcursionProb (k := k) elist a - empiricalExcursionProb (k := k) elist a| = 0 := by
      simp
    rw [habs]
    exact h0nonneg
  · intro a ha
    have hnonneg :
        0 ≤ empiricalExcursionProb (k := k) elist a := by
      simpa [empiricalExcursionProb] using
        (probWeight_nonneg
          ((excursionMultiset (k := k) elist).count a)
          ((excursionMultiset (k := k) elist).card))
    have hle :
        empiricalExcursionProb (k := k) elist a ≤ 1 := by
      simpa [empiricalExcursionProb] using
        (probWeight_le_one
          ((excursionMultiset (k := k) elist).count a)
          ((excursionMultiset (k := k) elist).card)
          (Multiset.count_le_card _ _))
    exact ⟨hnonneg, hle⟩
  · simpa using hCrepr

/-- Package the concrete `target = empiricalExcursionProb`, `Cstep = 0`
statewise witness into `HasCanonicalWRSmoothingRate`. -/
lemma hasCanonicalWRSmoothingRate_of_statewise_wr_repr_rate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ)
    (hrepr :
      ∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
        s ∈ stateFinset k N →
          0 < returnsToStart (k := k) s →
            ∃ elist pref : ExcursionList k,
              ∃ Crepr : ℝ,
                |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
                  excursionWithReplacementProb (k := k) elist pref| ≤
                    Crepr / (returnsToStart (k := k) s : ℝ) ∧
                Crepr ≤ Cw) :
    HasCanonicalWRSmoothingRate (k := k) hk n e Cw := by
  apply hasCanonicalWRSmoothingRate_of_excursion_target_rates
    (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw)
  exact
    excursion_target_statewise_witness_of_wr_repr_rate
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) hrepr


/-- Layer 1 (constructive): turn a concrete fiber-trajectory family witness into
the statewise WR representation-rate witness shape consumed downstream. -/
lemma statewise_wr_repr_rate_of_fiber_trajectory_family
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ)
    (htraj : HasFiberTrajectoryWRReprRate (k := k) hk n e Cw) :
    ∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
      s ∈ stateFinset k N →
        0 < returnsToStart (k := k) s →
          ∃ elist pref : ExcursionList k,
            ∃ Crepr : ℝ,
              |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
                excursionWithReplacementProb (k := k) elist pref| ≤
                  Crepr / (returnsToStart (k := k) s : ℝ) ∧
              Crepr ≤ Cw := by
  intro N hN s hs hRpos
  rcases htraj hN s hs hRpos with ⟨xs, hxs, hW⟩
  have _hstate : stateOfTraj (k := k) xs = s := (Finset.mem_filter.1 hxs).2
  refine ⟨excursionListOfTraj (k := k) xs,
    (excursionListOfTraj (k := k) xs).take (prefixExcursionCount (k := k) hN xs),
    Cw, ?_, le_rfl⟩
  simpa using hW

/-- Layer 2 (constructive): package the fiber-trajectory family witness directly
into `HasCanonicalWRSmoothingRate`. -/
lemma hasCanonicalWRSmoothingRate_of_fiber_trajectory_family
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ)
    (htraj : HasFiberTrajectoryWRReprRate (k := k) hk n e Cw) :
    HasCanonicalWRSmoothingRate (k := k) hk n e Cw := by
  apply hasCanonicalWRSmoothingRate_of_statewise_wr_repr_rate
    (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw)
  exact
    statewise_wr_repr_rate_of_fiber_trajectory_family
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) htraj

/-- Directly feed a constructive fiber-trajectory WR witness plus WOR transport
into the split-rate residual constructor. -/
lemma hasExcursionResidualBoundRate_of_fiberTrajectorySplitRates
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw Cpc : ℝ)
    (htraj : HasFiberTrajectoryWRReprRate (k := k) hk n e Cw)
    (hWOR : HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    HasExcursionResidualBoundRate (k := k) hk n e (Cw + Cpc) := by
  have hWR :
      HasCanonicalWRSmoothingRate (k := k) hk n e Cw :=
    hasCanonicalWRSmoothingRate_of_fiber_trajectory_family
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) htraj
  intro N hN s hs hRpos
  exact
    hasExcursionResidualBoundRate_of_splitRates
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc)
      hWR hWOR hN s hs hRpos

/-- Family-level residual-rate constructor from fiber-trajectory split-rate data. -/
theorem hasExcursionResidualBoundRateAll_of_fiberTrajectorySplitRatesAll
    (hsplitTrajAll :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        ∃ Cw Cpc : ℝ,
          0 ≤ Cw ∧ 0 ≤ Cpc ∧
          HasFiberTrajectoryWRReprRate (k := k) hk n e Cw ∧
          HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro hk n e
  rcases hsplitTrajAll hk n e with ⟨Cw, Cpc, hCw, hCpc, htraj, hWOR⟩
  refine ⟨Cw + Cpc, add_nonneg hCw hCpc, ?_⟩
  exact
    hasExcursionResidualBoundRate_of_fiberTrajectorySplitRates
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc)
      htraj hWOR

/-- Fixed-`k` family-level residual-rate constructor from fiber-trajectory split-rate data. -/
theorem hasExcursionResidualBoundRateAll_fixed_of_fiberTrajectorySplitRatesAll
    (hk : 0 < k)
    (hsplitTrajAll :
      ∀ n : ℕ, ∀ e : MarkovState k,
        ∃ Cw Cpc : ℝ,
          0 ≤ Cw ∧ 0 ≤ Cpc ∧
          HasFiberTrajectoryWRReprRate (k := k) hk n e Cw ∧
          HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro n e
  rcases hsplitTrajAll n e with ⟨Cw, Cpc, hCw, hCpc, htraj, hWOR⟩
  refine ⟨Cw + Cpc, add_nonneg hCw hCpc, ?_⟩
  exact
    hasExcursionResidualBoundRate_of_fiberTrajectorySplitRates
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc)
      htraj hWOR

theorem hasCanonicalWRSmoothingRate_exists_of_statewise_wr_repr_rate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hwitness :
      ∃ Cw : ℝ, 0 ≤ Cw ∧
        (∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
          s ∈ stateFinset k N →
            0 < returnsToStart (k := k) s →
              ∃ elist pref : ExcursionList k,
                ∃ Crepr : ℝ,
                  |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
                    excursionWithReplacementProb (k := k) elist pref| ≤
                      Crepr / (returnsToStart (k := k) s : ℝ) ∧
                  Crepr ≤ Cw)) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ HasCanonicalWRSmoothingRate (k := k) hk n e Cw := by
  rcases hwitness with ⟨Cw, hCw, hrepr⟩
  refine ⟨Cw, hCw, ?_⟩
  exact
    hasCanonicalWRSmoothingRate_of_statewise_wr_repr_rate
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) hrepr

/-- Fixed-`k` family version of `hasCanonicalWRSmoothingRate_exists_of_statewise_wr_repr_rate`. -/
theorem hasCanonicalWRSmoothingRateAll_fixed_of_statewise_wr_repr_rateAll
    (hk : 0 < k)
    (hwitnessAll :
      ∀ n : ℕ, ∀ e : MarkovState k,
        ∃ Cw : ℝ, 0 ≤ Cw ∧
          (∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
            s ∈ stateFinset k N →
              0 < returnsToStart (k := k) s →
                ∃ elist pref : ExcursionList k,
                  ∃ Crepr : ℝ,
                    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
                      excursionWithReplacementProb (k := k) elist pref| ≤
                        Crepr / (returnsToStart (k := k) s : ℝ) ∧
                    Crepr ≤ Cw)) :
    ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cw : ℝ, 0 ≤ Cw ∧ HasCanonicalWRSmoothingRate (k := k) hk n e Cw := by
  intro n e
  exact
    hasCanonicalWRSmoothingRate_exists_of_statewise_wr_repr_rate
      (k := k) (hk := hk) (n := n) (e := e) (hwitness := hwitnessAll n e)
/-- Robust route: build the residual-rate bound from a scalar statewise WR surrogate
and a canonical WOR transport rate. -/
lemma hasExcursionResidualBoundRate_of_statewise_close_and_worTransport
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw Cpc : ℝ)
    (hclose :
      ∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
        s ∈ stateFinset k N →
          0 < returnsToStart (k := k) s →
            ∃ wSurrogate : ℝ,
              |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
                wSurrogate| ≤ Cw / (returnsToStart (k := k) s : ℝ))
    (hWOR : HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    HasExcursionResidualBoundRate (k := k) hk n e (Cw + Cpc) := by
  have hWR : HasCanonicalWRSmoothingRate (k := k) hk n e Cw :=
    hasCanonicalWRSmoothingRate_of_statewise_close
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) hclose
  intro N hN s hs hRpos
  exact
    hasExcursionResidualBoundRate_of_splitRates
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc)
      hWR hWOR hN s hs hRpos

/-- Robust split-rate constructor using the start-target scalar WR crux directly. -/
lemma hasExcursionResidualBoundRate_of_startTargetWClose_and_worTransport
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw Cpc : ℝ)
    (hcloseStart : HasStatewiseStartTargetWClose (k := k) hk n e Cw)
    (hWOR : HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    HasExcursionResidualBoundRate (k := k) hk n e (Cw + Cpc) := by
  exact
    hasExcursionResidualBoundRate_of_statewise_close_and_worTransport
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc)
      (statewise_close_of_startTargetWClose
        (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) hcloseStart)
      hWOR

/-- Row-`L1` start-target WR rate + WOR transport packaged directly into a
residual-rate bound. -/
lemma hasExcursionResidualBoundRate_of_rowL1StartTarget_and_worTransport
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cpc : ℝ)
    (hWOR :
      HasCanonicalWORTransportRate (k := k) hk n e
        ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
        Cpc) :
    HasExcursionResidualBoundRate (k := k) hk n e
      (((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))) + Cpc) := by
  exact
    hasExcursionResidualBoundRate_of_startTargetWClose_and_worTransport
      (k := k) (hk := hk) (n := n) (e := e)
      (Cw := ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))))
      (Cpc := Cpc)
      (hasStatewiseStartTargetWClose_of_rowL1 (k := k) (hk := hk) (n := n) (e := e))
      hWOR

/-- Robust split-rate constructor from excursion-target WR rates and WOR transport. -/
lemma hasExcursionResidualBoundRate_of_excursionTargetRates_and_worTransport
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw Cpc : ℝ)
    (hstate : HasStatewiseExcursionTargetRates (k := k) hk n e Cw)
    (hWOR : HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    HasExcursionResidualBoundRate (k := k) hk n e (Cw + Cpc) := by
  have hclose :
      ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
        s ∈ stateFinset k N →
          0 < returnsToStart (k := k) s →
            ∃ wSurrogate : ℝ,
              |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
                wSurrogate| ≤ Cw / (returnsToStart (k := k) s : ℝ) :=
    statewise_close_of_excursion_target_rates
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) hstate
  intro N hN s hs hRpos
  exact
    hasExcursionResidualBoundRate_of_statewise_close_and_worTransport
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc)
      hclose hWOR hN s hs hRpos

/-- Explicit-pattern route: if a pattern surrogate rate is already available,
it directly yields the statewise residual-rate bound. -/
lemma hasExcursionResidualBoundRate_of_explicitPatternSurrogateRate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (C : ℝ)
    (halign : HasPatternSurrogateResidualAlignmentRate (k := k) hk n e C) :
    HasExcursionResidualBoundRate (k := k) hk n e C := by
  exact
    hasExcursionResidualBoundRate_of_patternSurrogateResidualAlignmentRate
      (k := k) (hk := hk) (n := n) (e := e) (C := C) halign
lemma hasCanonicalWRSmoothingRate_zero
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) :
    HasCanonicalWRSmoothingRate (k := k) hk n e 0 := by
  intro N hN s hs hRpos
  refine ⟨(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal, 0, ?_, ?_⟩
  · simp
  · have hnonneg : (0 : ℝ) ≤ 0 / (returnsToStart (k := k) s : ℝ) := by
      positivity
    exact hnonneg

/-- Build WOR transport directly from a pattern-level WR/WOR discrepancy rate.

This keeps the remaining bottleneck at one explicit summed pattern inequality,
without requiring the stronger semantic `HasExcursionBiapproxCore` package. -/
lemma hasCanonicalWORTransportRate_of_patternWRWORRate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw Cdf : ℝ)
    (hwrwor : HasPatternWRWORRate (k := k) hk n e Cdf) :
    HasCanonicalWORTransportRate (k := k) hk n e Cw (Cw + Cdf) := by
  intro N hN s hs hRpos wSurrogate hWclose
  refine ⟨(Cw + Cdf) / (returnsToStart (k := k) s : ℝ), ?_, le_rfl⟩
  exact
    surrogate_to_wor_bound
      (k := k) (hk := hk) (n := n) (e := e)
      (hN := hN) (s := s)
      (wSurrogate := wSurrogate) (Cw := Cw) (Cdf := Cdf)
      hWclose
      (hwrwor hN s hs hRpos)

/-- Build a direct WR/WOR pattern discrepancy rate from split-rate assumptions. -/
lemma hasPatternWRWORRate_of_splitRates
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw Cpc : ℝ)
    (hWR : HasCanonicalWRSmoothingRate (k := k) hk n e Cw)
    (hWOR : HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    HasPatternWRWORRate (k := k) hk n e (Cw + Cpc) := by
  intro N hN s hs hRpos
  rcases hWR hN s hs hRpos with ⟨wSurrogate, εW, hWclose, hεW⟩
  have hWcloseCw :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        wSurrogate| ≤ Cw / (returnsToStart (k := k) s : ℝ) :=
    le_trans hWclose hεW
  rcases hWOR hN s hs hRpos wSurrogate hWcloseCw with ⟨εPC, hq_wor, hεPC⟩
  let q : ExcursionList k → ℝ := canonicalWRSurrogateMass (k := k) n e wSurrogate
  have hwr_q :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal - q p| ≤ εW := by
    simpa [q] using
      (sum_abs_wrPatternMass_toReal_sub_canonicalWRSurrogateMass_le
        (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
        (wSurrogate := wSurrogate) (εW := εW) hWclose)
  have hsum :
      (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
        εW + εPC := by
    exact
      sum_abs_wr_wor_patternMass_toReal_le_of_surrogate
        (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s)
        (q := q) (εW := εW) (εPC := εPC) hwr_q (by simpa [q] using hq_wor)
  calc
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤ εW + εPC := hsum
    _ ≤ Cw / (returnsToStart (k := k) s : ℝ) +
          Cpc / (returnsToStart (k := k) s : ℝ) := add_le_add hεW hεPC
    _ = (Cw + Cpc) / (returnsToStart (k := k) s : ℝ) := by ring

lemma hasCanonicalWORTransportRate_of_biapproxCore
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw : ℝ)
    (hcore : HasExcursionBiapproxCore (k := k) hk n e) :
    HasCanonicalWORTransportRate (k := k) hk n e Cw
      (Cw + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) := by
  intro N hN s hs hRpos wSurrogate hWclose
  refine ⟨(Cw + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
      (returnsToStart (k := k) s : ℝ), ?_, ?_⟩
  · exact
      wor_transport_rate_canonicalWRSurrogate
        (k := k) (hk := hk) (n := n) (e := e)
        (hN := hN) (s := s) (hs := hs)
        (hcore := hcore hN s hs)
        (wSurrogate := wSurrogate) (Cw := Cw)
        hWclose
  · simp

/-- BEST-side pattern discrepancy witness:
from the semantic core package, get a direct WR/WOR pattern-sum rate. -/
lemma hasPatternWRWORRate_of_biapproxCore
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hcore : HasExcursionBiapproxCore (k := k) hk n e) :
    HasPatternWRWORRate (k := k) hk n e
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) := by
  intro N hN s hs hRpos
  let wSurrogate : ℝ :=
    (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
  let q : ExcursionList k → ℝ :=
    canonicalWRSurrogateMass (k := k) n e wSurrogate
  have hwr_q :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal - q p| ≤ 0 := by
    simpa [q, wSurrogate] using
      (wr_smoothing_rate_canonicalWRSurrogate_exact
        (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s))
  have hq_wor :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |q p - (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
    simpa [q, wSurrogate] using
      (wor_transport_rate_canonicalWRSurrogate_exact
        (k := k) (hk := hk) (n := n) (e := e)
        (hN := hN) (s := s) (hs := hs) (hcore := hcore hN s hs))
  have hsum :=
    sum_abs_wr_wor_patternMass_toReal_le_of_surrogate
      (k := k) (hk := hk) (n := n) (e := e) (hN := hN) (s := s)
      (q := q) (εW := 0)
      (εPC := (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ))
      hwr_q hq_wor
  simpa using hsum

/-- Fixed-parameter BEST representative bound implies a direct WR/WOR
pattern discrepancy rate witness. -/
lemma hasPatternWRWORRate_of_bestReprBound
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hreprBound : HasBestReprBound (k := k) hk n e) :
    HasPatternWRWORRate (k := k) hk n e
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) := by
  exact
    hasPatternWRWORRate_of_biapproxCore
      (k := k) (hk := hk) (n := n) (e := e)
      (hcore := hasExcursionBiapproxCore_of_bestReprBound
        (k := k) (hk := hk) (n := n) (e := e) hreprBound)

/-- Fixed-parameter positive-return pattern-collision consequence of a BEST
representative bound witness. -/
lemma hasPatternCollisionPos_of_bestReprBound
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hreprBound : HasBestReprBound (k := k) hk n e) :
    ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
      s ∈ stateFinset k N →
        0 < returnsToStart (k := k) s →
          (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
            |(wrPatternMass (k := k) hk n e s p).toReal -
              (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
            (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
              (returnsToStart (k := k) s : ℝ) := by
  exact
    hasPatternWRWORRate_of_bestReprBound
      (k := k) (hk := hk) (n := n) (e := e) hreprBound

lemma hasExcursionResidualBoundRate_of_worTransportRate
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cpc : ℝ)
    (hWOR : HasCanonicalWORTransportRate (k := k) hk n e 0 Cpc) :
    HasExcursionResidualBoundRate (k := k) hk n e Cpc := by
  have hWR0 : HasCanonicalWRSmoothingRate (k := k) hk n e 0 :=
    hasCanonicalWRSmoothingRate_zero (k := k) (hk := hk) (n := n) (e := e)
  have hsplit :
      HasExcursionResidualBoundRate (k := k) hk n e (0 + Cpc) :=
    hasExcursionResidualBoundRate_of_splitRates
      (k := k) (hk := hk) (n := n) (e := e) (Cw := 0) (Cpc := Cpc)
      hWR0 hWOR
  intro N hN s hs hRpos
  rcases hsplit hN s hs hRpos with ⟨εW, εPC, hWnonneg, hPCnonneg, hrate, hbound⟩
  refine ⟨εW, εPC, hWnonneg, hPCnonneg, ?_, hbound⟩
  simpa [zero_add] using hrate

lemma hasExcursionResidualBoundRate_of_biapproxCore
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hcore : HasExcursionBiapproxCore (k := k) hk n e) :
    HasExcursionResidualBoundRate (k := k) hk n e
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) := by
  intro N hN s hs hRpos
  let C : ℝ := 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)
  refine ⟨C / (returnsToStart (k := k) s : ℝ), 0, ?_, by positivity, ?_, ?_⟩
  · exact div_nonneg (by positivity)
      (by exact_mod_cast (Nat.zero_le (returnsToStart (k := k) s)))
  · simp [C]
  · have hbound :=
      excursion_bound_from_decomposition
        (k := k) (hk := hk) (n := n) (e := e)
        (hN := hN) (s := s) (hs := hs) (hcore := hcore hN s hs)
    simpa [C] using hbound


lemma hasExcursionResidualBoundRate_of_biapproxCore_via_robust
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    (hcore : HasExcursionBiapproxCore (k := k) hk n e) :
    HasExcursionResidualBoundRate (k := k) hk n e
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) := by
  have hWOR :
      HasCanonicalWORTransportRate (k := k) hk n e 0
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) := by
    have hWORraw :
        HasCanonicalWORTransportRate (k := k) hk n e 0
          (0 + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) :=
      hasCanonicalWORTransportRate_of_biapproxCore
        (k := k) (hk := hk) (n := n) (e := e) (Cw := 0) hcore
    intro N hN s hs hRpos wSurrogate hWclose
    simpa [zero_add] using hWORraw hN s hs hRpos wSurrogate hWclose
  intro N hN s hs hRpos
  exact
    (hasExcursionResidualBoundRate_of_worTransportRate
      (k := k) (hk := hk) (n := n) (e := e)
      (Cpc := 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) hWOR)
      hN s hs hRpos



theorem hasExcursionResidualBoundRateAll_of_biapproxCoreAll
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro hk n e
  refine ⟨4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ), by positivity, ?_⟩
  exact hasExcursionResidualBoundRate_of_biapproxCore
    (k := k) (hk := hk) (n := n) (e := e) (hcore := hcoreAll hk n e)


theorem hasExcursionResidualBoundRateAll_of_biapproxCoreAll_fixed
    (hk : 0 < k)
    (hcoreAll : ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro n e
  refine ⟨4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ), by positivity, ?_⟩
  exact hasExcursionResidualBoundRate_of_biapproxCore
    (k := k) (hk := hk) (n := n) (e := e) (hcore := hcoreAll n e)

/-- Family-level direct pattern-rate witness extracted from BEST-side core packages. -/
theorem hasPatternWRWORRateAll_of_biapproxCoreAll
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf := by
  intro hk n e
  refine ⟨4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ), by positivity, ?_⟩
  exact
    hasPatternWRWORRate_of_biapproxCore
      (k := k) (hk := hk) (n := n) (e := e) (hcore := hcoreAll hk n e)

/-- Convert the BEST representative-counting bound family directly into a
family-level WR/WOR pattern discrepancy rate witness. -/
theorem hasPatternWRWORRateAll_of_best_repr_boundAll
    (hreprBoundAll :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
          s ∈ stateFinset k N →
            let P := excursionPatternSet (k := k) (hN := hN) e s
            let repr : Multiset (ExcursionType k) → ExcursionList k := fun mset =>
              if hm : ∃ p ∈ P, Multiset.ofList p = mset then (Classical.choose hm) else []
            (∑ mset ∈ P.image Multiset.ofList,
              (((P.filter (fun p => Multiset.ofList p = mset)).card : ℝ) *
                |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
                  (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal|))
              ≤
                (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
                  (returnsToStart (k := k) s : ℝ)) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf := by
  have hcoreAll :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        HasExcursionBiapproxCore (k := k) hk n e :=
    hasExcursionBiapproxCoreAll_of_best_repr_boundAll
      (k := k) hreprBoundAll
  exact hasPatternWRWORRateAll_of_biapproxCoreAll (k := k) hcoreAll

/-- Alias-wrapper version of `hasPatternWRWORRateAll_of_best_repr_boundAll`. -/
theorem hasPatternWRWORRateAll_of_bestReprBoundAll
    (hreprBoundAll : HasBestReprBoundAll (k := k)) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf := by
  exact hasPatternWRWORRateAll_of_best_repr_boundAll
    (k := k) hreprBoundAll

/-- Convert direct pattern-collision + zero-return obligations into a
family-level WR/WOR pattern discrepancy rate witness. -/
@[deprecated "Legacy collision-only constructor. Prefer hasPatternWRWORRateAll_of_rowL1StartTarget_and_worTransportAll."
  (since := "2026-02-17")]
theorem hasPatternWRWORRateAll_of_patternCollision_and_zeroCaseAll
    (hposAll : HasPatternCollisionPosAll (k := k))
    (hzeroAll : HasPatternCollisionZeroAll (k := k)) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf := by
  have hcoreAll :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        HasExcursionBiapproxCore (k := k) hk n e :=
    hasExcursionBiapproxCoreAll_of_patternCollision_and_zeroCaseAll
      (k := k) hposAll hzeroAll
  exact hasPatternWRWORRateAll_of_biapproxCoreAll (k := k) hcoreAll

/-- Convert the positive-return pattern-collision family directly into
`HasPatternWRWORRate` witnesses (no zero-return branch needed). -/
@[deprecated "Legacy collision-only constructor. Prefer hasPatternWRWORRateAll_of_rowL1StartTarget_and_worTransportAll."
  (since := "2026-02-17")]
theorem hasPatternWRWORRateAll_of_patternCollisionPosAll
    (hposAll : HasPatternCollisionPosAll (k := k)) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf := by
  intro hk n e
  refine ⟨4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ), by positivity, ?_⟩
  intro N hN s hs hRpos
  simpa using hposAll hk n e hN s hs hRpos

/-- Reduction principle: to build family-level pattern WR/WOR rates, it is
enough to prove them on realizable short-horizon states `e ∈ stateFinset k (n+1)`.
Unrealizable `e` are discharged by the zero-rate lemma. -/
theorem hasPatternWRWORRateAll_of_realizable_shortState
    (hreal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf := by
  intro hk n e
  by_cases he : e ∈ stateFinset k (Nat.succ n)
  · exact hreal hk n e he
  · refine ⟨0, le_rfl, ?_⟩
    exact
      hasPatternWRWORRate_zero_of_not_mem_shortStateFinset
        (k := k) (hk := hk) (n := n) (e := e) he

/-- Realizable-short-state constructor specialized to BEST representative bounds:
to build family-level `HasPatternWRWORRate` witnesses, it suffices to provide
`HasBestReprBound` on realizable short states. -/
theorem hasPatternWRWORRateAll_of_bestReprBound_on_realizable_shortState
    (hrealBest :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          HasBestReprBound (k := k) hk n e) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf := by
  apply hasPatternWRWORRateAll_of_realizable_shortState (k := k)
  intro hk n e he
  refine
    ⟨4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ),
      by positivity, ?_⟩
  exact
    hasPatternWRWORRate_of_bestReprBound
      (k := k) (hk := hk) (n := n) (e := e)
      (hrealBest hk n e he)

/-- Realizable-short-state WOR-transport constructor from BEST representative
bounds, aligned with the rowL1 WR smoothing route (`Cw = (n+1)k²`). -/
theorem hasCanonicalWORTransportRate_on_realizable_shortState_of_bestReprBound_rowL1StartTarget
    (hrealBest :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          HasBestReprBound (k := k) hk n e) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      e ∈ stateFinset k (Nat.succ n) →
        ∃ Cpc : ℝ, 0 ≤ Cpc ∧
          HasCanonicalWORTransportRate (k := k) hk n e
            ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
            Cpc := by
  intro hk n e he
  let Cw : ℝ := (Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))
  have hwrwor :
      HasPatternWRWORRate (k := k) hk n e
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) :=
    hasPatternWRWORRate_of_bestReprBound
      (k := k) (hk := hk) (n := n) (e := e)
      (hrealBest hk n e he)
  have hWOR :
      HasCanonicalWORTransportRate (k := k) hk n e Cw
        (Cw + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) :=
    hasCanonicalWORTransportRate_of_patternWRWORRate
      (k := k) (hk := hk) (n := n) (e := e)
      (Cw := Cw)
      (Cdf := 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ))
      hwrwor
  refine ⟨Cw + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ), by positivity, hWOR⟩

/-- Extract positive-return pattern-collision obligations from a BEST-side
core package family. -/
theorem hasPatternCollisionPosAll_of_biapproxCoreAll
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e) :
    HasPatternCollisionPosAll (k := k) := by
  intro hk n e N hN s hs hRpos
  have hwrwor :
      HasPatternWRWORRate (k := k) hk n e
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) :=
    hasPatternWRWORRate_of_biapproxCore
      (k := k) (hk := hk) (n := n) (e := e) (hcore := hcoreAll hk n e)
  simpa using hwrwor hN s hs hRpos

/-- Extract positive-return pattern-collision obligations directly from the
BEST representative bound family. -/
theorem hasPatternCollisionPosAll_of_best_repr_boundAll
    (hreprBoundAll :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
          s ∈ stateFinset k N →
            let P := excursionPatternSet (k := k) (hN := hN) e s
            let repr : Multiset (ExcursionType k) → ExcursionList k := fun mset =>
              if hm : ∃ p ∈ P, Multiset.ofList p = mset then (Classical.choose hm) else []
            (∑ mset ∈ P.image Multiset.ofList,
              (((P.filter (fun p => Multiset.ofList p = mset)).card : ℝ) *
                |(wrPatternMass (k := k) hk n e s (repr mset)).toReal -
                  (worPatternMass (k := k) (hN := hN) e s (repr mset)).toReal|))
              ≤
                (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
                  (returnsToStart (k := k) s : ℝ)) :
    HasPatternCollisionPosAll (k := k) := by
  have hcoreAll :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        HasExcursionBiapproxCore (k := k) hk n e :=
    hasExcursionBiapproxCoreAll_of_best_repr_boundAll
      (k := k) hreprBoundAll
  exact hasPatternCollisionPosAll_of_biapproxCoreAll (k := k) hcoreAll

/-- Alias-wrapper version of `hasPatternCollisionPosAll_of_best_repr_boundAll`. -/
theorem hasPatternCollisionPosAll_of_bestReprBoundAll
    (hreprBoundAll : HasBestReprBoundAll (k := k)) :
    HasPatternCollisionPosAll (k := k) := by
  exact hasPatternCollisionPosAll_of_best_repr_boundAll
    (k := k) hreprBoundAll

/-- Even when restricted to realizable short states, a biapprox-core family
implies the legacy positive-return collision obligations. -/
theorem hasPatternCollisionPosAll_of_biapproxCore_on_realizable_shortState
    (hcoreReal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          HasExcursionBiapproxCore (k := k) hk n e) :
    HasPatternCollisionPosAll (k := k) := by
  intro hk n e N hN s hs hRpos
  by_cases he : e ∈ stateFinset k (Nat.succ n)
  · have hwrwor :
      HasPatternWRWORRate (k := k) hk n e
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) :=
      hasPatternWRWORRate_of_biapproxCore
        (k := k) (hk := hk) (n := n) (e := e)
        (hcoreReal hk n e he)
    simpa using hwrwor hN s hs hRpos
  · have hwrwor0 :
      HasPatternWRWORRate (k := k) hk n e 0 :=
      hasPatternWRWORRate_zero_of_not_mem_shortStateFinset
        (k := k) (hk := hk) (n := n) (e := e) he
    have h0 :
        (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
          (0 : ℝ) / (returnsToStart (k := k) s : ℝ) :=
      hwrwor0 hN s hs hRpos
    have h0_le_collision :
        (0 : ℝ) / (returnsToStart (k := k) s : ℝ) ≤
          (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
            (returnsToStart (k := k) s : ℝ) := by
      have hcollision_nonneg :
          0 ≤
            (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
              (returnsToStart (k := k) s : ℝ) := by positivity
      simpa using hcollision_nonneg
    exact le_trans h0 h0_le_collision

theorem hasExcursionResidualBoundRateAll_of_splitRatesAll
    (hsplitAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cw Cpc : ℝ,
        0 ≤ Cw ∧ 0 ≤ Cpc ∧
        HasCanonicalWRSmoothingRate (k := k) hk n e Cw ∧
        HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro hk n e
  rcases hsplitAll hk n e with ⟨Cw, Cpc, hCw, hCpc, hWR, hWOR⟩
  refine ⟨Cw + Cpc, add_nonneg hCw hCpc, ?_⟩
  exact hasExcursionResidualBoundRate_of_splitRates
    (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc)
    hWR hWOR

/-- Family-level direct pattern WR/WOR discrepancy rates from split-rate
assumptions. -/
theorem hasPatternWRWORRateAll_of_splitRatesAll
    (hsplitAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cw Cpc : ℝ,
        0 ≤ Cw ∧ 0 ≤ Cpc ∧
        HasCanonicalWRSmoothingRate (k := k) hk n e Cw ∧
        HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf := by
  intro hk n e
  rcases hsplitAll hk n e with ⟨Cw, Cpc, hCw, hCpc, hWR, hWOR⟩
  refine ⟨Cw + Cpc, add_nonneg hCw hCpc, ?_⟩
  exact
    hasPatternWRWORRate_of_splitRates
      (k := k) (hk := hk) (n := n) (e := e)
      (Cw := Cw) (Cpc := Cpc) hWR hWOR

theorem hasExcursionResidualBoundRateAll_of_statewiseCloseSplitRatesAll
    (hsplitCloseAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cw Cpc : ℝ,
        0 ≤ Cw ∧ 0 ≤ Cpc ∧
        (∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
          s ∈ stateFinset k N →
            0 < returnsToStart (k := k) s →
              ∃ wSurrogate : ℝ,
                |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
                  wSurrogate| ≤ Cw / (returnsToStart (k := k) s : ℝ)) ∧
        HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro hk n e
  rcases hsplitCloseAll hk n e with ⟨Cw, Cpc, hCw, hCpc, hclose, hWOR⟩
  refine ⟨Cw + Cpc, add_nonneg hCw hCpc, ?_⟩
  exact
    hasExcursionResidualBoundRate_of_statewise_close_and_worTransport
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc)
      hclose hWOR

theorem hasExcursionResidualBoundRateAll_of_rowL1StartTarget_and_worTransportAll
    (hWORAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cpc : ℝ, 0 ≤ Cpc ∧
        HasCanonicalWORTransportRate (k := k) hk n e
          ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
          Cpc) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro hk n e
  rcases hWORAll hk n e with ⟨Cpc, hCpc, hWOR⟩
  refine
    ⟨((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))) + Cpc,
      add_nonneg (by positivity) hCpc, ?_⟩
  exact
    hasExcursionResidualBoundRate_of_rowL1StartTarget_and_worTransport
      (k := k) (hk := hk) (n := n) (e := e) (Cpc := Cpc) hWOR

/-- Robust all-states constructor from:
`rowL1` WR smoothing + WOR transport rates, yielding direct pattern WR/WOR rates. -/
theorem hasPatternWRWORRateAll_of_rowL1StartTarget_and_worTransportAll
    (hWORAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cpc : ℝ, 0 ≤ Cpc ∧
        HasCanonicalWORTransportRate (k := k) hk n e
          ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
          Cpc) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf := by
  intro hk n e
  rcases hWORAll hk n e with ⟨Cpc, hCpc, hWOR⟩
  let Cw : ℝ := (Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))
  have hWR :
      HasCanonicalWRSmoothingRate (k := k) hk n e Cw :=
    hasCanonicalWRSmoothingRate_of_rowL1StartTarget
      (k := k) (hk := hk) (n := n) (e := e)
  refine ⟨Cw + Cpc, add_nonneg (by positivity) hCpc, ?_⟩
  exact
    hasPatternWRWORRate_of_splitRates
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc) hWR hWOR

/-- Realizable-short-state constructor from:
`rowL1` WR smoothing + WOR transport rates on realizable short states only. -/
theorem hasPatternWRWORRate_on_realizable_shortState_of_rowL1StartTarget_and_worTransport
    (hWORReal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          ∃ Cpc : ℝ, 0 ≤ Cpc ∧
            HasCanonicalWORTransportRate (k := k) hk n e
              ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
              Cpc) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      e ∈ stateFinset k (Nat.succ n) →
        ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf := by
  intro hk n e he
  rcases hWORReal hk n e he with ⟨Cpc, hCpc, hWOR⟩
  let Cw : ℝ := (Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))
  have hWR :
      HasCanonicalWRSmoothingRate (k := k) hk n e Cw :=
    hasCanonicalWRSmoothingRate_of_rowL1StartTarget
      (k := k) (hk := hk) (n := n) (e := e)
  refine ⟨Cw + Cpc, add_nonneg (by positivity) hCpc, ?_⟩
  exact
    hasPatternWRWORRate_of_splitRates
      (k := k) (hk := hk) (n := n) (e := e)
      (Cw := Cw) (Cpc := Cpc) hWR hWOR

/-- Realizable-short-state WOR-transport constructor from direct pattern WR/WOR
rate witnesses, aligned with the rowL1 WR smoothing choice `Cw = (n+1)k²`. -/
theorem hasCanonicalWORTransportRate_on_realizable_shortState_of_patternWRWORRate_rowL1StartTarget
    (hwrworReal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      e ∈ stateFinset k (Nat.succ n) →
        ∃ Cpc : ℝ, 0 ≤ Cpc ∧
          HasCanonicalWORTransportRate (k := k) hk n e
            ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
            Cpc := by
  intro hk n e he
  rcases hwrworReal hk n e he with ⟨Cdf, hCdf, hwrwor⟩
  let Cw : ℝ := (Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))
  refine ⟨Cw + Cdf, add_nonneg (by positivity) hCdf, ?_⟩
  exact
    hasCanonicalWORTransportRate_of_patternWRWORRate
      (k := k) (hk := hk) (n := n) (e := e)
      (Cw := Cw) (Cdf := Cdf) hwrwor

/-- Realizable-short-state WOR-transport constructor from a two-regime direct
pattern estimate:
- small-`R` is handled universally by `sum_abs_wr_wor_patternMass_toReal_le_two`,
- large-`R` is supplied by `hlargeReal`.

This keeps the remaining quantitative crux localized to the large-`R` branch. -/
theorem hasCanonicalWORTransportRate_on_realizable_shortState_of_largeR_patternRate_rowL1StartTarget
    (hlargeReal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          ∃ Clarge : ℝ, 0 ≤ Clarge ∧
            (∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
              s ∈ stateFinset k N →
                0 < returnsToStart (k := k) s →
                (4 * (Nat.succ n) * (Nat.succ n)) < returnsToStart (k := k) s →
                  (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
                    |(wrPatternMass (k := k) hk n e s p).toReal -
                      (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
                    Clarge / (returnsToStart (k := k) s : ℝ))) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      e ∈ stateFinset k (Nat.succ n) →
        ∃ Cpc : ℝ, 0 ≤ Cpc ∧
          HasCanonicalWORTransportRate (k := k) hk n e
            ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
            Cpc := by
  intro hk n e he
  rcases hlargeReal hk n e he with ⟨Clarge, hClarge, hlarge⟩
  let R0 : ℕ := 4 * (Nat.succ n) * (Nat.succ n)
  let Cdf : ℝ := max (2 * (R0 : ℝ)) Clarge
  have hwrwor :
      HasPatternWRWORRate (k := k) hk n e Cdf :=
    hasPatternWRWORRate_of_smallR_largeR
      (k := k) (hk := hk) (n := n) (e := e)
      (R0 := R0) (Clarge := Clarge)
      (by
        intro N hN s hs hRpos hRlarge
        exact hlarge hN s hs hRpos (by simpa [R0] using hRlarge))
  let Cw : ℝ := (Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))
  have hCdf_nonneg : 0 ≤ Cdf := by
    have hleft_nonneg : 0 ≤ 2 * (R0 : ℝ) := by positivity
    exact le_trans hleft_nonneg (le_max_left (2 * (R0 : ℝ)) Clarge)
  refine ⟨Cw + Cdf, add_nonneg (by positivity) hCdf_nonneg, ?_⟩
  exact
    hasCanonicalWORTransportRate_of_patternWRWORRate
      (k := k) (hk := hk) (n := n) (e := e)
      (Cw := Cw) (Cdf := Cdf) hwrwor

/-- Realizable-short-state large-`R` canonical-surrogate witness, reduced from a
direct large-`R` WR/WOR pattern-rate family.

This removes any dependency on `HasExcursionBiapproxCore` at this interface
boundary: the only required input is a direct large-`R` WR/WOR pattern bound. -/
theorem hasCanonicalWRSurrogateLargeR_on_realizable_shortState_of_largeR_patternRate
    (hlargeReal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          ∃ Clarge : ℝ, 0 ≤ Clarge ∧
            (∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
              s ∈ stateFinset k N →
                0 < returnsToStart (k := k) s →
                (4 * (Nat.succ n) * (Nat.succ n)) < returnsToStart (k := k) s →
                  (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
                    |(wrPatternMass (k := k) hk n e s p).toReal -
                      (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
                    Clarge / (returnsToStart (k := k) s : ℝ))) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      e ∈ stateFinset k (Nat.succ n) →
        ∃ Clarge : ℝ, 0 ≤ Clarge ∧
          (∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
            s ∈ stateFinset k N →
              0 < returnsToStart (k := k) s →
              (4 * (Nat.succ n) * (Nat.succ n)) < returnsToStart (k := k) s →
                (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
                  |canonicalWRSurrogateMass (k := k) n e
                      ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal) p -
                    (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
                  Clarge / (returnsToStart (k := k) s : ℝ)) := by
  intro hk n e he
  rcases hlargeReal hk n e he with ⟨Clarge, hClarge, hlarge⟩
  refine ⟨Clarge, hClarge, ?_⟩
  intro N hN s hs hRpos hRlarge
  have hWclose0 :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal| ≤
      (0 : ℝ) / (returnsToStart (k := k) s : ℝ) := by
    simp
  have hwrwor :
      (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
      Clarge / (returnsToStart (k := k) s : ℝ) :=
    hlarge hN s hs hRpos hRlarge
  simpa using
    surrogate_to_wor_bound
      (k := k) (hk := hk) (n := n) (e := e)
      (hN := hN) (s := s)
      (wSurrogate := (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal)
      (Cw := 0) (Cdf := Clarge)
      hWclose0 hwrwor

/-- Realizable-short-state WOR-transport constructor from large-`R` canonical
WR-surrogate→WOR bounds, then strict reduction to direct WR/WOR large-`R`
pattern rates via
`MarkovDeFinettiHardBEST.largeR_wr_wor_patternRate_of_canonicalWRSurrogate_largeR`. -/
theorem hasCanonicalWORTransportRate_on_realizable_shortState_of_largeR_canonicalWRSurrogate_rowL1StartTarget
    (hcanonLargeReal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          ∃ Clarge : ℝ, 0 ≤ Clarge ∧
            (∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
              s ∈ stateFinset k N →
                0 < returnsToStart (k := k) s →
                (4 * (Nat.succ n) * (Nat.succ n)) < returnsToStart (k := k) s →
                  (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
                    |canonicalWRSurrogateMass (k := k) n e
                        ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal) p -
                      (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
                    Clarge / (returnsToStart (k := k) s : ℝ))) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      e ∈ stateFinset k (Nat.succ n) →
        ∃ Cpc : ℝ, 0 ≤ Cpc ∧
          HasCanonicalWORTransportRate (k := k) hk n e
            ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
            Cpc := by
  have hlargeReal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          ∃ Clarge : ℝ, 0 ≤ Clarge ∧
            (∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
              s ∈ stateFinset k N →
                0 < returnsToStart (k := k) s →
                (4 * (Nat.succ n) * (Nat.succ n)) < returnsToStart (k := k) s →
                  (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
                    |(wrPatternMass (k := k) hk n e s p).toReal -
                      (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
                    Clarge / (returnsToStart (k := k) s : ℝ)) := by
    intro hk n e he
    rcases hcanonLargeReal hk n e he with ⟨Clarge, hClarge, hcanon⟩
    exact
      MarkovDeFinettiHardBEST.largeR_wr_wor_patternRate_of_canonicalWRSurrogate_largeR
        (k := k) (hk := hk) (n := n) (e := e)
        (hcanonLarge := ⟨Clarge, hClarge, hcanon⟩)
  exact
    hasCanonicalWORTransportRate_on_realizable_shortState_of_largeR_patternRate_rowL1StartTarget
      (k := k) hlargeReal

/-- Robust all-states constructor from:
`rowL1` WR smoothing + direct pattern WR/WOR discrepancy rates. -/
theorem hasExcursionResidualBoundRateAll_of_rowL1StartTarget_and_patternWRWORRateAll
    (hwrworAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro hk n e
  rcases hwrworAll hk n e with ⟨Cdf, hCdf, hwrwor⟩
  have hWOR :
      HasCanonicalWORTransportRate (k := k) hk n e
        ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
        (((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))) + Cdf) :=
    hasCanonicalWORTransportRate_of_patternWRWORRate
      (k := k) (hk := hk) (n := n) (e := e)
      (Cw := ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))))
      (Cdf := Cdf) hwrwor
  have hres :
      HasExcursionResidualBoundRate (k := k) hk n e
        (((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))) +
          (((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))) + Cdf)) :=
    hasExcursionResidualBoundRate_of_rowL1StartTarget_and_worTransport
      (k := k) (hk := hk) (n := n) (e := e)
      (Cpc := ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))) + Cdf) hWOR
  refine
    ⟨((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))) +
        (((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))) + Cdf),
      add_nonneg (by positivity) (add_nonneg (by positivity) hCdf),
      hres⟩

/-- Robust all-states constructor from:
`rowL1` WR smoothing + direct pattern-collision/zero-case obligations. -/
@[deprecated "Legacy collision-only constructor. Prefer hasExcursionResidualBoundRateAll_of_rowL1StartTarget_and_patternWRWORRateAll."
  (since := "2026-02-17")]
theorem hasExcursionResidualBoundRateAll_of_rowL1StartTarget_and_patternCollision_zeroCaseAll
    (hposAll : HasPatternCollisionPosAll (k := k))
    (hzeroAll : HasPatternCollisionZeroAll (k := k)) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  have hcoreAll :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        HasExcursionBiapproxCore (k := k) hk n e :=
    hasExcursionBiapproxCoreAll_of_patternCollision_and_zeroCaseAll
      (k := k) hposAll hzeroAll
  have hwrworAll :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf :=
    hasPatternWRWORRateAll_of_biapproxCoreAll
      (k := k) hcoreAll
  exact
    hasExcursionResidualBoundRateAll_of_rowL1StartTarget_and_patternWRWORRateAll
      (k := k) hwrworAll

/-- Robust all-states constructor from:
`rowL1` WR smoothing + positive-return pattern-collision obligations. -/
@[deprecated "Legacy collision-only constructor. Prefer hasExcursionResidualBoundRateAll_of_rowL1StartTarget_and_patternWRWORRateAll."
  (since := "2026-02-17")]
theorem hasExcursionResidualBoundRateAll_of_rowL1StartTarget_and_patternCollisionPosAll
    (hposAll : HasPatternCollisionPosAll (k := k)) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  have hwrworAll :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf :=
    by
      intro hk n e
      refine ⟨4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ), by positivity, ?_⟩
      intro N hN s hs hRpos
      simpa using hposAll hk n e hN s hs hRpos
  exact
    hasExcursionResidualBoundRateAll_of_rowL1StartTarget_and_patternWRWORRateAll
      (k := k) hwrworAll

theorem hasExcursionResidualBoundRateAll_of_excursionTargetSplitRatesAll
    (hsplitTargetAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cw Cpc : ℝ,
        0 ≤ Cw ∧ 0 ≤ Cpc ∧
        HasStatewiseExcursionTargetRates (k := k) hk n e Cw ∧
        HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro hk n e
  rcases hsplitTargetAll hk n e with ⟨Cw, Cpc, hCw, hCpc, hstate, hWOR⟩
  refine ⟨Cw + Cpc, add_nonneg hCw hCpc, ?_⟩
  exact
    hasExcursionResidualBoundRate_of_excursionTargetRates_and_worTransport
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc)
      hstate hWOR

theorem hasExcursionResidualBoundRateAll_of_splitRatesAll_fixed
    (hk : 0 < k)
    (hsplitAll : ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cw Cpc : ℝ,
        0 ≤ Cw ∧ 0 ≤ Cpc ∧
        HasCanonicalWRSmoothingRate (k := k) hk n e Cw ∧
        HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro n e
  rcases hsplitAll n e with ⟨Cw, Cpc, hCw, hCpc, hWR, hWOR⟩
  refine ⟨Cw + Cpc, add_nonneg hCw hCpc, ?_⟩
  exact hasExcursionResidualBoundRate_of_splitRates
    (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc)
    hWR hWOR

theorem hasExcursionResidualBoundRateAll_fixed_of_statewiseCloseSplitRatesAll
    (hk : 0 < k)
    (hsplitCloseAll : ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cw Cpc : ℝ,
        0 ≤ Cw ∧ 0 ≤ Cpc ∧
        (∀ {N : ℕ} (_hN : Nat.succ n ≤ N) (s : MarkovState k),
          s ∈ stateFinset k N →
            0 < returnsToStart (k := k) s →
              ∃ wSurrogate : ℝ,
                |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
                  wSurrogate| ≤ Cw / (returnsToStart (k := k) s : ℝ)) ∧
        HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro n e
  rcases hsplitCloseAll n e with ⟨Cw, Cpc, hCw, hCpc, hclose, hWOR⟩
  refine ⟨Cw + Cpc, add_nonneg hCw hCpc, ?_⟩
  exact
    hasExcursionResidualBoundRate_of_statewise_close_and_worTransport
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc)
      hclose hWOR

theorem hasExcursionResidualBoundRateAll_fixed_of_excursionTargetSplitRatesAll
    (hk : 0 < k)
    (hsplitTargetAll : ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cw Cpc : ℝ,
        0 ≤ Cw ∧ 0 ≤ Cpc ∧
        HasStatewiseExcursionTargetRates (k := k) hk n e Cw ∧
        HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro n e
  rcases hsplitTargetAll n e with ⟨Cw, Cpc, hCw, hCpc, hstate, hWOR⟩
  refine ⟨Cw + Cpc, add_nonneg hCw hCpc, ?_⟩
  exact
    hasExcursionResidualBoundRate_of_excursionTargetRates_and_worTransport
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw) (Cpc := Cpc)
      hstate hWOR




theorem hasExcursionResidualBoundRateAll_of_exactSurrogateWORTransportAll
    (hWORAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cpc : ℝ, 0 ≤ Cpc ∧
        HasCanonicalWORTransportRate (k := k) hk n e 0 Cpc) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro hk n e
  rcases hWORAll hk n e with ⟨Cpc, hCpc, hWOR⟩
  refine ⟨Cpc, hCpc, ?_⟩
  exact
    hasExcursionResidualBoundRate_of_worTransportRate
      (k := k) (hk := hk) (n := n) (e := e) (Cpc := Cpc) hWOR


theorem hasExcursionResidualBoundRateAll_of_exactSurrogateWORTransportAll_fixed
    (hk : 0 < k)
    (hWORAll : ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cpc : ℝ, 0 ≤ Cpc ∧
        HasCanonicalWORTransportRate (k := k) hk n e 0 Cpc) :
    ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro n e
  rcases hWORAll n e with ⟨Cpc, hCpc, hWOR⟩
  refine ⟨Cpc, hCpc, ?_⟩
  exact
    hasExcursionResidualBoundRate_of_worTransportRate
      (k := k) (hk := hk) (n := n) (e := e) (Cpc := Cpc) hWOR


theorem hasCanonicalWORTransportRateAll_of_biapproxCoreAll_exact
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cpc : ℝ, 0 ≤ Cpc ∧
        HasCanonicalWORTransportRate (k := k) hk n e 0 Cpc := by
  intro hk n e
  have hWORraw :
      HasCanonicalWORTransportRate (k := k) hk n e 0
        (0 + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) :=
    hasCanonicalWORTransportRate_of_biapproxCore
      (k := k) (hk := hk) (n := n) (e := e) (Cw := 0)
      (hcore := hcoreAll hk n e)
  refine ⟨0 + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ), by positivity, ?_⟩
  exact hWORraw

theorem hasCanonicalWORTransportRateAll_of_biapproxCoreAll_rowL1StartTarget
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cpc : ℝ, 0 ≤ Cpc ∧
        HasCanonicalWORTransportRate (k := k) hk n e
          ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
          Cpc := by
  intro hk n e
  refine
    ⟨((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))) +
      4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ), by positivity, ?_⟩
  exact
    hasCanonicalWORTransportRate_of_biapproxCore
      (k := k) (hk := hk) (n := n) (e := e)
      (Cw := (Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
      (hcore := hcoreAll hk n e)

/-- Realizable-short-state constructor:
from biapprox-core hypotheses on realizable short states `e ∈ stateFinset k (n+1)`,
build the WOR-transport obligations needed by the rowL1 route. -/
theorem hasCanonicalWORTransportRate_on_realizable_shortState_of_biapproxCore_rowL1StartTarget
    (hcoreReal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      e ∈ stateFinset k (Nat.succ n) →
        ∃ Cpc : ℝ, 0 ≤ Cpc ∧
          HasCanonicalWORTransportRate (k := k) hk n e
            ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
            Cpc := by
  intro hk n e he
  let Cw : ℝ := (Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ))
  refine
    ⟨Cw + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ),
      by positivity, ?_⟩
  exact
    hasCanonicalWORTransportRate_of_biapproxCore
      (k := k) (hk := hk) (n := n) (e := e) (Cw := Cw)
      (hcore := hcoreReal hk n e he)

/-- Realizable-short-state canonical-surrogate large-`R` witness extracted from
biapprox-core hypotheses. This is the exact `hcanonLargeReal` shape consumed by
`hasCanonicalWORTransportRate_on_realizable_shortState_of_largeR_canonicalWRSurrogate_rowL1StartTarget`.
-/
theorem hasCanonicalWRSurrogateLargeR_on_realizable_shortState_of_biapproxCore
    (hcoreReal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      e ∈ stateFinset k (Nat.succ n) →
        ∃ Clarge : ℝ, 0 ≤ Clarge ∧
          (∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
            s ∈ stateFinset k N →
              0 < returnsToStart (k := k) s →
              (4 * (Nat.succ n) * (Nat.succ n)) < returnsToStart (k := k) s →
                (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
                  |canonicalWRSurrogateMass (k := k) n e
                      ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal) p -
                    (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
                  Clarge / (returnsToStart (k := k) s : ℝ)) := by
  intro hk n e he
  refine ⟨4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ), by positivity, ?_⟩
  intro N hN s hs hRpos _hRlarge
  simpa using
    (wor_transport_rate_canonicalWRSurrogate_exact
      (k := k) (hk := hk) (n := n) (e := e)
      (hN := hN) (s := s) (hs := hs)
      (hcore := hcoreReal hk n e he hN s hs))

/-- Same realizable-short-state WOR-transport obligations as
`hasCanonicalWORTransportRate_on_realizable_shortState_of_biapproxCore_rowL1StartTarget`,
but routed explicitly through the large-`R` canonical-surrogate interface.
-/
theorem hasCanonicalWORTransportRate_on_realizable_shortState_of_biapproxCore_via_largeR_canonical_rowL1StartTarget
    (hcoreReal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      e ∈ stateFinset k (Nat.succ n) →
        ∃ Cpc : ℝ, 0 ≤ Cpc ∧
          HasCanonicalWORTransportRate (k := k) hk n e
            ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
            Cpc := by
  have hcanonLargeReal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          ∃ Clarge : ℝ, 0 ≤ Clarge ∧
            (∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
              s ∈ stateFinset k N →
                0 < returnsToStart (k := k) s →
                (4 * (Nat.succ n) * (Nat.succ n)) < returnsToStart (k := k) s →
                  (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
                    |canonicalWRSurrogateMass (k := k) n e
                        ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal) p -
                      (worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
                    Clarge / (returnsToStart (k := k) s : ℝ)) :=
    hasCanonicalWRSurrogateLargeR_on_realizable_shortState_of_biapproxCore
      (k := k) hcoreReal
  exact
    hasCanonicalWORTransportRate_on_realizable_shortState_of_largeR_canonicalWRSurrogate_rowL1StartTarget
      (k := k) hcanonLargeReal

/-- Realizable-short-state direct pattern-rate constructor:
biapprox-core on realizable short states implies realizable `HasPatternWRWORRate`
through rowL1 WR smoothing + WOR transport composition. -/
theorem hasPatternWRWORRate_on_realizable_shortState_of_biapproxCore_rowL1StartTarget
    (hcoreReal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      e ∈ stateFinset k (Nat.succ n) →
        ∃ Cdf : ℝ, 0 ≤ Cdf ∧ HasPatternWRWORRate (k := k) hk n e Cdf := by
  have hWORReal :
      ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
        e ∈ stateFinset k (Nat.succ n) →
          ∃ Cpc : ℝ, 0 ≤ Cpc ∧
            HasCanonicalWORTransportRate (k := k) hk n e
              ((Nat.succ n : ℝ) * ((k : ℝ) * (k : ℝ)))
              Cpc :=
    hasCanonicalWORTransportRate_on_realizable_shortState_of_biapproxCore_rowL1StartTarget
      (k := k) hcoreReal
  exact
    hasPatternWRWORRate_on_realizable_shortState_of_rowL1StartTarget_and_worTransport
      (k := k) hWORReal


theorem hasExcursionResidualBoundRateAll_of_biapproxCoreAll_exactSurrogate
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro hk n e
  have hWORAll := hasCanonicalWORTransportRateAll_of_biapproxCoreAll_exact
    (k := k) hcoreAll
  rcases hWORAll hk n e with ⟨Cpc, hCpc, hWOR⟩
  refine ⟨Cpc, hCpc, ?_⟩
  exact
    hasExcursionResidualBoundRate_of_worTransportRate
      (k := k) (hk := hk) (n := n) (e := e) (Cpc := Cpc) hWOR


theorem hasExcursionResidualBoundRateAll_of_biapproxCoreAll_exactSurrogate_fixed
    (hk : 0 < k)
    (hcoreAll : ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro n e
  have hWORraw :
      HasCanonicalWORTransportRate (k := k) hk n e 0
        (0 + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) :=
    hasCanonicalWORTransportRate_of_biapproxCore
      (k := k) (hk := hk) (n := n) (e := e) (Cw := 0)
      (hcore := hcoreAll n e)
  refine ⟨0 + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ), by positivity, ?_⟩
  exact
    hasExcursionResidualBoundRate_of_worTransportRate
      (k := k) (hk := hk) (n := n) (e := e)
      (Cpc := 0 + 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) hWORraw

theorem hasExcursionResidualBoundRateAll_of_explicitPatternSurrogateRateAll
    (halignAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧
        HasPatternSurrogateResidualAlignmentRate (k := k) hk n e C) :
    ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro hk n e
  rcases halignAll hk n e with ⟨C, hC, halign⟩
  refine ⟨C, hC, ?_⟩
  exact
    hasExcursionResidualBoundRate_of_explicitPatternSurrogateRate
      (k := k) (hk := hk) (n := n) (e := e) (C := C) halign

theorem hasExcursionResidualBoundRateAll_of_explicitPatternSurrogateRateAll_fixed
    (hk : 0 < k)
    (halignAll : ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧
        HasPatternSurrogateResidualAlignmentRate (k := k) hk n e C) :
    ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C := by
  intro n e
  rcases halignAll n e with ⟨C, hC, halign⟩
  refine ⟨C, hC, ?_⟩
  exact
    hasExcursionResidualBoundRate_of_explicitPatternSurrogateRate
      (k := k) (hk := hk) (n := n) (e := e) (C := C) halign

/-! ## Good‑state bound (Diaconis–Freedman core)

The core approximation lemma: for evidence states with many returns to start,
the empirical Markov predictor approximates the uniform‑fiber prefix coefficient
at rate `O(1 / M)`.

Definitions and helper lemmas (`prefixExcursionCount`, `excursionListOfTraj_length`,
etc.) are in `MarkovDeFinettiHardBEST`.
-/

/-- **Excursion WOR/WR correspondence** (the core Diaconis–Freedman lemma).

For `R > 4n²`, the difference between `W(empiricalParam s)` and `prefixCoeff`
is bounded by `4n²/R` via the excursion decomposition.

The proof requires:
- Fiber partition into excursion prefix fibers (disjoint covering)
- BEST theorem consequence: uniform Euler path sampling → uniform excursion ordering
- Product decomposition of `wordProbNN` through excursion frequencies

These show `prefixCoeff = ∑ WOR` and `W(empiricalParam) = ∑ WR` over the same
index set, reducing the bound to `abs_excursion_wor_wr_le_take`. -/
private lemma excursion_wor_wr_bound
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (hcore : HasExcursionBiapproxCore (k := k) hk n e) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  exact excursion_bound_from_decomposition hk n e hN s hs (hcore hN s hs)

/-- The per‑state excursion bound: the difference between the empirical
evidence polynomial and the prefix coefficient is bounded by `4n²/R`,
where `R = returnsToStart s`.

For `R ≤ 4n²`: the bound ≥ 1, which dominates |diff| since both values ∈ [0,1].
For `R > 4n²`: uses the genuine excursion WOR/WR correspondence. -/
private lemma excursion_decomposition_bound
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (hcore : HasExcursionBiapproxCore (k := k) hk n e)
    (hRpos : 0 < returnsToStart (k := k) s) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  by_cases hsmall : returnsToStart (k := k) s ≤ 4 * (Nat.succ n) * (Nat.succ n)
  · -- Trivial case: R ≤ 4(n+1)², so 4(n+1)²/R ≥ 1 ≥ |diff|.
    have hdiff := abs_diffTerm_le_one (k := k) (hk := hk) (hN := hN) (e := e) (s := s) hs
    have hRreal : (0 : ℝ) < (returnsToStart (k := k) s : ℝ) :=
      Nat.cast_pos.mpr hRpos
    have hbound : (1 : ℝ) ≤ (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
      rw [le_div_iff₀ hRreal]
      simp only [one_mul]
      exact_mod_cast hsmall
    linarith
  · -- Real case: R > 4(n+1)², use the excursion WOR/WR correspondence.
    have hRlarge : 4 * (Nat.succ n) * (Nat.succ n) < returnsToStart (k := k) s := by omega
    exact excursion_wor_wr_bound (k := k) hk n e hN s hs hcore

/-- The per‑state excursion bound: the difference between the empirical
evidence polynomial and the prefix coefficient is bounded by `4n²/M`.

Proved from `excursion_decomposition_bound` (with `R = returnsToStart s`)
and the hypothesis `M ≤ R`. -/
private lemma perState_excursion_bound
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (hcore : HasExcursionBiapproxCore (k := k) hk n e)
    (M : ℕ) (hM : 0 < M) (hMret : M ≤ returnsToStart (k := k) s) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) / (M : ℝ) := by
  have hRpos : 0 < returnsToStart (k := k) s := Nat.lt_of_lt_of_le hM hMret
  have hR := excursion_decomposition_bound (k := k) hk n e hN s hs hcore hRpos
  have hnum : (0 : ℝ) ≤ 4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ) := by positivity
  calc |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
          - (prefixCoeff (k := k) (h := hN) e s).toReal|
      ≤ (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := hR
    _ ≤ (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) / (M : ℝ) := by
        apply div_le_div_of_nonneg_left hnum
        · exact Nat.cast_pos.mpr hM
        · exact Nat.cast_le.mpr hMret

theorem good_state_bound
    (hk : 0 < k)
    (n : ℕ) (e : MarkovState k)
    (hcore : HasExcursionBiapproxCore (k := k) hk n e) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {N : ℕ} (hN : Nat.succ n ≤ N)
        (s : MarkovState k),
          s ∈ stateFinset k N →
            ∀ (M : ℕ), 0 < M → M ≤ returnsToStart (k := k) s →
              |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
                  - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤ C / (M : ℝ) := by
  -- The constant C = 4 * (n+1)² works universally.
  refine ⟨4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ), by positivity, ?_⟩
  intro N hN s hs M hM hMret
  exact perState_excursion_bound (k := k) hk n e hN s hs hcore M hM hMret

theorem good_state_bound_of_residualRate
    (hk : 0 < k)
    (n : ℕ) (e : MarkovState k)
    (C : ℝ) (hC : 0 ≤ C)
    (hrate : HasExcursionResidualBoundRate (k := k) hk n e C) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ {N : ℕ} (hN : Nat.succ n ≤ N)
        (s : MarkovState k),
          s ∈ stateFinset k N →
            ∀ (M : ℕ), 0 < M → M ≤ returnsToStart (k := k) s →
              |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
                  - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤ C' / (M : ℝ) := by
  refine ⟨C, hC, ?_⟩
  intro N hN s hs M hM hMret
  have hRpos : 0 < returnsToStart (k := k) s := Nat.lt_of_lt_of_le hM hMret
  rcases hrate hN s hs hRpos with ⟨εW, εPC, hWnonneg, hPCnonneg, hrate_le, hbound⟩
  have hCdivR_le_CdivM :
      C / (returnsToStart (k := k) s : ℝ) ≤ C / (M : ℝ) := by
    refine div_le_div_of_nonneg_left hC ?_ ?_
    · exact Nat.cast_pos.mpr hM
    · exact_mod_cast hMret
  calc
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal|
        ≤ εW + εPC := hbound
    _ ≤ C / (returnsToStart (k := k) s : ℝ) := hrate_le
    _ ≤ C / (M : ℝ) := hCdivR_le_CdivM

lemma abs_weightedDiffCore_le
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (n : ℕ) (e : MarkovState k) (N : ℕ) (hN : Nat.succ n ≤ N)
    (M : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hgood :
      ∀ (s : MarkovState k),
        s ∈ stateFinset k N →
          M ≤ returnsToStart (k := k) s →
            |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
                - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤ C / (M : ℝ)) :
    |weightedDiffCore hk μ n e N hN| ≤ C / (M : ℝ) + badMass (k := k) μ N M := by
  classical
  have hsum_abs :
      |∑ s ∈ stateFinset k N,
        ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
          - (prefixCoeff (k := k) (h := hN) e s).toReal) *
          (wμ (k := k) μ N s).toReal| ≤
        ∑ s ∈ stateFinset k N,
          |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
              - (prefixCoeff (k := k) (h := hN) e s).toReal| *
            (wμ (k := k) μ N s).toReal := by
    have h :=
      (Finset.abs_sum_le_sum_abs
        (s := stateFinset k N)
        (f := fun s =>
          ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
            - (prefixCoeff (k := k) (h := hN) e s).toReal) *
            (wμ (k := k) μ N s).toReal))
    simpa using h
  have hterm_le :
      ∀ s ∈ stateFinset k N,
        |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
            - (prefixCoeff (k := k) (h := hN) e s).toReal| *
            (wμ (k := k) μ N s).toReal ≤
          (if returnsToStart (k := k) s < M then 1 else C / (M : ℝ)) *
            (wμ (k := k) μ N s).toReal := by
    intro s hs
    by_cases hbad : returnsToStart (k := k) s < M
    · have hdiff :=
        abs_diffTerm_le_one (k := k) (hk := hk) (hN := hN) (e := e) (s := s) hs
      have hw : 0 ≤ (wμ (k := k) μ N s).toReal := by exact ENNReal.toReal_nonneg
      have hmul := mul_le_mul_of_nonneg_right hdiff hw
      simpa [hbad] using hmul
    · have hgood' : M ≤ returnsToStart (k := k) s := le_of_not_gt hbad
      have hdiff := hgood s hs hgood'
      have hw : 0 ≤ (wμ (k := k) μ N s).toReal := by exact ENNReal.toReal_nonneg
      have hmul := mul_le_mul_of_nonneg_right hdiff hw
      simpa [hbad] using hmul
  have hsum_bound :
      ∑ s ∈ stateFinset k N,
        |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
            - (prefixCoeff (k := k) (h := hN) e s).toReal| *
            (wμ (k := k) μ N s).toReal ≤
        ∑ s ∈ stateFinset k N,
          (if returnsToStart (k := k) s < M then 1 else C / (M : ℝ)) *
            (wμ (k := k) μ N s).toReal := by
    exact Finset.sum_le_sum hterm_le
  have hsplit_le :
      ∑ s ∈ stateFinset k N,
        (if returnsToStart (k := k) s < M then 1 else C / (M : ℝ)) *
          (wμ (k := k) μ N s).toReal ≤
        badMass (k := k) μ N M + (C / (M : ℝ)) *
          ∑ s ∈ stateFinset k N, (wμ (k := k) μ N s).toReal := by
    -- First compare to a pointwise upper bound.
    have hsum_le :
        ∑ s ∈ stateFinset k N,
          (if returnsToStart (k := k) s < M then 1 else C / (M : ℝ)) *
            (wμ (k := k) μ N s).toReal ≤
          ∑ s ∈ stateFinset k N,
            ((if returnsToStart (k := k) s < M then (wμ (k := k) μ N s).toReal else 0) +
              (C / (M : ℝ)) * (wμ (k := k) μ N s).toReal) := by
      refine Finset.sum_le_sum ?_
      intro s hs
      by_cases hbad : returnsToStart (k := k) s < M
      · have hw : 0 ≤ (wμ (k := k) μ N s).toReal := by exact ENNReal.toReal_nonneg
        have hcm : 0 ≤ C / (M : ℝ) := by
          exact div_nonneg hC (Nat.cast_nonneg M)
        -- after simplification, it suffices to show nonnegativity
        simp [hbad]
        exact mul_nonneg hcm hw
      · simp [hbad]
    -- Now compute the sum on the right.
    have hsum_eq :
        (∑ s ∈ stateFinset k N,
            ((if returnsToStart (k := k) s < M then (wμ (k := k) μ N s).toReal else 0) +
              (C / (M : ℝ)) * (wμ (k := k) μ N s).toReal)) =
          badMass (k := k) μ N M + (C / (M : ℝ)) *
            ∑ s ∈ stateFinset k N, (wμ (k := k) μ N s).toReal := by
      simp [badMass, Finset.sum_add_distrib, Finset.mul_sum]
    exact hsum_le.trans (by simp [hsum_eq])
  have hsum_wμ : ∑ s ∈ stateFinset k N, (wμ (k := k) μ N s).toReal = 1 :=
    sum_wμ_toReal_eq_one (k := k) (μ := μ) N
  calc
    |weightedDiffCore hk μ n e N hN|
        = |∑ s ∈ stateFinset k N,
              ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
                - (prefixCoeff (k := k) (h := hN) e s).toReal) *
                (wμ (k := k) μ N s).toReal| := by
              simp [weightedDiffCore]
    _ ≤ ∑ s ∈ stateFinset k N,
          |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
              - (prefixCoeff (k := k) (h := hN) e s).toReal| *
            (wμ (k := k) μ N s).toReal := hsum_abs
    _ ≤ ∑ s ∈ stateFinset k N,
          (if returnsToStart (k := k) s < M then 1 else C / (M : ℝ)) *
            (wμ (k := k) μ N s).toReal := hsum_bound
    _ ≤ badMass (k := k) μ N M + (C / (M : ℝ)) *
          ∑ s ∈ stateFinset k N, (wμ (k := k) μ N s).toReal := hsplit_le
    _ = badMass (k := k) μ N M + (C / (M : ℝ)) * 1 := by
          simp [hsum_wμ]
    _ = C / (M : ℝ) + badMass (k := k) μ N M := by
          ring_nf
    _ = C / (M : ℝ) + badMass (k := k) μ N M := rfl

/-! The core asymptotic statement for the weighted difference. -/
private theorem weightedDiffCore_tendsto_zero_of_goodStateBound
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hrec : MarkovRecurrentPrefixMeasure μ)
    (n : ℕ) (e : MarkovState k)
    (hgoodPack :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ {N : ℕ} (hN : Nat.succ n ≤ N)
          (s : MarkovState k),
            s ∈ stateFinset k N →
              ∀ (M : ℕ), 0 < M → M ≤ returnsToStart (k := k) s →
                |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
                    - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤ C / (M : ℝ)) :
    Filter.Tendsto (weightedDiff (k := k) hk μ n e) Filter.atTop (nhds 0) := by
  classical
  obtain ⟨C, hC, hgood⟩ := hgoodPack
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨M, hMpos, hMbound⟩ : ∃ M : ℕ, 0 < M ∧ C / (M : ℝ) < ε / 2 := by
    by_cases hC0 : C = 0
    · refine ⟨1, ?_⟩
      refine ⟨by decide, ?_⟩
      simp [hC0, hε2]
    · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
      have hden : 0 < (2 : ℝ) * C := by nlinarith
      have hεC : 0 < ε / ((2 : ℝ) * C) := by exact div_pos hε hden
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hεC
      refine ⟨m + 1, Nat.succ_pos _, ?_⟩
      have hm' : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) < ε / ((2 : ℝ) * C) := by
        simpa using hm
      have hmul : C * ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) < C * (ε / ((2 : ℝ) * C)) := by
        exact mul_lt_mul_of_pos_left hm' hCpos
      have hleft : C / ((m + 1 : ℕ) : ℝ) = C * ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
        ring
      have hright : C * (ε / ((2 : ℝ) * C)) = ε / 2 := by
        have hCne : C ≠ 0 := ne_of_gt hCpos
        field_simp [hCne]
      simpa [hleft, hright] using hmul
  have hbad := badMass_tendsto_zero (k := k) (μ := μ) (M := M) hrec
  rw [Metric.tendsto_atTop] at hbad
  obtain ⟨N0, hN0⟩ := hbad (ε / 2) hε2
  refine ⟨max N0 (Nat.succ n), ?_⟩
  intro N hN
  have hN0' : N0 ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
  have hN1' : Nat.succ n ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
  have hbadN := hN0 N hN0'
  have hcore : weightedDiff (k := k) hk μ n e N =
      weightedDiffCore hk μ n e N hN1' := by
    simp [weightedDiff, hN1', weightedDiffCore]
  have hbound :=
    abs_weightedDiffCore_le (k := k) (hk := hk) (μ := μ) (n := n) (e := e)
      (N := N) (hN := hN1') (M := M) (C := C) hC
      (fun s hs hret => hgood (N := N) hN1' s hs M hMpos hret)
  have hbadN' : |badMass (k := k) μ N M - 0| < ε / 2 := by
    simpa [Real.dist_eq, sub_zero] using hbadN
  have hbadN'' : badMass (k := k) μ N M < ε / 2 := by
    have hnonneg := badMass_nonneg (k := k) (μ := μ) (N := N) (M := M)
    simpa [abs_of_nonneg hnonneg] using hbadN'
  have hfinal : |weightedDiff (k := k) hk μ n e N| < ε := by
    have hle : |weightedDiff (k := k) hk μ n e N|
        ≤ C / (M : ℝ) + badMass (k := k) μ N M := by
      simpa [hcore] using hbound
    have hsum : C / (M : ℝ) + badMass (k := k) μ N M < ε := by
      linarith [hMbound, hbadN'']
    exact lt_of_le_of_lt hle hsum
  simpa [Real.dist_eq, sub_zero] using hfinal

theorem weightedDiffCore_tendsto_zero
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure μ)
    (n : ℕ) (e : MarkovState k)
    (hcore : HasExcursionBiapproxCore (k := k) hk n e) :
    Filter.Tendsto (weightedDiff (k := k) hk μ n e) Filter.atTop (nhds 0) := by
  have hgoodPack := good_state_bound (k := k) (hk := hk) (n := n) (e := e) hcore
  exact weightedDiffCore_tendsto_zero_of_goodStateBound
    (k := k) (hk := hk) (μ := μ) (hrec := hrec) (n := n) (e := e) hgoodPack

theorem weightedDiffCore_tendsto_zero_of_residualRate
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure μ)
    (n : ℕ) (e : MarkovState k)
    (C : ℝ) (hC : 0 ≤ C)
    (hrate : HasExcursionResidualBoundRate (k := k) hk n e C) :
    Filter.Tendsto (weightedDiff (k := k) hk μ n e) Filter.atTop (nhds 0) := by
  have hgoodPack :=
    good_state_bound_of_residualRate
      (k := k) (hk := hk) (n := n) (e := e)
      (C := C) hC hrate
  exact weightedDiffCore_tendsto_zero_of_goodStateBound
    (k := k) (hk := hk) (μ := μ) (hrec := hrec) (n := n) (e := e) hgoodPack

/-!
### Diaconis–Freedman approximation lemma (main remaining gap)

This is the only hard analytic lemma required for the Markov de Finetti
hard direction. Once proven, the rest of the pipeline (moment polytope,
compactness, finite‑intersection) closes automatically.
-/

theorem weightedDiff_tendsto_zero
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure μ)
    (n : ℕ) (e : MarkovState k)
    (hcore : HasExcursionBiapproxCore (k := k) hk n e) :
    Filter.Tendsto (weightedDiff (k := k) hk μ n e) Filter.atTop (nhds 0) := by
  exact weightedDiffCore_tendsto_zero (k := k) (hk := hk) (μ := μ) hμ hrec n e hcore

theorem weightedDiff_tendsto_zero_of_residualRate
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure μ)
    (n : ℕ) (e : MarkovState k)
    (C : ℝ) (hC : 0 ≤ C)
    (hrate : HasExcursionResidualBoundRate (k := k) hk n e C) :
    Filter.Tendsto (weightedDiff (k := k) hk μ n e) Filter.atTop (nhds 0) := by
  exact weightedDiffCore_tendsto_zero_of_residualRate
    (k := k) (hk := hk) (μ := μ) hμ hrec n e C hC hrate

end MarkovDeFinettiHard

end Mettapedia.Logic
