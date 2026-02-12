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
  ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
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
      ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
        s ∈ stateFinset k N →
          0 < returnsToStart (k := k) s →
            ∃ wSurrogate : ℝ,
              |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
                wSurrogate| ≤ Cw / (returnsToStart (k := k) s : ℝ)) :
    HasCanonicalWRSmoothingRate (k := k) hk n e Cw := by
  intro N hN s hs hRpos
  rcases hclose hN s hs hRpos with ⟨wSurrogate, hWclose⟩
  refine ⟨wSurrogate, Cw / (returnsToStart (k := k) s : ℝ), hWclose, le_rfl⟩


/-- Robust route: build the residual-rate bound from a scalar statewise WR surrogate
and a canonical WOR transport rate. -/
lemma hasExcursionResidualBoundRate_of_statewise_close_and_worTransport
    (hk : 0 < k) (n : ℕ) (e : MarkovState k) (Cw Cpc : ℝ)
    (hclose :
      ∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
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
    simpa using hnonneg

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
