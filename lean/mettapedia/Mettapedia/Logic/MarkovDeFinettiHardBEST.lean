import Mettapedia.Logic.MarkovDeFinettiHardEuler
import Mettapedia.Logic.MarkovDeFinettiHardBESTCore
import Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
import Mettapedia.Logic.MarkovDeFinettiHardEmpirical

/-! LLM primer:
- `MarkovState k` encodes (start : Fin k, counts : TransCounts k).
- `fiber k N eN` = trajectories of length N whose `stateOfTraj` = eN.
- The BEST theorem: #EulerTrails = #arborescences(root) × ∏_{v} (outdeg(v) - 1)!

Status: The main theorem `excursion_bound_from_decomposition` reduces to a single
sorry `excursion_wor_wr_core`. This sorry IS the Diaconis-Freedman core lemma:
for states with many returns, |W(empiricalParam) - prefixCoeff| ≤ 4n²/R.
Proving it requires the BEST theorem for Euler trail counting.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHardBEST

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiHardEuler
open Mettapedia.Logic.MarkovDeFinettiHard
open Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
open Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacementModel
open Mettapedia.Logic.MarkovDeFinettiHardExcursions
open Mettapedia.Logic.EvidenceDirichlet

variable {k : ℕ}

/-! ## Excursion-count helpers -/

lemma excursionListOfTraj_length {n : ℕ} (xs : Traj k n) :
    (excursionListOfTraj (k := k) xs).length = numExcursions (k := k) xs := by
  simp [excursionListOfTraj, excursionsOfTraj, length_excursionPairs]

lemma excursionMultiset_card_eq_numExcursions {n : ℕ} (xs : Traj k n) :
    (excursionMultiset (k := k) (excursionListOfTraj (k := k) xs)).card =
      numExcursions (k := k) xs := by
  simp [excursionMultiset, excursionListOfTraj_length]

/-- Number of excursions in the first `n` transitions of a trajectory. -/
def prefixExcursionCount {n N : ℕ} (hN : n ≤ N) (xs : Traj k N) : ℕ :=
  numExcursions (k := k) (trajPrefix (k := k) hN xs)

lemma prefixExcursionCount_le_n {n N : ℕ} (hN : n ≤ N) (xs : Traj k N) :
    prefixExcursionCount (k := k) hN xs ≤ n := by
  unfold prefixExcursionCount numExcursions
  have hcard : (returnPositions (k := k) (trajPrefix (k := k) hN xs)).card ≤ n + 1 := by
    have := Finset.card_le_univ (returnPositions (k := k) (trajPrefix (k := k) hN xs))
    simpa [Fintype.card_fin] using this
  omega

/-- The excursion list of any trajectory in the fiber of `s` has length
`returnsToStart s`. -/
lemma excursionList_length_eq_returnsToStart
    {N : ℕ} (s : MarkovState k) (xs : Traj k N) (hxs : xs ∈ fiber k N s) :
    (excursionListOfTraj (k := k) xs).length = returnsToStart (k := k) s := by
  have h1 := excursionListOfTraj_length (k := k) xs
  have h2 := numExcursions_eq_returnsToStart (k := k) xs
  have h3 : stateOfTraj (k := k) xs = s := (Finset.mem_filter.1 hxs).2
  rw [h1, h2, h3]

/-! ## Empirical parameter step probability -/

/-- `empiricalStepProb` is nonneg. -/
lemma empiricalStepProb_nonneg' (hk : 0 < k) (c : TransCounts k) (a b : Fin k) :
    0 ≤ empiricalStepProb (k := k) hk c a b := by
  unfold empiricalStepProb
  apply div_nonneg
  · have h1 : 0 ≤ (c.counts a b : ℝ) := by exact_mod_cast Nat.zero_le _
    have h2 : 0 ≤ (DirichletParams.uniformPrior (k := k)).priorParams b := by
      simp [DirichletParams.uniformPrior, DirichletParams.uniform]
    linarith
  · have h1 : 0 ≤ (c.rowTotal a : ℝ) := by exact_mod_cast Nat.zero_le _
    have h2 : 0 < (DirichletParams.uniformPrior (k := k)).totalConcentration :=
      DirichletParams.totalConcentration_pos (k := k) (p := DirichletParams.uniformPrior) hk
    linarith

/-- `stepProb` of the empirical parameter equals the Laplace-smoothed empirical probability,
cast to NNReal. -/
lemma stepProb_empiricalParam (hk : 0 < k) (s : MarkovState k) (a b : Fin k) :
    (stepProb (k := k) (empiricalParam (k := k) hk s) a b : ℝ) =
      empiricalStepProb (k := k) hk s.counts a b := by
  unfold stepProb empiricalParam empiricalRowMeasure
  dsimp only []
  rw [MeasureTheory.ProbabilityMeasure.mk_apply]
  have hsingle :
      (empiricalRowPMF (k := k) hk s.counts a).toMeasure (Set.singleton b) =
        empiricalRowPMF (k := k) hk s.counts a b := by
    exact PMF.toMeasure_apply_singleton
      (p := empiricalRowPMF (k := k) hk s.counts a)
      (a := b)
      (h := measurableSet_singleton b)
  rw [hsingle]
  simp only [empiricalRowPMF, PMF.ofFinset_apply]
  rw [ENNReal.coe_toNNReal_eq_toReal]
  exact ENNReal.toReal_ofReal (empiricalStepProb_nonneg' hk s.counts a b)

/-! ## wordProbNN of empiricalParam on fiber members -/

/-- For any trajectory `xs` in `fiber(N, s)`, `wordProbNN(empiricalParam(s), xs)` depends
only on `s` (not the choice of `xs`), since `wordProbNN` is constant on fibers. -/
lemma wordProbNN_empiricalParam_const_on_fiber
    (hk : 0 < k) {N : ℕ} (s : MarkovState k) {xs ys : Traj k N}
    (hxs : xs ∈ fiber k N s) (hys : ys ∈ fiber k N s) :
    wordProbNN (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) xs) =
      wordProbNN (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys) := by
  have hstate_xs : stateOfTraj (k := k) xs = s := (Finset.mem_filter.1 hxs).2
  have hstate_ys : stateOfTraj (k := k) ys = s := (Finset.mem_filter.1 hys).2
  exact wordProbNN_const_on_state_fiber (k := k) (empiricalParam (k := k) hk s)
    (by rw [hstate_xs, hstate_ys])

/-- `W(N, s, θ) = |fiber(N, s)| × wordProb(θ, xs₀)` for any `xs₀ ∈ fiber(N, s)`,
since `wordProb` is constant on the fiber. -/
lemma W_eq_card_mul_wordProb_of_mem_fiber
    {N : ℕ} (θ : MarkovParam k) (s : MarkovState k)
    (xs₀ : Traj k N) (hxs₀ : xs₀ ∈ fiber k N s) :
    W (k := k) N s θ =
      (fiber k N s).card *
        wordProb (k := k) θ (trajToList (k := k) xs₀) := by
  classical
  simp only [W]
  have hfib : (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = s) = fiber k N s := rfl
  rw [hfib]
  have hconst : ∀ xs ∈ fiber k N s,
      wordProb (k := k) θ (trajToList (k := k) xs) =
        wordProb (k := k) θ (trajToList (k := k) xs₀) := by
    intro xs hxs
    exact wordProb_const_on_state_fiber (k := k) θ
      (by rw [(Finset.mem_filter.1 hxs).2, (Finset.mem_filter.1 hxs₀).2])
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]
  simp [nsmul_eq_mul]

/-! ## Diaconis-Freedman core lemma

The key bound connecting `W(empiricalParam)` and `prefixCoeff` via the
excursion decomposition. This is the mathematical heart of the proof.

The proof requires the BEST theorem (or excursion ordering bijection):
1. Uniform fiber sampling → uniform excursion ordering
2. `prefixCoeff` = ∑ WOR probabilities over excursion prefix patterns
3. `W(empiricalParam)` ≈ ∑ WR probabilities (up to Laplace smoothing)
4. WOR/WR bound gives `4n²/R`
-/

/-- **Diaconis-Freedman core**: for `R > 4n²`, the difference between
`W(empiricalParam s)` and `prefixCoeff` is bounded by `4n²/R`.

TODO: Prove via BEST theorem consequence (Euler trail counting / excursion
ordering bijection). The key missing pieces are:
- Fiber cardinality formula: `|fiber(N, s)| = t_s(G) × ∏_a (outdeg(a) - 1)!`
- Excursion ordering uniformity (consequence of BEST)
- Product decomposition of `wordProbNN` through excursion frequencies -/
theorem excursion_bound_from_decomposition
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (hRlarge : 4 * n * n < returnsToStart (k := k) s) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      (4 * (n : ℝ) * (n : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  -- Correct core target (to be discharged via BEST-style counting):
  --
  -- We must compare two quantities that are defined on the *entire fiber* `fiber k N s`:
  --
  -- 1. `prefixCoeff (h := hN) e s` (uniform-on-fiber prefix event probability),
  -- 2. `W (n+1) e (empiricalParam hk s)` (empirical Markov predictive mass).
  --
  -- A representative trajectory `xs₀` and its excursion list `excursionListOfTraj xs₀`
  -- are not sufficient by themselves, because excursion multisets are not constant on a
  -- whole state fiber in general.
  --
  -- The required bridge is a finite combinatorial theorem:
  -- a partition/average formula over excursion-profile classes, with each class weighted by
  -- Euler-trail counts; BEST (or an equivalent Euler-trail counting theorem) is then used to
  -- identify the class weights and derive the `O(n² / returnsToStart s)` bound.
  --
  -- Once that bridge is formalized, this theorem should become a short wrapper.
  sorry

end MarkovDeFinettiHardBEST

end Mettapedia.Logic
