import Mettapedia.Logic.UniversalPrediction
import Mettapedia.Logic.UniversalPrediction.MarkovDirichletPredictor
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.CompetitorBounds
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.ComputableMixture
import Mettapedia.Computability.HutterComputabilityENNReal
import Mettapedia.Computability.HutterComputabilityRational

import Mathlib.Computability.Primrec.List

/-!
# Hyperprior Mixtures for Markov(1) Dirichlet Predictors (Finite Alphabet)

This file is the finite-alphabet analogue of `UniversalPrediction/MarkovHyperpriorMixture.lean`.

It implements the **Hook B** pattern for the Markov(1) setting:

* pick a **countable family** of tractable Markov(1) predictors (here: symmetric Dirichlet priors),
* put a **hyperprior** (a weight sequence summing to 1) on that family, and
* form the Bayesian mixture (a `FiniteAlphabet.PrefixMeasure`) which dominates each component by
  its weight.

This yields a theorem-grade statement that “choosing a prior” can be done by a mixture; once the
mixture is shown enumerable/LSC, Hutter-style universal prediction competes with it automatically.

For now we keep the family simple: one parameter `a > 0` used as `Dirichlet(a,…,a)` for **every**
transition row.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical BigOperators

open Mettapedia.Logic.EvidenceDirichlet

open FiniteAlphabet
open FiniteAlphabet.FiniteHorizon
open FiniteAlphabet.SolomonoffBridge

namespace MarkovDirichletHyperprior

/-! ## A countable symmetric Markov-Dirichlet family -/

variable {k : ℕ} (hk : 0 < k)

/-- A simple countable positive grid of symmetric Dirichlet parameters.

We use the half-integers `(n+1)/2`, so the family includes:
* `n = 0`  → `a = 1/2` (Jeffreys/KT analogue),
* `n = 1`  → `a = 1`   (Laplace),
* `n = 2`  → `a = 3/2`, etc.
-/
def a (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ) / 2

lemma a_pos (n : ℕ) : 0 < a n := by
  unfold a
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by
    exact_mod_cast Nat.succ_pos n
  have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
  exact div_pos hn h2

/-- Symmetric Markov(1) predictor: `Dirichlet(a,…,a)` priors for every transition row. -/
noncomputable def markovSymmetric (n : ℕ) : PrefixMeasure (Fin k) :=
  MarkovDirichlet.markovDirichletPrefixMeasure (k := k) hk
    (fun _ => DirichletParams.uniform (a n) (a_pos n))

theorem markovSymmetric_ne_zero (n : ℕ) : ∀ xs : List (Fin k), markovSymmetric hk n xs ≠ 0 := by
  intro xs
  simpa [markovSymmetric] using
    (MarkovDirichlet.markovDirichletPrefixMeasure_ne_zero (k := k) hk
      (prior := fun _ => DirichletParams.uniform (a n) (a_pos n)) xs)

/-! ## Hyperprior mixture over the family -/

/-- Hyperprior weight on the index `n`. We reuse the canonical self-delimiting weights
`2^{-(n+1)}` which sum to `1`. -/
noncomputable def w (n : ℕ) : ENNReal := geometricWeight n

theorem tsum_w : (∑' n : ℕ, w n) = 1 := by
  simpa [w] using (tsum_geometricWeight : (∑' n : ℕ, geometricWeight n) = 1)

/-- The hyperprior mixture predictor over the symmetric Markov-Dirichlet family. -/
noncomputable def mixture : PrefixMeasure (Fin k) :=
  xiPrefixMeasure (ν := fun n : ℕ => markovSymmetric hk n) (w := w) (hw := tsum_w)

/-! ## Componentwise dominance and the immediate KL bound -/

theorem dominates_component (n : ℕ) :
    FiniteAlphabet.Dominates (mixture hk).toSemimeasure (markovSymmetric hk n) (w n) := by
  intro x
  unfold mixture FiniteAlphabet.xiPrefixMeasure FiniteAlphabet.PrefixMeasure.toSemimeasure
  simpa [FiniteAlphabet.xiFun, w] using
    (FiniteAlphabet.xi_dominates_index
      (ν := fun i : ℕ => (markovSymmetric hk i).toSemimeasure)
      (w := w) (i := n) (x := x))

private theorem w_ne_zero (n : ℕ) : w n ≠ 0 := by
  have hpos : 0 < w n := by
    have h2_0 : (2 : ENNReal) ≠ 0 := by norm_num
    have h2_top : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
    simpa [w, geometricWeight] using
      (ENNReal.zpow_pos (a := (2 : ENNReal)) h2_0 h2_top (-1 - (n : ℤ)))
  exact ne_of_gt hpos

theorem relEntropy_le_log_inv_component (n N : ℕ) :
    relEntropy (markovSymmetric hk n) (mixture hk).toSemimeasure N ≤ Real.log (1 / (w n).toReal) := by
  have hdom : FiniteAlphabet.Dominates (mixture hk).toSemimeasure (markovSymmetric hk n) (w n) :=
    dominates_component (hk := hk) n
  exact relEntropy_le_log_inv_of_dominates (μ := markovSymmetric hk n) (ξ := (mixture hk).toSemimeasure)
    (hdom := hdom) (hc0 := w_ne_zero n) N

/-! ## Best-expert bound (Hook B) -/

/-- **Hook B**: the mixture competes with every component on every environment `μ`.

This is the standard “best expert + log(1/w)” regret inequality derived directly from dominance.
-/
theorem relEntropy_le_component_add_log (μ : PrefixMeasure (Fin k)) (n N : ℕ) :
    relEntropy μ (mixture hk).toSemimeasure N ≤
      relEntropy μ (markovSymmetric hk n).toSemimeasure N + Real.log (1 / (w n).toReal) := by
  have hdom : FiniteAlphabet.Dominates (mixture hk).toSemimeasure (markovSymmetric hk n) (w n) :=
    dominates_component (hk := hk) n
  exact relEntropy_le_add_log_inv_of_dominates_right
    (μ := μ) (ξ := (mixture hk).toSemimeasure) (η := markovSymmetric hk n)
    (hdom := hdom) (hc0 := w_ne_zero n) (hη0 := markovSymmetric_ne_zero (hk := hk) n) N

/-- The hyperprior mixture assigns nonzero weight to every finite prefix. -/
theorem mixture_ne_zero :
    ∀ xs : List (Fin k), (mixture hk) xs ≠ 0 := by
  intro xs
  -- Use dominance of the `n = 0` component (any fixed component works).
  have hdom :
      FiniteAlphabet.Dominates (mixture hk).toSemimeasure (markovSymmetric hk 0) (w 0) :=
    dominates_component (hk := hk) 0
  have hleft0 : w 0 * (markovSymmetric hk 0) xs ≠ 0 := by
    -- `w 0 ≠ 0` and the component is everywhere nonzero.
    refine mul_ne_zero (w_ne_zero 0) ?_
    -- `markovSymmetric_ne_zero` already provides this.
    simpa using markovSymmetric_ne_zero (hk := hk) 0 xs
  intro hmix0
  -- If the mixture were `0`, dominance would force the LHS to be `0` too.
  have hle : w 0 * (markovSymmetric hk 0) xs ≤ (mixture hk).toSemimeasure xs := hdom xs
  have : w 0 * (markovSymmetric hk 0) xs ≤ 0 := by simpa [hmix0] using hle
  -- In `ENNReal`, `a ≤ 0` implies `a = 0`.
  have : w 0 * (markovSymmetric hk 0) xs = 0 := le_antisymm this (by simp)
  exact hleft0 this

/-! ## Lower semicomputability (Hutter, Chapter 2) -/

open Mettapedia.Computability.Hutter

namespace Computability

open MarkovDirichlet

/-!
To connect Hook‑B mixtures to the concrete finite-alphabet Solomonoff predictor `M₂`, we need a
Hutter-style enumerability witness: lower semicomputability of the real-valued map
`x ↦ (mixture hk x).toReal`.

The key observation is that each weighted component term is **exactly a rational number**
computable from the finite word:

* the hyperprior weight is `2^{-(n+1)}`
* the Markov-Dirichlet(1) symmetric predictor uses step probabilities of the form
  `(2*count + (n+1)) / (2*rowTotal + k*(n+1))`

So for each index `n` and word `x`, the real value `(w n * (markovSymmetric hk n) x).toReal` can be
written as an explicit `Nat` ratio.  This is sufficient to obtain `LowerSemicomputable` via the
generic `of_natRatio` lemma in `HutterComputabilityRational`.
-/

variable {k : ℕ} (hk : 0 < k)

/-! ### A Nat-level evaluator for the symmetric family

We compute the real value of each *weighted* component term

`(w n * (markovSymmetric hk n) x).toReal`

as an explicit ratio of natural numbers.  This supports a direct `LowerSemicomputable` proof via
`LowerSemicomputable.of_natRatio`.
-/

abbrev Word (k : ℕ) : Type := List (Fin k)

abbrev Counts (k : ℕ) : Type := Fin k → Fin k → ℕ

abbrev RowTotals (k : ℕ) : Type := Fin k → ℕ

def countsZero (k : ℕ) : Counts k := fun _ _ => 0

def rowTotalsZero (k : ℕ) : RowTotals k := fun _ => 0

def bumpCounts {k : ℕ} (C : Counts k) (prev next : Fin k) : Counts k :=
  fun i j => if i = prev ∧ j = next then C i j + 1 else C i j

def bumpRowTotals {k : ℕ} (R : RowTotals k) (prev : Fin k) : RowTotals k :=
  fun i => if i = prev then R i + 1 else R i

def stepNum (n : ℕ) {k : ℕ} (C : Counts k) (prev next : Fin k) : ℕ :=
  2 * C prev next + (n + 1)

def stepDen (n : ℕ) (k : ℕ) (R : RowTotals k) (prev : Fin k) : ℕ :=
  2 * R prev + k * (n + 1)

abbrev Acc (k : ℕ) : Type :=
  (Fin k × Counts k) × (RowTotals k × (ℕ × ℕ))

namespace Acc

def prev {k : ℕ} (st : Acc k) : Fin k := st.1.1
def counts {k : ℕ} (st : Acc k) : Counts k := st.1.2
def rowTotals {k : ℕ} (st : Acc k) : RowTotals k := st.2.1
def num {k : ℕ} (st : Acc k) : ℕ := st.2.2.1
def den {k : ℕ} (st : Acc k) : ℕ := st.2.2.2

end Acc

def stepAcc (n : ℕ) {k : ℕ} (st : Acc k) (next : Fin k) : Acc k :=
  ((next, bumpCounts (Acc.counts st) (Acc.prev st) next),
   (bumpRowTotals (Acc.rowTotals st) (Acc.prev st),
    (Acc.num st * stepNum n (Acc.counts st) (Acc.prev st) next,
     Acc.den st * stepDen n k (Acc.rowTotals st) (Acc.prev st))))

/-- Compute the numerator/denominator for the weighted term at hyper-index `n` and word `x`. -/
def termNumDen {k : ℕ} (n : ℕ) (x : Word k) : ℕ × ℕ :=
  match x with
  | [] =>
      -- `markovSymmetric n [] = 1`, so the term is just the hyperprior weight `2^{-(n+1)}`.
      (1, 2 ^ (n + 1))
  | b :: xs =>
      let st0 : Acc k := ((b, countsZero k), (rowTotalsZero k, (1, k)))
      let st := xs.foldl (stepAcc n) st0
      (Acc.num st, Acc.den st * 2 ^ (n + 1))

def termNum {k : ℕ} (p : ℕ × Word k) : ℕ :=
  (termNumDen (k := k) p.1 p.2).1

def termDen {k : ℕ} (p : ℕ × Word k) : ℕ :=
  (termNumDen (k := k) p.1 p.2).2

theorem termDen_pos {k : ℕ} (hk : 0 < k) (p : ℕ × Word k) : 0 < termDen (k := k) p := by
  rcases p with ⟨n, x⟩
  cases x with
  | nil =>
      simp [termDen, termNumDen]
  | cons b xs =>
      -- `k > 0` and the fold multiplies by strictly positive denominators.
      have hk' : 0 < k := hk
      have hstepDen_pos : ∀ (st : Acc k), 0 < stepDen n k (Acc.rowTotals st) (Acc.prev st) := by
        intro st
        -- `k*(n+1) > 0`, hence `2*row + k*(n+1) > 0`.
        unfold stepDen
        have hn : 0 < n + 1 := Nat.succ_pos n
        have hkn : 0 < k * (n + 1) := Nat.mul_pos hk' hn
        exact Nat.lt_of_lt_of_le hkn (Nat.le_add_left _ _)
      have hfold_den_pos :
          ∀ (st : Acc k), 0 < Acc.den st → 0 < Acc.den (xs.foldl (stepAcc n) st) := by
        intro st hst
        induction xs generalizing st with
        | nil =>
            simpa using hst
        | cons x xs ih =>
            -- One step multiplies by a positive factor, so positivity is preserved.
            have hst' : 0 < Acc.den (stepAcc n st x) := by
              -- `den` is multiplied by a strictly positive step denominator.
              -- (This avoids `simp` getting stuck on the tuple projections.)
              dsimp [stepAcc, Acc.den]
              exact Nat.mul_pos hst (hstepDen_pos st)
            simpa [List.foldl] using ih (st := stepAcc n st x) hst'
      have hden_pos :
          0 < Acc.den (xs.foldl (stepAcc n) ((b, countsZero k), (rowTotalsZero k, (1, k)))) := by
        exact hfold_den_pos (st := ((b, countsZero k), (rowTotalsZero k, (1, k)))) hk'
      -- Finish: multiply by `2^(n+1)`.
      have hpow : 0 < (2 ^ (n + 1) : ℕ) := pow_pos (by decide : (0 : ℕ) < 2) _
      -- `termDen` is the fold denominator times `2^(n+1)`.
      simpa [termDen, termNumDen] using Nat.mul_pos hden_pos hpow

/-! ### Helper lemma: explicit real value of the geometric weight -/

  private lemma neg_one_sub_nat (n : ℕ) : (-1 - (n : ℤ)) = Int.negSucc n := by
    -- `Int.negSucc n` is notation for `-(n+1)`.
    calc
      (-1 - (n : ℤ)) = -((n : ℤ) + 1) := by
        ring
      _ = Int.negSucc n := by
        -- `Int.negSucc_eq` is the canonical lemma: `negSucc n = -(↑n + 1)`.
        simp [Int.negSucc_eq]

private lemma geometricWeight_toReal (n : ℕ) : (geometricWeight n).toReal = (1 : ℝ) / (2 : ℝ) ^ (n + 1) := by
  unfold geometricWeight
  rw [neg_one_sub_nat]
  rw [zpow_negSucc]
  rw [ENNReal.toReal_inv]
  rw [ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofNat]
  rw [one_div]

/-! ### Markov-Dirichlet arithmetic bridge for `term_toReal_eq` -/

/-- Row totals are consistent with the transition-count matrix. -/
private def rowsOk {k : ℕ} (R : RowTotals k) (C : Counts k) : Prop :=
  ∀ i : Fin k, R i = ∑ j : Fin k, C i j

private lemma rowsOk_zero (k : ℕ) : rowsOk (rowTotalsZero k) (countsZero k) := by
  intro i
  simp [rowTotalsZero, countsZero]

private lemma sum_bumpCounts_row_self {k : ℕ} (C : Counts k) (prev next : Fin k) :
    (∑ j : Fin k, bumpCounts C prev next prev j) = (∑ j : Fin k, C prev j) + 1 := by
  classical
  calc
    (∑ j : Fin k, bumpCounts C prev next prev j)
        = ∑ j : Fin k, (if j = next then C prev j + 1 else C prev j) := by
            simp [bumpCounts]
    _ = ∑ j : Fin k, (C prev j + (if j = next then 1 else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          by_cases h : j = next
          · subst h
            simp
          · simp [h]
    _ = (∑ j : Fin k, C prev j) + ∑ j : Fin k, (if j = next then 1 else 0) := by
          simp [Finset.sum_add_distrib]
    _ = (∑ j : Fin k, C prev j) + 1 := by
          simp

private lemma sum_bumpCounts_row_of_ne {k : ℕ} (C : Counts k) {i prev next : Fin k} (hi : i ≠ prev) :
    (∑ j : Fin k, bumpCounts C prev next i j) = ∑ j : Fin k, C i j := by
  classical
  refine Finset.sum_congr rfl ?_
  intro j hj
  have : ¬(i = prev ∧ j = next) := by
    intro h
    exact hi h.1
  simp [bumpCounts, this]

private lemma rowsOk_stepAcc (n : ℕ) {k : ℕ} (st : Acc k) (next : Fin k)
    (h : rowsOk (Acc.rowTotals st) (Acc.counts st)) :
    rowsOk (Acc.rowTotals (stepAcc n st next)) (Acc.counts (stepAcc n st next)) := by
  intro i
  classical
  by_cases hi : i = Acc.prev st
  · subst hi
    have hRT : bumpRowTotals (Acc.rowTotals st) (Acc.prev st) (Acc.prev st) =
        Acc.rowTotals st (Acc.prev st) + 1 := by
      simp [bumpRowTotals]
    have hC : (∑ j : Fin k, bumpCounts (Acc.counts st) (Acc.prev st) next (Acc.prev st) j) =
        (∑ j : Fin k, Acc.counts st (Acc.prev st) j) + 1 := by
      simpa using sum_bumpCounts_row_self (C := Acc.counts st) (prev := Acc.prev st) (next := next)
    dsimp [stepAcc, Acc.rowTotals, Acc.counts]
    calc
      bumpRowTotals (Acc.rowTotals st) (Acc.prev st) (Acc.prev st)
          = (∑ j : Fin k, Acc.counts st (Acc.prev st) j) + 1 := by
              simp [hRT, h (Acc.prev st)]
      _ = ∑ j : Fin k, bumpCounts (Acc.counts st) (Acc.prev st) next (Acc.prev st) j := by
              simp [hC, add_comm]
  ·
    have hRT : bumpRowTotals (Acc.rowTotals st) (Acc.prev st) i = Acc.rowTotals st i := by
      simp [bumpRowTotals, hi]
    have hC : (∑ j : Fin k, bumpCounts (Acc.counts st) (Acc.prev st) next i j) =
        ∑ j : Fin k, Acc.counts st i j := by
      simpa using sum_bumpCounts_row_of_ne (C := Acc.counts st) (i := i) (prev := Acc.prev st) (next := next) hi
    dsimp [stepAcc, Acc.rowTotals, Acc.counts]
    calc
      bumpRowTotals (Acc.rowTotals st) (Acc.prev st) i
          = ∑ j : Fin k, Acc.counts st i j := by
              simp [hRT, h i]
      _ = ∑ j : Fin k, bumpCounts (Acc.counts st) (Acc.prev st) next i j := by
              simp [hC]

private lemma rowsOk_foldl (n : ℕ) {k : ℕ} (xs : List (Fin k)) (st : Acc k)
    (h : rowsOk (Acc.rowTotals st) (Acc.counts st)) :
    rowsOk (Acc.rowTotals (xs.foldl (stepAcc n) st)) (Acc.counts (xs.foldl (stepAcc n) st)) := by
  induction xs generalizing st with
  | nil =>
      simpa using h
  | cons a xs ih =>
      simpa [List.foldl] using
        ih (st := stepAcc n st a) (rowsOk_stepAcc (n := n) (st := st) (next := a) h)

private lemma stepProb_uniform_eq (n : ℕ) (st : Acc k) (next : Fin k)
    (h : rowsOk (Acc.rowTotals st) (Acc.counts st)) :
    MarkovDirichlet.stepProb (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
        ⟨Acc.counts st⟩ (Acc.prev st) next =
      (stepNum n (Acc.counts st) (Acc.prev st) next : ℝ) /
        (stepDen n k (Acc.rowTotals st) (Acc.prev st) : ℝ) := by
  classical
  unfold MarkovDirichlet.stepProb MarkovDirichlet.stepDenom stepNum stepDen a
  simp [DirichletParams.uniform, DirichletParams.totalConcentration]
  let tc : TransCounts k := ⟨Acc.counts st⟩
  have hrow : tc.rowTotal (Acc.prev st) = Acc.rowTotals st (Acc.prev st) := by
    have hprev : Acc.rowTotals st (Acc.prev st) = ∑ j : Fin k, Acc.counts st (Acc.prev st) j := h _
    simp [TransCounts.rowTotal, tc, hprev]
  have hrow' : (↑(tc.rowTotal (Acc.prev st)) : ℝ) = (Acc.rowTotals st (Acc.prev st) : ℝ) := by
    exact_mod_cast hrow
  rw [hrow']
  field_simp

private lemma ratio_foldl_eq (_hk : 0 < k) (n : ℕ) (st : Acc k) (xs : List (Fin k))
    (h : rowsOk (Acc.rowTotals st) (Acc.counts st)) :
    (Acc.num (xs.foldl (stepAcc n) st) : ℝ) / (Acc.den (xs.foldl (stepAcc n) st) : ℝ) =
      (Acc.num st : ℝ) / (Acc.den st : ℝ) *
        (MarkovDirichlet.prefixAux (k := k)
            (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
            (prev := Acc.prev st) (c := ⟨Acc.counts st⟩) xs).toReal := by
  classical
  induction xs generalizing st with
  | nil =>
      simp [MarkovDirichlet.prefixAux]
  | cons sym xs ih =>
      have hstep : rowsOk (Acc.rowTotals (stepAcc n st sym)) (Acc.counts (stepAcc n st sym)) :=
        rowsOk_stepAcc (n := n) (st := st) (next := sym) h
      have htc : TransCounts.bump ⟨Acc.counts st⟩ (Acc.prev st) sym = ⟨Acc.counts (stepAcc n st sym)⟩ := by
        rfl
      have hprob :
          MarkovDirichlet.stepProb (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
              ⟨Acc.counts st⟩ (Acc.prev st) sym =
            (stepNum n (Acc.counts st) (Acc.prev st) sym : ℝ) /
              (stepDen n k (Acc.rowTotals st) (Acc.prev st) : ℝ) :=
        stepProb_uniform_eq (n := n) (st := st) (next := sym) h
      have hprob0 :
          0 ≤ MarkovDirichlet.stepProb (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
              ⟨Acc.counts st⟩ (Acc.prev st) sym := by
        rw [hprob]
        exact div_nonneg (by exact_mod_cast Nat.zero_le _) (by exact_mod_cast Nat.zero_le _)
      have ih' := ih (st := stepAcc n st sym) hstep
      have hratio_step :
          (Acc.num (stepAcc n st sym) : ℝ) / (Acc.den (stepAcc n st sym) : ℝ) =
            (Acc.num st : ℝ) / (Acc.den st : ℝ) *
              ((stepNum n (Acc.counts st) (Acc.prev st) sym : ℝ) /
                (stepDen n k (Acc.rowTotals st) (Acc.prev st) : ℝ)) := by
        dsimp [stepAcc, Acc.num, Acc.den]
        simp [Nat.cast_mul, mul_div_mul_comm]
      have hprefix :
          (MarkovDirichlet.prefixAux (k := k)
              (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
              (prev := Acc.prev st) (c := ⟨Acc.counts st⟩) (sym :: xs)).toReal =
            MarkovDirichlet.stepProb (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                ⟨Acc.counts st⟩ (Acc.prev st) sym *
              (MarkovDirichlet.prefixAux (k := k)
                  (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
              (prev := Acc.prev (stepAcc n st sym))
              (c := ⟨Acc.counts (stepAcc n st sym)⟩) xs).toReal := by
        simp only [MarkovDirichlet.prefixAux, ENNReal.toReal_mul, ENNReal.toReal_ofReal hprob0]
        rw [htc]
        rfl
      have ih'' :
          (Acc.num (xs.foldl (stepAcc n) (stepAcc n st sym)) : ℝ) /
              (Acc.den (xs.foldl (stepAcc n) (stepAcc n st sym)) : ℝ) =
            ((Acc.num st : ℝ) / (Acc.den st : ℝ) *
                MarkovDirichlet.stepProb (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                  ⟨Acc.counts st⟩ (Acc.prev st) sym) *
              (MarkovDirichlet.prefixAux (k := k)
                  (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                  (prev := Acc.prev (stepAcc n st sym))
                  (c := ⟨Acc.counts (stepAcc n st sym)⟩) xs).toReal := by
        simpa [hratio_step, hprob, mul_assoc] using ih'
      have hmul :
          ((Acc.num st : ℝ) / (Acc.den st : ℝ) *
                MarkovDirichlet.stepProb (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                  ⟨Acc.counts st⟩ (Acc.prev st) sym) *
              (MarkovDirichlet.prefixAux (k := k)
                  (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                  (prev := Acc.prev (stepAcc n st sym))
                  (c := ⟨Acc.counts (stepAcc n st sym)⟩) xs).toReal =
            (Acc.num st : ℝ) / (Acc.den st : ℝ) *
              (MarkovDirichlet.prefixAux (k := k)
                  (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                  (prev := Acc.prev st) (c := ⟨Acc.counts st⟩) (sym :: xs)).toReal := by
        simp [hprefix, mul_assoc]
      simpa [List.foldl, hmul] using ih''

/-! ### Correctness: the Nat ratio equals the real-valued term -/

theorem term_toReal_eq (hk : 0 < k) (p : ℕ × Word k) :
    ((w p.1) * (markovSymmetric (k := k) hk p.1) p.2).toReal =
      (termNum (k := k) p : ℝ) / (termDen (k := k) p : ℝ) := by
  classical
  rcases p with ⟨n, x⟩
  cases x with
  | nil =>
      -- Empty word: `markovSymmetric n [] = 1`, so this is just the hyperprior weight.
      have hm : (markovSymmetric (k := k) hk n) ([] : Word k) = 1 := by
        -- `prefixProb prior [] = 1` by definition.
        simp [MarkovDirichletHyperprior.markovSymmetric, MarkovDirichlet.markovDirichletPrefixMeasure,
          MarkovDirichlet.prefixProb]
      simp [hm, termNum, termDen, termNumDen, MarkovDirichletHyperprior.w, w, geometricWeight_toReal]
  | cons b xs =>
      -- Nonempty word: the Markov(1) prefix probability is a product of rational step factors.
      -- We show its real value equals the accumulator ratio `Acc.num/Acc.den` computed by `termNumDen`.
      --
      -- First rewrite the overall term as weight * prefixProb.
      have hweight : (w n).toReal = (1 : ℝ) / (2 : ℝ) ^ (n + 1) := by
        simpa [MarkovDirichletHyperprior.w, w] using geometricWeight_toReal n
      -- Unfold the Markov-Dirichlet definition.
      -- This is the symmetric prior with `a = (n+1)/2` on every row.
      have hprior : (markovSymmetric (k := k) hk n) (b :: xs) =
          MarkovDirichlet.prefixProb (k := k)
            (fun _ => DirichletParams.uniform (a n) (a_pos n)) (b :: xs) := by
        -- `markovSymmetric` is defined as the `markovDirichletPrefixMeasure` wrapper around `prefixProb`.
        simp [MarkovDirichletHyperprior.markovSymmetric, MarkovDirichlet.markovDirichletPrefixMeasure]
      -- Define the initial accumulator state used by `termNumDen`.
      let st0 : Acc k := ((b, countsZero k), (rowTotalsZero k, (1, k)))
      let st : Acc k := xs.foldl (stepAcc n) st0
      have htermDen : termDen (k := k) (n, b :: xs) = Acc.den st * 2 ^ (n + 1) := by
        simp [termDen, termNumDen, st, st0]
      have htermNum : termNum (k := k) (n, b :: xs) = Acc.num st := by
        simp [termNum, termNumDen, st, st0]
      -- Reduce the goal to showing `toReal (prefixProb ...) = num/den`.
      have hpref :
          (MarkovDirichlet.prefixProb (k := k)
              (fun _ => DirichletParams.uniform (a n) (a_pos n)) (b :: xs)).toReal =
            (Acc.num st : ℝ) / (Acc.den st : ℝ) := by
        -- Use the accumulator lemma `ratio_foldl_eq` specialized to the initial state `st0`.
        have hrows : rowsOk (Acc.rowTotals st0) (Acc.counts st0) := by
          simpa [st0, Acc.rowTotals, Acc.counts] using rowsOk_zero k
        have hratio :
            (Acc.num st : ℝ) / (Acc.den st : ℝ) =
              (Acc.num st0 : ℝ) / (Acc.den st0 : ℝ) *
                (MarkovDirichlet.prefixAux (k := k)
                    (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                    (prev := Acc.prev st0) (c := ⟨Acc.counts st0⟩) xs).toReal := by
          simpa [st, st0] using ratio_foldl_eq (k := k) (_hk := hk) (n := n) (st := st0) (xs := xs) hrows
        have hinit0 : 0 ≤ MarkovDirichlet.initProb (k := k) b := by
          unfold MarkovDirichlet.initProb
          have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
          exact one_div_nonneg.2 hk0
        have hpp :
            (MarkovDirichlet.prefixProb (k := k)
                (fun _ => DirichletParams.uniform (a n) (a_pos n)) (b :: xs)).toReal =
              MarkovDirichlet.initProb (k := k) b *
                (MarkovDirichlet.prefixAux (k := k)
                    (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                    (prev := b) (c := TransCounts.zero) xs).toReal := by
          simp [MarkovDirichlet.prefixProb, ENNReal.toReal_mul, ENNReal.toReal_ofReal hinit0]
        -- The accumulator starts with `num/den = 1/k`, matching the uniform initial probability.
        -- Use `ratio_foldl_eq` to identify the full prefix probability with the final accumulator ratio.
        calc
          (MarkovDirichlet.prefixProb (k := k)
              (fun _ => DirichletParams.uniform (a n) (a_pos n)) (b :: xs)).toReal
              = MarkovDirichlet.initProb (k := k) b *
                  (MarkovDirichlet.prefixAux (k := k)
                      (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                      (prev := b) (c := TransCounts.zero) xs).toReal := hpp
          _ = ((Acc.num st0 : ℝ) / (Acc.den st0 : ℝ)) *
                  (MarkovDirichlet.prefixAux (k := k)
                      (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                      (prev := Acc.prev st0) (c := ⟨Acc.counts st0⟩) xs).toReal := by
                -- `st0.num = 1`, `st0.den = k`, and `TransCounts.zero = ⟨countsZero⟩`.
                have hinit :
                    MarkovDirichlet.initProb (k := k) b = (Acc.num st0 : ℝ) / (Acc.den st0 : ℝ) := by
                  simp [st0, Acc.num, Acc.den, MarkovDirichlet.initProb, div_eq_mul_inv]
                have haux :
                    (MarkovDirichlet.prefixAux (k := k)
                          (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                          (prev := b) (c := TransCounts.zero) xs).toReal =
                        (MarkovDirichlet.prefixAux (k := k)
                          (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                          (prev := Acc.prev st0) (c := ⟨Acc.counts st0⟩) xs).toReal := by
                  -- Reduce `TransCounts.zero` and the initial accumulator's counts.
                  have hcounts : (TransCounts.zero (k := k)) = ⟨countsZero k⟩ := by
                    ext i j
                    simp [TransCounts.zero, countsZero]
                  simp [st0, Acc.prev, Acc.counts, hcounts]
                -- Rewrite the initial factor via `hinit`, then align the `prefixAux` terms via `haux`.
                calc
                  MarkovDirichlet.initProb (k := k) b *
                      (MarkovDirichlet.prefixAux (k := k)
                          (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                          (prev := b) (c := TransCounts.zero) xs).toReal
                      =
                      ((Acc.num st0 : ℝ) / (Acc.den st0 : ℝ)) *
                        (MarkovDirichlet.prefixAux (k := k)
                          (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                          (prev := b) (c := TransCounts.zero) xs).toReal := by
                    simp [hinit]
                  _ =
                      ((Acc.num st0 : ℝ) / (Acc.den st0 : ℝ)) *
                        (MarkovDirichlet.prefixAux (k := k)
                          (prior := fun _ => DirichletParams.uniform (a n) (a_pos n))
                          (prev := Acc.prev st0) (c := ⟨Acc.counts st0⟩) xs).toReal := by
                    simp [haux]
          _ = (Acc.num st : ℝ) / (Acc.den st : ℝ) := by
                simpa using hratio.symm
      -- Combine the pieces.
      -- LHS is weight * prefixProb.
      have hleft :
          ((w n) * (markovSymmetric (k := k) hk n) (b :: xs)).toReal =
            (w n).toReal * (MarkovDirichlet.prefixProb (k := k)
                (fun _ => DirichletParams.uniform (a n) (a_pos n)) (b :: xs)).toReal := by
        -- Use `toReal_mul` and the unfolding lemma.
        simp [hprior, ENNReal.toReal_mul]
      -- RHS is the Nat ratio.
      calc
        ((w n) * (markovSymmetric (k := k) hk n) (b :: xs)).toReal
            = (w n).toReal *
                (MarkovDirichlet.prefixProb (k := k)
                  (fun _ => DirichletParams.uniform (a n) (a_pos n)) (b :: xs)).toReal := hleft
        _ = ((1 : ℝ) / (2 : ℝ) ^ (n + 1)) * ((Acc.num st : ℝ) / (Acc.den st : ℝ)) := by
              simp [hweight, hpref]
        _ = (Acc.num st : ℝ) / (Acc.den st * 2 ^ (n + 1) : ℝ) := by
              -- Rearrange: `(1/2^(n+1)) * (num/den) = num/(den*2^(n+1))`.
              field_simp
        _ = (termNum (k := k) (n, b :: xs) : ℝ) / (termDen (k := k) (n, b :: xs) : ℝ) := by
              simp [htermNum, htermDen]

/-! ### Lower semicomputability of the hyperprior mixture -/

/-!
`LowerSemicomputable.of_natRatio` requires the Nat-level evaluators `termNum` and `termDen` to be
computable.  These evaluators are definable using primitive recursion on lists together with basic
arithmetic and `Fin`-indexed tables, but Lean does not infer `Computable` automatically.

We discharge this by proving the stronger statement that the evaluators are **primitive recursive**
(`Primrec`) and then using `Primrec.to_comp`.
-/

namespace PrimrecHelpers

open Primrec

private theorem rowTotals_eval_primrec {k : ℕ} :
    Primrec (fun p : RowTotals k × Fin k => (p.1 : RowTotals k) p.2) := by
  have happ : Primrec₂ (@id (Fin k → ℕ)) := by
    simpa using (Primrec.fin_app (σ := ℕ) (n := k))
  simpa using (Primrec₂.comp happ (Primrec.fst) (Primrec.snd))

private theorem counts_eval_primrec {k : ℕ} :
    Primrec (fun p : Counts k × (Fin k × Fin k) => (p.1 : Counts k) p.2.1 p.2.2) := by
  have happ1 : Primrec₂ (@id (Fin k → (Fin k → ℕ))) := by
    simpa using (Primrec.fin_app (σ := (Fin k → ℕ)) (n := k))
  have happ2 : Primrec₂ (@id (Fin k → ℕ)) := by
    simpa using (Primrec.fin_app (σ := ℕ) (n := k))
  have hCi : Primrec (fun p : Counts k × (Fin k × Fin k) => ((p.1 : Counts k) p.2.1 : Fin k → ℕ)) := by
    have hC : Primrec (fun p : Counts k × (Fin k × Fin k) => (p.1 : Counts k)) := by
      simpa using (Primrec.fst)
    have hi : Primrec (fun p : Counts k × (Fin k × Fin k) => (p.2.1 : Fin k)) := by
      simpa using (Primrec.fst.comp Primrec.snd)
    simpa using (Primrec₂.comp happ1 hC hi)
  have hj : Primrec (fun p : Counts k × (Fin k × Fin k) => (p.2.2 : Fin k)) := by
    simpa using (Primrec.snd.comp Primrec.snd)
  simpa using (Primrec₂.comp happ2 hCi hj)

private theorem bumpRowTotals_primrec {k : ℕ} :
    Primrec (fun p : RowTotals k × Fin k => bumpRowTotals (k := k) p.1 p.2) := by
  have happ : Primrec₂ (@id (Fin k → ℕ)) := by
    simpa using (Primrec.fin_app (σ := ℕ) (n := k))
  have hEval : Primrec₂ (fun p : RowTotals k × Fin k => fun i : Fin k =>
      bumpRowTotals (k := k) p.1 p.2 i) := by
    unfold Primrec₂
    have hPred : PrimrecPred (fun q : (RowTotals k × Fin k) × Fin k => q.2 = q.1.2) := by
      refine PrimrecRel.comp (R := (@Eq (Fin k))) (hR := Primrec.eq)
        (hf := Primrec.snd) (hg := Primrec.snd.comp Primrec.fst)
    have hRi : Primrec (fun q : (RowTotals k × Fin k) × Fin k => (q.1.1 : RowTotals k) q.2) := by
      have hR : Primrec (fun q : (RowTotals k × Fin k) × Fin k => (q.1.1 : RowTotals k)) := by
        simpa using (Primrec.fst.comp Primrec.fst)
      have hi : Primrec (fun q : (RowTotals k × Fin k) × Fin k => (q.2 : Fin k)) := by
        simpa using Primrec.snd
      simpa using (Primrec₂.comp happ hR hi)
    have hRi_succ : Primrec (fun q : (RowTotals k × Fin k) × Fin k => (q.1.1 : RowTotals k) q.2 + 1) := by
      simpa using (Primrec.succ.comp hRi)
    have : Primrec (fun q : (RowTotals k × Fin k) × Fin k =>
        if q.2 = q.1.2 then (q.1.1 : RowTotals k) q.2 + 1 else (q.1.1 : RowTotals k) q.2) :=
      Primrec.ite hPred hRi_succ hRi
    simpa [bumpRowTotals] using this
  have hCurried :
      Primrec (fun p : RowTotals k × Fin k => fun i : Fin k => bumpRowTotals (k := k) p.1 p.2 i) :=
    (Primrec.fin_curry (α := RowTotals k × Fin k) (σ := ℕ) (n := k)).2 hEval
  simpa [RowTotals] using hCurried

private theorem bumpCounts_primrec {k : ℕ} :
    Primrec (fun p : (Counts k × Fin k) × Fin k => bumpCounts (k := k) p.1.1 p.1.2 p.2) := by
  let P : Type := (Counts k × Fin k) × Fin k
  have happ1 : Primrec₂ (@id (Fin k → (Fin k → ℕ))) := by
    simpa using (Primrec.fin_app (σ := (Fin k → ℕ)) (n := k))
  have happ2 : Primrec₂ (@id (Fin k → ℕ)) := by
    simpa using (Primrec.fin_app (σ := ℕ) (n := k))
  have hUnc : Primrec (fun q : (P × Fin k) × Fin k =>
      if q.1.2 = q.1.1.1.2 ∧ q.2 = q.1.1.2 then
        (q.1.1.1.1 q.1.2 q.2 + 1)
      else
        (q.1.1.1.1 q.1.2 q.2)) := by
    have hEq_i : PrimrecPred (fun q : (P × Fin k) × Fin k => q.1.2 = q.1.1.1.2) := by
      refine PrimrecRel.comp (R := (@Eq (Fin k))) (hR := Primrec.eq)
        (hf := Primrec.snd.comp (Primrec.fst))
        (hg := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))))
    have hEq_j : PrimrecPred (fun q : (P × Fin k) × Fin k => q.2 = q.1.1.2) := by
      refine PrimrecRel.comp (R := (@Eq (Fin k))) (hR := Primrec.eq)
        (hf := Primrec.snd) (hg := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))
    have hPred : PrimrecPred (fun q : (P × Fin k) × Fin k => q.1.2 = q.1.1.1.2 ∧ q.2 = q.1.1.2) :=
      PrimrecPred.and hEq_i hEq_j
    have hCi : Primrec (fun q : (P × Fin k) × Fin k => ((q.1.1.1.1) (q.1.2) : Fin k → ℕ)) := by
      have hC : Primrec (fun q : (P × Fin k) × Fin k => (q.1.1.1.1 : Counts k)) := by
        simpa using (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))))
      have hi : Primrec (fun q : (P × Fin k) × Fin k => (q.1.2 : Fin k)) := by
        simpa using (Primrec.snd.comp Primrec.fst)
      simpa using (Primrec₂.comp happ1 hC hi)
    have hCij : Primrec (fun q : (P × Fin k) × Fin k => (q.1.1.1.1 q.1.2 q.2 : ℕ)) := by
      have hj : Primrec (fun q : (P × Fin k) × Fin k => (q.2 : Fin k)) := by
        simpa using Primrec.snd
      simpa using (Primrec₂.comp happ2 hCi hj)
    have hCij_succ : Primrec (fun q : (P × Fin k) × Fin k => q.1.1.1.1 q.1.2 q.2 + 1) := by
      simpa using (Primrec.succ.comp hCij)
    exact Primrec.ite hPred hCij_succ hCij
  have hF : Primrec (fun r : P × Fin k => fun j : Fin k =>
      if r.2 = r.1.1.2 ∧ j = r.1.2 then (r.1.1.1 r.2 j + 1) else (r.1.1.1 r.2 j)) := by
    have hF2 : Primrec₂ (fun r : P × Fin k => fun j : Fin k =>
        if r.2 = r.1.1.2 ∧ j = r.1.2 then (r.1.1.1 r.2 j + 1) else (r.1.1.1 r.2 j)) := by
      unfold Primrec₂
      simpa using hUnc
    exact (Primrec.fin_curry (α := P × Fin k) (σ := ℕ) (n := k)).2 hF2
  have hG2 :
      Primrec₂ (Function.curry (fun r : (P × Fin k) => (fun j : Fin k =>
        if r.2 = r.1.1.2 ∧ j = r.1.2 then (r.1.1.1 r.2 j + 1) else (r.1.1.1 r.2 j)))) := by
    have : Primrec (fun r : P × Fin k => (fun j : Fin k =>
        if r.2 = r.1.1.2 ∧ j = r.1.2 then (r.1.1.1 r.2 j + 1) else (r.1.1.1 r.2 j))) := hF
    exact (Primrec₂.curry).2 this
  have hG :
      Primrec (Function.curry (fun r : (P × Fin k) => (fun j : Fin k =>
        if r.2 = r.1.1.2 ∧ j = r.1.2 then (r.1.1.1 r.2 j + 1) else (r.1.1.1 r.2 j)))) := by
    exact (Primrec.fin_curry (α := P) (σ := (Fin k → ℕ)) (n := k)).2 hG2
  exact hG.of_eq (by
    intro p
    rfl)

private theorem stepAcc_primrec {k : ℕ} :
    Primrec₂ (fun p : (ℕ × Acc k) => fun next : Fin k => stepAcc (k := k) p.1 p.2 next) := by
  have hMul : Primrec₂ ((· * ·) : ℕ → ℕ → ℕ) := Primrec.nat_mul
  have hAdd : Primrec₂ ((· + ·) : ℕ → ℕ → ℕ) := Primrec.nat_add
  -- Unfold to a unary `Primrec` on `((ℕ × Acc k) × Fin k)` and assemble componentwise.
  unfold Primrec₂
  have hn : Primrec (fun q : (ℕ × Acc k) × Fin k => (q.1.1 : ℕ)) := by
    simpa using (Primrec.fst.comp Primrec.fst)
  have hst : Primrec (fun q : (ℕ × Acc k) × Fin k => (q.1.2 : Acc k)) := by
    simpa using (Primrec.snd.comp Primrec.fst)
  have hnext : Primrec (fun q : (ℕ × Acc k) × Fin k => (q.2 : Fin k)) := by
    simpa using Primrec.snd

  -- Extract components from the accumulator.
  have hprev : Primrec (fun q : (ℕ × Acc k) × Fin k => (q.1.2.1.1 : Fin k)) := by
    simpa [Acc.prev] using (Primrec.fst.comp (Primrec.fst.comp hst))
  have hcounts : Primrec (fun q : (ℕ × Acc k) × Fin k => (q.1.2.1.2 : Counts k)) := by
    simpa [Acc.counts] using (Primrec.snd.comp (Primrec.fst.comp hst))
  have hrowTotals : Primrec (fun q : (ℕ × Acc k) × Fin k => (q.1.2.2.1 : RowTotals k)) := by
    simpa [Acc.rowTotals] using (Primrec.fst.comp (Primrec.snd.comp hst))
  have hnum : Primrec (fun q : (ℕ × Acc k) × Fin k => (q.1.2.2.2.1 : ℕ)) := by
    simpa [Acc.num] using (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hst)))
  have hden : Primrec (fun q : (ℕ × Acc k) × Fin k => (q.1.2.2.2.2 : ℕ)) := by
    simpa [Acc.den] using (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hst)))

  -- Lookups: `C prev next` and `R prev`.
  have hCprevnext : Primrec (fun q : (ℕ × Acc k) × Fin k => (q.1.2.1.2 : Counts k) (q.1.2.1.1) q.2) := by
    have hPack : Primrec (fun q : (ℕ × Acc k) × Fin k =>
        ((q.1.2.1.2 : Counts k), (q.1.2.1.1, q.2))) :=
      Primrec.pair hcounts (Primrec.pair hprev hnext)
    simpa using (counts_eval_primrec (k := k)).comp hPack

  have hRprev : Primrec (fun q : (ℕ × Acc k) × Fin k => (q.1.2.2.1 : RowTotals k) (q.1.2.1.1)) := by
    have hPack : Primrec (fun q : (ℕ × Acc k) × Fin k =>
        ((q.1.2.2.1 : RowTotals k), (q.1.2.1.1 : Fin k))) :=
      Primrec.pair hrowTotals hprev
    simpa using (rowTotals_eval_primrec (k := k)).comp hPack

  have hn1 : Primrec (fun q : (ℕ × Acc k) × Fin k => q.1.1 + 1) := by
    simpa using (Primrec.succ.comp hn)

  -- Step factors: `2*C + (n+1)` and `2*R + k*(n+1)`.
  have hStepNum : Primrec (fun q : (ℕ × Acc k) × Fin k => 2 * ((q.1.2.1.2 : Counts k) (q.1.2.1.1) q.2) + (q.1.1 + 1)) := by
    have h2mul : Primrec (fun q : (ℕ × Acc k) × Fin k => 2 * ((q.1.2.1.2 : Counts k) (q.1.2.1.1) q.2)) := by
      simpa using (Primrec₂.comp hMul (Primrec.const 2) hCprevnext)
    simpa using (Primrec₂.comp hAdd h2mul hn1)

  have hStepDen : Primrec (fun q : (ℕ × Acc k) × Fin k => 2 * ((q.1.2.2.1 : RowTotals k) (q.1.2.1.1)) + k * (q.1.1 + 1)) := by
    have h2mul : Primrec (fun q : (ℕ × Acc k) × Fin k => 2 * ((q.1.2.2.1 : RowTotals k) (q.1.2.1.1))) := by
      simpa using (Primrec₂.comp hMul (Primrec.const 2) hRprev)
    have hkmul : Primrec (fun q : (ℕ × Acc k) × Fin k => k * (q.1.1 + 1)) := by
      simpa using (Primrec₂.comp hMul (Primrec.const k) hn1)
    simpa using (Primrec₂.comp hAdd h2mul hkmul)

  -- Updated evidence tables.
  have hCounts' : Primrec (fun q : (ℕ × Acc k) × Fin k =>
      bumpCounts (k := k) (q.1.2.1.2 : Counts k) (q.1.2.1.1) q.2) := by
    have hPack : Primrec (fun q : (ℕ × Acc k) × Fin k =>
        (((q.1.2.1.2 : Counts k), (q.1.2.1.1 : Fin k)), (q.2 : Fin k))) :=
      Primrec.pair (Primrec.pair hcounts hprev) hnext
    simpa using (bumpCounts_primrec (k := k)).comp hPack

  have hRowTotals' : Primrec (fun q : (ℕ × Acc k) × Fin k =>
      bumpRowTotals (k := k) (q.1.2.2.1 : RowTotals k) (q.1.2.1.1)) := by
    have hPack : Primrec (fun q : (ℕ × Acc k) × Fin k =>
        ((q.1.2.2.1 : RowTotals k), (q.1.2.1.1 : Fin k))) :=
      Primrec.pair hrowTotals hprev
    simpa using (bumpRowTotals_primrec (k := k)).comp hPack

  have hNum' : Primrec (fun q : (ℕ × Acc k) × Fin k => (q.1.2.2.2.1 : ℕ) * (2 * (q.1.2.1.2 : Counts k) (q.1.2.1.1) q.2 + (q.1.1 + 1))) := by
    simpa using (Primrec₂.comp hMul hnum hStepNum)
  have hDen' : Primrec (fun q : (ℕ × Acc k) × Fin k => (q.1.2.2.2.2 : ℕ) * (2 * (q.1.2.2.1 : RowTotals k) (q.1.2.1.1) + k * (q.1.1 + 1))) := by
    simpa using (Primrec₂.comp hMul hden hStepDen)

  have hStep :=
    Primrec.pair (Primrec.pair hnext hCounts') (Primrec.pair hRowTotals' (Primrec.pair hNum' hDen'))
  simpa [stepAcc, stepNum, stepDen, Acc.prev, Acc.counts, Acc.rowTotals, Acc.num, Acc.den] using hStep

private theorem termNumDen_primrec {k : ℕ} :
    Primrec (fun p : ℕ × Word k => termNumDen (k := k) p.1 p.2) := by
  have hPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
    Primrec₂.unpaired'.1 Nat.Primrec.pow
  -- Case split on the word argument.
  refine (Primrec.list_casesOn
    (f := fun p : ℕ × Word k => p.2)
    (g := fun p : ℕ × Word k => (1, (2 : ℕ) ^ (p.1 + 1)))
    (h := fun p : ℕ × Word k => fun t : Fin k × Word k =>
      let n := p.1
      let b := t.1
      let xs := t.2
      let st0 : Acc k := ((b, countsZero k), (rowTotalsZero k, (1, k)))
      let st := xs.foldl (stepAcc (k := k) n) st0
      (Acc.num st, Acc.den st * (2 : ℕ) ^ (n + 1)))
    Primrec.snd
    ?_ ?_).of_eq ?_
  · -- nil case: `(1, 2^(n+1))`
    have hn1 : Primrec (fun p : ℕ × Word k => p.1 + 1) := by
      simpa using (Primrec.succ.comp Primrec.fst)
    have hpow : Primrec (fun p : ℕ × Word k => (2 : ℕ) ^ (p.1 + 1)) := by
      simpa using (Primrec₂.comp hPow (Primrec.const 2) hn1)
    simpa using (Primrec.pair (Primrec.const 1) hpow)
  · -- cons case
    unfold Primrec₂
    let foldFun : (ℕ × Word k) × (Fin k × Word k) → Acc k :=
      fun u =>
        (u.2.2).foldl (fun st next => stepAcc (k := k) u.1.1 st next)
          ((u.2.1, countsZero k), (rowTotalsZero k, (1, k)))
    -- Fold on `xs` with step function `stepAcc n`.
    have hFold : Primrec foldFun := by
      have hf : Primrec (fun u : (ℕ × Word k) × (Fin k × Word k) => (u.2.2 : Word k)) := by
        simpa using (Primrec.snd.comp Primrec.snd)
      have hg : Primrec (fun u : (ℕ × Word k) × (Fin k × Word k) =>
          ((u.2.1, countsZero k), (rowTotalsZero k, (1, k)))) := by
        have hb : Primrec (fun u : (ℕ × Word k) × (Fin k × Word k) => (u.2.1 : Fin k)) := by
          simpa using (Primrec.fst.comp Primrec.snd)
        exact
          (Primrec.pair
            (Primrec.pair hb (Primrec.const (countsZero k)))
            (Primrec.pair (Primrec.const (rowTotalsZero k)) (Primrec.pair (Primrec.const 1) (Primrec.const k))))
      have hh : Primrec₂ (fun u : (ℕ × Word k) × (Fin k × Word k) => fun q : Acc k × Fin k =>
          stepAcc (k := k) u.1.1 q.1 q.2) := by
        unfold Primrec₂
        -- Package `((n,st),next)` for `stepAcc_primrec`.
        have hPack : Primrec (fun z : ((ℕ × Word k) × (Fin k × Word k)) × (Acc k × Fin k) =>
            (((z.1.1.1 : ℕ), (z.2.1 : Acc k)), (z.2.2 : Fin k))) := by
          have hn : Primrec (fun z : ((ℕ × Word k) × (Fin k × Word k)) × (Acc k × Fin k) => (z.1.1.1 : ℕ)) := by
            simpa using (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          have hst : Primrec (fun z : ((ℕ × Word k) × (Fin k × Word k)) × (Acc k × Fin k) => (z.2.1 : Acc k)) := by
            simpa using (Primrec.fst.comp Primrec.snd)
          have ha : Primrec (fun z : ((ℕ × Word k) × (Fin k × Word k)) × (Acc k × Fin k) =>
              ((z.1.1.1 : ℕ), (z.2.1 : Acc k))) :=
            Primrec.pair hn hst
          have hnext : Primrec (fun z : ((ℕ × Word k) × (Fin k × Word k)) × (Acc k × Fin k) => (z.2.2 : Fin k)) := by
            simpa using (Primrec.snd.comp Primrec.snd)
          exact Primrec.pair ha hnext
        have hStepUnc : Primrec (fun p : (ℕ × Acc k) × Fin k =>
            stepAcc (k := k) p.1.1 p.1.2 p.2) := by
          simpa [Primrec₂] using (stepAcc_primrec (k := k))
        simpa using hStepUnc.comp hPack
      simpa [foldFun] using (Primrec.list_foldl hf hg hh)
    -- Combine fold results into the `(num, den * 2^(n+1))` pair.
    have hn : Primrec (fun u : (ℕ × Word k) × (Fin k × Word k) => (u.1.1 : ℕ)) := by
      simpa using (Primrec.fst.comp Primrec.fst)
    have hn1 : Primrec (fun u : (ℕ × Word k) × (Fin k × Word k) => u.1.1 + 1) := by
      simpa using (Primrec.succ.comp hn)
    have hpow : Primrec (fun u : (ℕ × Word k) × (Fin k × Word k) => (2 : ℕ) ^ (u.1.1 + 1)) := by
      simpa using (Primrec₂.comp hPow (Primrec.const 2) hn1)
    have hnumFold : Primrec (fun u : (ℕ × Word k) × (Fin k × Word k) => Acc.num (foldFun u)) := by
      simpa [Acc.num, foldFun] using (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hFold)))
    have hdenFold : Primrec (fun u : (ℕ × Word k) × (Fin k × Word k) => Acc.den (foldFun u)) := by
      simpa [Acc.den, foldFun] using (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hFold)))
    have hdenMul : Primrec (fun u : (ℕ × Word k) × (Fin k × Word k) => Acc.den (foldFun u) * (2 : ℕ) ^ (u.1.1 + 1)) := by
      simpa using (Primrec₂.comp Primrec.nat_mul hdenFold hpow)
    have hpair : Primrec (fun u : (ℕ × Word k) × (Fin k × Word k) =>
        (Acc.num (foldFun u), Acc.den (foldFun u) * (2 : ℕ) ^ (u.1.1 + 1))) :=
      Primrec.pair hnumFold hdenMul
    simpa [termNumDen, foldFun, Acc.num, Acc.den] using hpair
  · intro p
    rcases p with ⟨n, x⟩
    cases x <;> rfl

end PrimrecHelpers

theorem termNum_computable {k : ℕ} : Computable (termNum (k := k)) := by
  classical
  have h : Primrec (termNum (k := k)) :=
    Primrec.fst.comp (PrimrecHelpers.termNumDen_primrec (k := k))
  exact h.to_comp

theorem termDen_computable {k : ℕ} : Computable (termDen (k := k)) := by
  classical
  have h : Primrec (termDen (k := k)) :=
    Primrec.snd.comp (PrimrecHelpers.termNumDen_primrec (k := k))
  exact h.to_comp

theorem lsc_term (hk : 0 < k) :
    LowerSemicomputable (fun p : ℕ × Word k =>
      ((w p.1) * (markovSymmetric (k := k) hk p.1) p.2).toReal) := by
  -- First show the Nat-ratio is lower semicomputable.
  have hRat :
      LowerSemicomputable (fun p : ℕ × Word k =>
        (termNum (k := k) p : ℝ) / (termDen (k := k) p : ℝ)) := by
    simpa using
      (LowerSemicomputable.of_natRatio (α := ℕ × Word k)
        (num := termNum (k := k)) (den := termDen (k := k))
        (hnum := termNum_computable (k := k))
        (hden := termDen_computable (k := k))
        (hden_pos := termDen_pos (k := k) hk))
  -- Then rewrite the target pointwise using `term_toReal_eq`.
  refine LowerSemicomputable.congr (f := fun p : ℕ × Word k =>
      (termNum (k := k) p : ℝ) / (termDen (k := k) p : ℝ))
    (g := fun p : ℕ × Word k =>
      ((w p.1) * (markovSymmetric (k := k) hk p.1) p.2).toReal) hRat ?_
  intro p
  symm
  simpa using term_toReal_eq (k := k) hk p

theorem mixture_lsc (hk : 0 < k) :
    FiniteAlphabet.LowerSemicomputablePrefixMeasure (α := Fin k) (mixture (k := k) hk) := by
  classical
  have hf_ne_top : ∀ n x, w n * (markovSymmetric (k := k) hk n) x ≠ ⊤ := by
    intro n x
    refine ENNReal.mul_ne_top ?_ ?_
    · -- weights are finite
      -- `w n = 2^(-1-n)` with base `2`, hence it is finite.
      have h2_0 : (2 : ENNReal) ≠ 0 := by norm_num
      have h2_top : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
      simpa [MarkovDirichletHyperprior.w, w, geometricWeight] using
        (ENNReal.zpow_ne_top (a := (2 : ENNReal)) h2_0 h2_top (-1 - (n : ℤ)))
    · -- prefix measures are semimeasures, hence finite
      exact (FiniteAlphabet.Semimeasure.ne_top (μ := (markovSymmetric (k := k) hk n).toSemimeasure) x)
  have hsum : ∀ x, Summable (fun n : ℕ => (w n * (markovSymmetric (k := k) hk n) x).toReal) := by
    intro x
    -- Use `ENNReal.summable_toReal` once we show the `tsum` is finite.
    have htsum_ne_top :
        (∑' n : ℕ, w n * (markovSymmetric (k := k) hk n) x) ≠ (⊤ : ENNReal) := by
      -- `w n * μₙ x ≤ w n` since `μₙ x ≤ 1`.
      have hle :
          (∑' n : ℕ, w n * (markovSymmetric (k := k) hk n) x) ≤ (∑' n : ℕ, w n) := by
        refine ENNReal.tsum_le_tsum ?_
        intro n
        have hx : (markovSymmetric (k := k) hk n) x ≤ 1 :=
          (FiniteAlphabet.Semimeasure.le_one (μ := (markovSymmetric (k := k) hk n).toSemimeasure) x)
        -- Multiply the bound by `w n`.
        simpa using mul_le_mul_of_nonneg_left hx (by simp)
      have hfinite : (∑' n : ℕ, w n) < (⊤ : ENNReal) := by
        -- The weight sum is `1`.
        simp [MarkovDirichletHyperprior.tsum_w]
      exact ne_of_lt (lt_of_le_of_lt hle hfinite)
    exact ENNReal.summable_toReal htsum_ne_top
  have hLSC :
      LowerSemicomputable (fun p : ℕ × Word k =>
        (w p.1 * (markovSymmetric (k := k) hk p.1) p.2).toReal) := by
    simpa using lsc_term (k := k) hk
  -- Package the standard closure lemma for countable mixtures.
  simpa [MarkovDirichletHyperprior.mixture] using
    (FiniteAlphabet.Computability.lsc_xiPrefixMeasure_nat (α := Fin k)
      (ν := fun n : ℕ => markovSymmetric (k := k) hk n)
      (w := w) (hw := MarkovDirichletHyperprior.tsum_w)
      (hf_ne_top := hf_ne_top) (hsum := hsum) (hLSC := hLSC))

end Computability

/-! ## Solomonoff competitiveness -/

/-- If the hyperprior mixture is lower semicomputable, then the Solomonoff-style universal mixture
`M₂` (finite alphabet) competes with it automatically.

This is the “third layer” in the semantics → Hook‑B mixture → Solomonoff story.
-/
theorem relEntropy_le_mixture_add_log_inv_M₂
    (μ : PrefixMeasure (Fin k))
    (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      relEntropy μ (M₂ (α := Fin k)) n ≤
        relEntropy μ (mixture hk).toSemimeasure n + Real.log (1 / c.toReal) := by
  have hη : FiniteAlphabet.LowerSemicomputablePrefixMeasure (α := Fin k) (mixture hk) :=
    Computability.mixture_lsc (k := k) hk
  simpa using
    (FiniteAlphabet.SolomonoffBridge.relEntropy_le_competitor_add_log_inv_M₂
      (α := Fin k) (μ := μ) (η := mixture hk) (hη := hη) (hη0 := mixture_ne_zero (hk := hk)) n)

end MarkovDirichletHyperprior

end Mettapedia.Logic.UniversalPrediction
