import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic
import Mettapedia.Logic.EvidenceDirichlet

/-!
# Markov-Dirichlet Predictors (Finite Alphabet, Order-1)

This file generalizes `Mettapedia.Logic.UniversalPrediction.MarkovBetaPredictor` from `Bool` to a
finite alphabet `Fin k` by using **Dirichlet priors per transition row**.

We keep this file self-contained: it defines its own “k-ary prefix measure” interface
(`PrefixMeasureFin`) rather than refactoring the existing binary `PrefixMeasure` API.

Intended use:
* as the next “tractable restriction” after i.i.d. exchangeability,
* and as the template for “Markov‑PLN”: sufficient statistics = transition-count matrix.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical BigOperators

open Mettapedia.Logic.EvidenceDirichlet

/-! ## Prefix measures over a finite alphabet -/

/-- A probability measure on cylinder events for strings over `Fin k`. -/
structure PrefixMeasureFin (k : ℕ) where
  /-- Prefix probability `μ(x)` for a finite string `x`. -/
  toFun : List (Fin k) → ENNReal
  /-- Normalization: `μ(ε) = 1`. -/
  root_eq_one' : toFun [] = 1
  /-- Cylinder partition: `μ(x) = ∑ₐ μ(xa)`. -/
  additive' : ∀ x : List (Fin k), (∑ a : Fin k, toFun (x ++ [a])) = toFun x

instance (k : ℕ) : CoeFun (PrefixMeasureFin k) (fun _ => List (Fin k) → ENNReal) where
  coe := PrefixMeasureFin.toFun

/-! ## Transition-count evidence -/

@[ext]
structure TransCounts (k : ℕ) where
  counts : Fin k → Fin k → ℕ
deriving DecidableEq

namespace TransCounts

variable {k : ℕ}

def zero : TransCounts k := ⟨fun _ _ => 0⟩

/-- Increment exactly the transition counter `(prev,next)`. -/
def bump (c : TransCounts k) (prev next : Fin k) : TransCounts k :=
  ⟨fun i j => if i = prev ∧ j = next then c.counts i j + 1 else c.counts i j⟩

@[simp]
theorem bump_apply_self (c : TransCounts k) (prev next : Fin k) :
    (bump c prev next).counts prev next = c.counts prev next + 1 := by
  simp [bump]

@[simp]
theorem bump_apply_of_ne (c : TransCounts k) {i j prev next : Fin k}
    (h : ¬(i = prev ∧ j = next)) :
    (bump c prev next).counts i j = c.counts i j := by
  simp [bump, h]

/-- Row total count `∑ₐ N(prev,a)`. -/
def rowTotal (c : TransCounts k) (prev : Fin k) : ℕ :=
  ∑ a : Fin k, c.counts prev a

end TransCounts

/-! ## One-step predictive probabilities -/

namespace MarkovDirichlet

variable {k : ℕ}

private def stepDenom (prior : Fin k → DirichletParams k) (c : TransCounts k) (prev : Fin k) : ℝ :=
  (c.rowTotal prev : ℝ) + (prior prev).totalConcentration

private def stepProb (prior : Fin k → DirichletParams k) (c : TransCounts k) (prev next : Fin k) : ℝ :=
  (((c.counts prev next : ℕ) : ℝ) + (prior prev).priorParams next) / stepDenom prior c prev

private lemma stepDenom_pos (hk : 0 < k) (prior : Fin k → DirichletParams k) (c : TransCounts k)
    (prev : Fin k) :
    0 < stepDenom prior c prev := by
  unfold stepDenom
  have hrow : 0 ≤ (c.rowTotal prev : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have hα : 0 < (prior prev).totalConcentration :=
    DirichletParams.totalConcentration_pos (p := prior prev) hk
  linarith

private lemma stepProb_nonneg (hk : 0 < k) (prior : Fin k → DirichletParams k) (c : TransCounts k)
    (prev next : Fin k) :
    0 ≤ stepProb prior c prev next := by
  unfold stepProb
  have hden : 0 < stepDenom prior c prev := stepDenom_pos hk prior c prev
  refine div_nonneg ?_ (le_of_lt hden)
  have hcnt : 0 ≤ ((c.counts prev next : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have hα : 0 < (prior prev).priorParams next := (prior prev).params_pos next
  linarith

private lemma stepProb_sum (hk : 0 < k) (prior : Fin k → DirichletParams k) (c : TransCounts k)
    (prev : Fin k) :
    (∑ j : Fin k, stepProb prior c prev j) = 1 := by
  classical
  -- Factor the common denominator out of the finite sum.
  have hden_pos : 0 < stepDenom prior c prev := stepDenom_pos hk prior c prev
  have hden0 : stepDenom prior c prev ≠ 0 := ne_of_gt hden_pos
  have hrow :
      (c.rowTotal prev : ℝ) = ∑ j : Fin k, ((c.counts prev j : ℕ) : ℝ) := by
    -- `rowTotal` is a Nat-sum; cast it to ℝ and rewrite as a sum of casts.
    unfold TransCounts.rowTotal
    simp
  have hnum :
      (∑ j : Fin k, (((c.counts prev j : ℕ) : ℝ) + (prior prev).priorParams j)) =
        stepDenom prior c prev := by
    -- Split the sum and rewrite the casted row total.
    unfold stepDenom DirichletParams.totalConcentration
    calc
      (∑ j : Fin k, (((c.counts prev j : ℕ) : ℝ) + (prior prev).priorParams j))
          =
          (∑ j : Fin k, ((c.counts prev j : ℕ) : ℝ)) +
            (∑ j : Fin k, (prior prev).priorParams j) := by
              simpa using
                (Finset.sum_add_distrib :
                  (∑ j : Fin k,
                      (((c.counts prev j : ℕ) : ℝ) + (prior prev).priorParams j)) =
                    (∑ j : Fin k, ((c.counts prev j : ℕ) : ℝ)) +
                      (∑ j : Fin k, (prior prev).priorParams j))
      _ = (c.rowTotal prev : ℝ) + ∑ j : Fin k, (prior prev).priorParams j := by
            simp [hrow]
      _ = stepDenom prior c prev := by
            rfl
  -- Now the sum is `denom⁻¹ * denom`.
  unfold stepProb
  calc
    (∑ j : Fin k, (((c.counts prev j : ℕ) : ℝ) + (prior prev).priorParams j) /
        stepDenom prior c prev)
        =
        (∑ j : Fin k,
            (((c.counts prev j : ℕ) : ℝ) + (prior prev).priorParams j) *
              (stepDenom prior c prev)⁻¹) := by
          simp [div_eq_mul_inv]
    _ =
        (∑ j : Fin k, (((c.counts prev j : ℕ) : ℝ) + (prior prev).priorParams j)) *
          (stepDenom prior c prev)⁻¹ := by
          -- Factor out `(stepDenom ...)⁻¹` on the right.
          simpa using
            (Finset.sum_mul (s := (Finset.univ : Finset (Fin k)))
                (f := fun j : Fin k =>
                  ((c.counts prev j : ℕ) : ℝ) + (prior prev).priorParams j)
                ((stepDenom prior c prev)⁻¹)).symm
    _ = stepDenom prior c prev * (stepDenom prior c prev)⁻¹ := by
          simp [hnum]
    _ = 1 := by
          simp [hden0]

/-! ## Sequential prefix probability -/

private def prefixAux (prior : Fin k → DirichletParams k) (prev : Fin k) (c : TransCounts k) :
    List (Fin k) → ENNReal
  | [] => 1
  | b :: xs =>
      let p : ℝ := stepProb prior c prev b
      ENNReal.ofReal p *
        prefixAux prior b (TransCounts.bump c prev b) xs

private theorem prefixAux_additive (hk : 0 < k) (prior : Fin k → DirichletParams k) (prev : Fin k)
    (c : TransCounts k) (xs : List (Fin k)) :
    (∑ a : Fin k, prefixAux prior prev c (xs ++ [a])) = prefixAux prior prev c xs := by
  classical
  induction xs generalizing prev c with
  | nil =>
      -- Base: sum of one-step probabilities is 1.
      simp [prefixAux]
      have hnonneg : ∀ a : Fin k, 0 ≤ stepProb prior c prev a := fun a =>
        stepProb_nonneg hk prior c prev a
      -- Move the `ENNReal.ofReal` across the finite sum.
      have :
          (∑ a : Fin k, ENNReal.ofReal (stepProb prior c prev a)) =
            ENNReal.ofReal (∑ a : Fin k, stepProb prior c prev a) := by
        simpa using
          (ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset (Fin k)))
              (f := fun a : Fin k => stepProb prior c prev a)
              (by intro a ha; simpa using hnonneg a)).symm
      -- Finish by the algebraic identity in `ℝ`.
      calc
        (∑ a : Fin k, ENNReal.ofReal (stepProb prior c prev a))
            = ENNReal.ofReal (∑ a : Fin k, stepProb prior c prev a) := this
        _ = ENNReal.ofReal (1 : ℝ) := by
              congr 1
              simpa using stepProb_sum hk (prior := prior) (c := c) (prev := prev)
        _ = (1 : ENNReal) := by simp
  | cons b xs ih =>
      -- Factor out the first-step probability and use IH on the tail.
      have ih' :
          (∑ a : Fin k, prefixAux prior b (TransCounts.bump c prev b) (xs ++ [a])) =
            prefixAux prior b (TransCounts.bump c prev b) xs := by
        simpa using (ih (prev := b) (c := TransCounts.bump c prev b))
      simp [prefixAux]
      -- `∑ a, p * f a = p * ∑ a, f a`.
      have hfactor :
          (∑ a : Fin k,
                ENNReal.ofReal (stepProb prior c prev b) *
                  prefixAux prior b (TransCounts.bump c prev b) (xs ++ [a])) =
            ENNReal.ofReal (stepProb prior c prev b) *
              ∑ a : Fin k, prefixAux prior b (TransCounts.bump c prev b) (xs ++ [a]) := by
        simpa using (Finset.mul_sum (a := ENNReal.ofReal (stepProb prior c prev b))
          (f := fun a : Fin k => prefixAux prior b (TransCounts.bump c prev b) (xs ++ [a]))
          (s := (Finset.univ : Finset (Fin k)))).symm
      -- Combine.
      calc
        (∑ a : Fin k, prefixAux prior prev c ((b :: xs) ++ [a]))
            = ENNReal.ofReal (stepProb prior c prev b) *
                ∑ a : Fin k, prefixAux prior b (TransCounts.bump c prev b) (xs ++ [a]) := by
              simpa [List.cons_append, hfactor]
        _ = ENNReal.ofReal (stepProb prior c prev b) *
              prefixAux prior b (TransCounts.bump c prev b) xs := by
              exact congrArg (fun t => ENNReal.ofReal (stepProb prior c prev b) * t) ih'

/-! ## The Markov-Dirichlet predictor as a `PrefixMeasureFin` -/

private def initProb (_b : Fin k) : ℝ := (1 / (k : ℝ))

private lemma initProb_nonneg (hk : 0 < k) (b : Fin k) : 0 ≤ initProb (k := k) b := by
  unfold initProb
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have : 0 ≤ (k : ℝ) := le_of_lt hk'
  exact one_div_nonneg.2 this

private lemma initProb_sum (hk : 0 < k) : (∑ b : Fin k, initProb (k := k) b) = 1 := by
  classical
  unfold initProb
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  -- Sum of a constant over `Fin k`.
  simp [Finset.sum_const, hk0, Finset.card_univ]

private def prefixProb (prior : Fin k → DirichletParams k) : List (Fin k) → ENNReal
  | [] => 1
  | b :: xs =>
      ENNReal.ofReal (initProb (k := k) b) *
        prefixAux prior b (TransCounts.zero) xs

/-- Markov(1) predictor with independent Dirichlet priors per row, as a `PrefixMeasureFin`. -/
noncomputable def markovDirichletPrefixMeasure (hk : 0 < k) (prior : Fin k → DirichletParams k) :
    PrefixMeasureFin k where
  toFun := prefixProb prior
  root_eq_one' := by simp [prefixProb]
  additive' := by
    classical
    intro x
    cases x with
    | nil =>
        -- ε splits by the initial distribution.
        simp [prefixProb, prefixAux]
        have hnonneg : ∀ b : Fin k, 0 ≤ initProb (k := k) b := initProb_nonneg (k := k) hk
        have hsum :
            (∑ b : Fin k, ENNReal.ofReal (initProb (k := k) b)) =
              ENNReal.ofReal (∑ b : Fin k, initProb (k := k) b) := by
          simpa using
            (ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset (Fin k)))
                (f := fun b : Fin k => initProb (k := k) b)
                (by intro b hb; simpa using hnonneg b)).symm
        -- Now use `initProb_sum`.
        calc
          (∑ b : Fin k, ENNReal.ofReal (initProb (k := k) b)) =
              ENNReal.ofReal (∑ b : Fin k, initProb (k := k) b) := hsum
          _ = ENNReal.ofReal (1 : ℝ) := by
                congr 1
                simpa using initProb_sum (k := k) hk
          _ = (1 : ENNReal) := by simp
    | cons b xs =>
        -- Reduce to the auxiliary additivity lemma (starting from fresh counts).
        have haux :
            (∑ a : Fin k, prefixAux prior b TransCounts.zero (xs ++ [a])) =
              prefixAux prior b TransCounts.zero xs := by
          simpa using
            (prefixAux_additive (hk := hk) (prior := prior) (prev := b) (c := TransCounts.zero) (xs := xs))
        simp [prefixProb]
        -- Factor out the initial probability and apply `haux`.
        calc
          (∑ a : Fin k,
                ENNReal.ofReal (initProb (k := k) b) *
                  prefixAux prior b TransCounts.zero (xs ++ [a])) =
              ENNReal.ofReal (initProb (k := k) b) *
                ∑ a : Fin k, prefixAux prior b TransCounts.zero (xs ++ [a]) := by
                simpa using
                  (Finset.mul_sum (a := ENNReal.ofReal (initProb (k := k) b))
                    (f := fun a : Fin k => prefixAux prior b TransCounts.zero (xs ++ [a]))
                    (s := (Finset.univ : Finset (Fin k)))).symm
          _ = ENNReal.ofReal (initProb (k := k) b) * prefixAux prior b TransCounts.zero xs := by
                simp [haux]

/-- Markov-Laplace: Dirichlet(1,…,1) priors for every transition row. -/
noncomputable abbrev markovLaplace (k : ℕ) (hk : 0 < k) : PrefixMeasureFin k :=
  markovDirichletPrefixMeasure (k := k) hk (fun _ => DirichletParams.uniformPrior)

/-- Markov-Jeffreys/KT: Dirichlet(1/2,…,1/2) priors for every transition row. -/
noncomputable abbrev markovJeffreys (k : ℕ) (hk : 0 < k) : PrefixMeasureFin k :=
  markovDirichletPrefixMeasure (k := k) hk (fun _ =>
    DirichletParams.uniform (1/2 : ℝ) (by norm_num))

end MarkovDirichlet

end Mettapedia.Logic.UniversalPrediction
