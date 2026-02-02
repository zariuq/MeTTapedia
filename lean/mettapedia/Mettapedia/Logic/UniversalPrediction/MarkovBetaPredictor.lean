import Mathlib.Tactic
import Mettapedia.Logic.UniversalPrediction.PrefixMeasure

/-!
# Markov-Beta Predictors as Prefix Measures (Binary Order-1 Case)

This file is the “next restriction” after i.i.d. exchangeability:

* a first-order Markov model on `Bool`, with **independent Beta priors per row**.

Concretely, we treat the transition probabilities

* `P(next=true | prev=false)` and
* `P(next=true | prev=true)`

as separate Bernoulli parameters, each with its own Beta prior.

This yields a computable, finite-dimensional predictor whose sufficient statistics are
the **transition counts**:

* `N(false,false)`, `N(false,true)`, `N(true,false)`, `N(true,true)`.

Later, this can be generalized to:

* finite alphabets (Dirichlet priors per row),
* higher-order Markov models (block transition counts),
* Markov-exchangeability / mixtures of Markov chains (Diaconis–Freedman).
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical

/-! ## Transition-count state -/

@[ext]
structure TransCounts where
  ff : ℕ  -- false → false
  ft : ℕ  -- false → true
  tf : ℕ  -- true  → false
  tt : ℕ  -- true  → true
deriving DecidableEq

namespace TransCounts

def zero : TransCounts := ⟨0, 0, 0, 0⟩

/-- Increment the appropriate transition counter. -/
def bump (c : TransCounts) (prev next : Bool) : TransCounts :=
  match prev, next with
  | false, false => ⟨c.ff + 1, c.ft,     c.tf,     c.tt⟩
  | false, true  => ⟨c.ff,     c.ft + 1, c.tf,     c.tt⟩
  | true,  false => ⟨c.ff,     c.ft,     c.tf + 1, c.tt⟩
  | true,  true  => ⟨c.ff,     c.ft,     c.tf,     c.tt + 1⟩

/-- Scan a tail `xs` starting from a previous symbol `prev`, accumulating transition counts.

Returns the updated counts together with the last symbol seen (or `prev` if `xs = []`). -/
def summaryAux (prev : Bool) (c : TransCounts) : BinString → TransCounts × Bool
  | [] => (c, prev)
  | b :: xs => summaryAux b (bump c prev b) xs

/-- Transition-count evidence for a binary string: counts plus the final symbol (if any). -/
def summary : BinString → Option (TransCounts × Bool)
  | [] => none
  | b :: xs => some (summaryAux b zero xs)

theorem summaryAux_append_singleton (prev : Bool) (c : TransCounts) (xs : BinString) (b : Bool) :
    summaryAux prev c (xs ++ [b]) =
      let r := summaryAux prev c xs
      (bump r.1 r.2 b, b) := by
  induction xs generalizing prev c with
  | nil =>
      simp [summaryAux]
  | cons x xs ih =>
      simp [summaryAux, ih, List.cons_append]

theorem summary_append_singleton (xs : BinString) (b : Bool) :
    summary (xs ++ [b]) =
      match summary xs with
      | none => some (zero, b)
      | some r => some (bump r.1 r.2 b, b) := by
  cases xs with
  | nil =>
      simp [summary, summaryAux]
  | cons x xs =>
      -- Reduce to the `summaryAux` lemma.
      simp [summary, summaryAux_append_singleton]

end TransCounts

/-! ## One-step predictive probabilities -/

private def stepDenom (α0 β0 α1 β1 : ℝ) (c : TransCounts) (prev : Bool) : ℝ :=
  if prev then (c.tf + c.tt : ℝ) + α1 + β1 else (c.ff + c.ft : ℝ) + α0 + β0

private def stepProb (α0 β0 α1 β1 : ℝ) (c : TransCounts) (prev next : Bool) : ℝ :=
  let denom := stepDenom α0 β0 α1 β1 c prev
  if prev then
    if next then ((c.tt : ℝ) + α1) / denom else ((c.tf : ℝ) + β1) / denom
  else
    if next then ((c.ft : ℝ) + α0) / denom else ((c.ff : ℝ) + β0) / denom

private lemma stepDenom_pos (α0 β0 α1 β1 : ℝ)
    (hα0 : 0 < α0) (hβ0 : 0 < β0) (hα1 : 0 < α1) (hβ1 : 0 < β1)
    (c : TransCounts) (prev : Bool) :
    0 < stepDenom α0 β0 α1 β1 c prev := by
  unfold stepDenom
  cases prev <;> simp
  all_goals
    have h0 : 0 ≤ ((c.ff + c.ft : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have h1 : 0 ≤ ((c.tf + c.tt : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le _)
    linarith

private lemma stepProb_nonneg (α0 β0 α1 β1 : ℝ)
    (hα0 : 0 < α0) (hβ0 : 0 < β0) (hα1 : 0 < α1) (hβ1 : 0 < β1)
    (c : TransCounts) (prev next : Bool) :
    0 ≤ stepProb α0 β0 α1 β1 c prev next := by
  unfold stepProb
  set denom := stepDenom α0 β0 α1 β1 c prev
  have hdenom : 0 < denom := by
    simpa [denom] using stepDenom_pos (α0 := α0) (β0 := β0) (α1 := α1) (β1 := β1)
      hα0 hβ0 hα1 hβ1 c prev
  cases prev <;> cases next <;> simp [denom]
  all_goals
    have h0 : 0 ≤ (0 : ℝ) := le_rfl
    have hnn : 0 ≤ ((0 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le 0)
    -- all numerators are (Nat + positive), hence nonnegative
    refine div_nonneg ?_ (le_of_lt hdenom)
    have hn : 0 ≤ ((0 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le 0)
    linarith

private lemma stepProb_sum (α0 β0 α1 β1 : ℝ)
    (hα0 : 0 < α0) (hβ0 : 0 < β0) (hα1 : 0 < α1) (hβ1 : 0 < β1)
    (c : TransCounts) (prev : Bool) :
    stepProb α0 β0 α1 β1 c prev false + stepProb α0 β0 α1 β1 c prev true = 1 := by
  unfold stepProb
  set denom := stepDenom α0 β0 α1 β1 c prev
  have hdenom : denom ≠ 0 := ne_of_gt <|
    (stepDenom_pos (α0 := α0) (β0 := β0) (α1 := α1) (β1 := β1) hα0 hβ0 hα1 hβ1 c prev)
  cases prev <;> simp [denom]
  all_goals
    field_simp [denom, hdenom]
    simp [stepDenom]
    ring_nf

/-! ## Sequential prefix probability -/

private def markovPrefixAux
    (α0 β0 α1 β1 : ℝ)
    (hα0 : 0 < α0) (hβ0 : 0 < β0) (hα1 : 0 < α1) (hβ1 : 0 < β1)
    (prev : Bool) (c : TransCounts) : BinString → ENNReal
  | [] => 1
  | b :: xs =>
      let p : ℝ := stepProb α0 β0 α1 β1 c prev b
      ENNReal.ofReal p *
        markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b (TransCounts.bump c prev b) xs

private theorem markovPrefixAux_additive
    (α0 β0 α1 β1 : ℝ)
    (hα0 : 0 < α0) (hβ0 : 0 < β0) (hα1 : 0 < α1) (hβ1 : 0 < β1)
    (prev : Bool) (c : TransCounts) (xs : BinString) :
    markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 prev c (xs ++ [false]) +
        markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 prev c (xs ++ [true]) =
      markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 prev c xs := by
  induction xs generalizing prev c with
  | nil =>
      -- Base: sum of one-step probabilities is 1.
      simp [markovPrefixAux]
      have h0 : 0 ≤ stepProb α0 β0 α1 β1 c prev false :=
        stepProb_nonneg (α0 := α0) (β0 := β0) (α1 := α1) (β1 := β1) hα0 hβ0 hα1 hβ1 c prev false
      have h1 : 0 ≤ stepProb α0 β0 α1 β1 c prev true :=
        stepProb_nonneg (α0 := α0) (β0 := β0) (α1 := α1) (β1 := β1) hα0 hβ0 hα1 hβ1 c prev true
      have :
          ENNReal.ofReal (stepProb α0 β0 α1 β1 c prev false) +
              ENNReal.ofReal (stepProb α0 β0 α1 β1 c prev true) =
            ENNReal.ofReal (1 : ℝ) := by
        -- Use `ofReal_add` plus the algebraic identity from `stepProb_sum`.
        calc
          ENNReal.ofReal (stepProb α0 β0 α1 β1 c prev false) +
              ENNReal.ofReal (stepProb α0 β0 α1 β1 c prev true)
              = ENNReal.ofReal (stepProb α0 β0 α1 β1 c prev false +
                  stepProb α0 β0 α1 β1 c prev true) := by
                    symm
                    exact ENNReal.ofReal_add h0 h1
          _ = ENNReal.ofReal (1 : ℝ) := by
                    congr 1
                    simpa [add_comm] using stepProb_sum (α0 := α0) (β0 := β0) (α1 := α1) (β1 := β1)
                      hα0 hβ0 hα1 hβ1 c prev
      simpa using this
  | cons b xs ih =>
      -- Factor out the first-step probability and use IH on the tail.
      have ih' :
          markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b (c.bump prev b) (xs ++ [false]) +
              markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b (c.bump prev b) (xs ++ [true]) =
            markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b (c.bump prev b) xs := by
        simpa using (ih (prev := b) (c := c.bump prev b))
      simp [markovPrefixAux]
      -- Convert `p*A + p*B` to `p*(A+B)` and apply IH.
      calc
        ENNReal.ofReal (stepProb α0 β0 α1 β1 c prev b) *
              markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b (c.bump prev b) (xs ++ [false]) +
            ENNReal.ofReal (stepProb α0 β0 α1 β1 c prev b) *
              markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b (c.bump prev b) (xs ++ [true]) =
          ENNReal.ofReal (stepProb α0 β0 α1 β1 c prev b) *
            (markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b (c.bump prev b) (xs ++ [false]) +
              markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b (c.bump prev b) (xs ++ [true])) := by
          simp [mul_add]
        _ =
          ENNReal.ofReal (stepProb α0 β0 α1 β1 c prev b) *
            markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b (c.bump prev b) xs := by
          simpa using congrArg
            (fun t => ENNReal.ofReal (stepProb α0 β0 α1 β1 c prev b) * t) ih'

/-! ## The Markov-Beta predictor as a PrefixMeasure -/

private def initProb (_b : Bool) : ℝ := (1 / 2 : ℝ)

private lemma initProb_sum : initProb false + initProb true = 1 := by
  simp [initProb]; norm_num

private def markovPrefix
    (α0 β0 α1 β1 : ℝ)
    (hα0 : 0 < α0) (hβ0 : 0 < β0) (hα1 : 0 < α1) (hβ1 : 0 < β1) : BinString → ENNReal
  | [] => 1
  | b :: xs =>
      ENNReal.ofReal (initProb b) *
        markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b TransCounts.zero xs

/-- Binary Markov(1) predictor with independent Beta priors per row, as a `PrefixMeasure`. -/
noncomputable def markovBetaPrefixMeasure
    (α0 β0 α1 β1 : ℝ)
    (hα0 : 0 < α0) (hβ0 : 0 < β0) (hα1 : 0 < α1) (hβ1 : 0 < β1) : PrefixMeasure where
  toFun := markovPrefix α0 β0 α1 β1 hα0 hβ0 hα1 hβ1
  root_eq_one' := by simp [markovPrefix]
  additive' := by
    intro x
    cases x with
    | nil =>
        -- ε splits by the initial distribution.
        simp [markovPrefix, markovPrefixAux, initProb]
        have h2 : (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = 1 := by
          rw [← two_mul, ENNReal.mul_inv_cancel] <;> norm_num
        simpa using h2
    | cons b xs =>
        -- Reduce to the auxiliary additivity lemma (starting from fresh counts).
        have haux :
            markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b TransCounts.zero (xs ++ [false]) +
                markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b TransCounts.zero (xs ++ [true]) =
              markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b TransCounts.zero xs := by
          simpa using
            (markovPrefixAux_additive (α0 := α0) (β0 := β0) (α1 := α1) (β1 := β1)
              (hα0 := hα0) (hβ0 := hβ0) (hα1 := hα1) (hβ1 := hβ1)
              (prev := b) (c := TransCounts.zero) (xs := xs))
        simp [markovPrefix]
        calc
          ENNReal.ofReal (initProb b) *
                markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b TransCounts.zero (xs ++ [false]) +
              ENNReal.ofReal (initProb b) *
                markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b TransCounts.zero (xs ++ [true]) =
            ENNReal.ofReal (initProb b) *
              (markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b TransCounts.zero (xs ++ [false]) +
                markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b TransCounts.zero (xs ++ [true])) := by
              simp [mul_add]
          _ =
            ENNReal.ofReal (initProb b) *
              markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 b TransCounts.zero xs := by
              simpa using congrArg (fun t => ENNReal.ofReal (initProb b) * t) haux

/-- Markov-Laplace: Beta(1,1) priors for both transition rows. -/
noncomputable abbrev markovLaplacePrefixMeasure : PrefixMeasure :=
  markovBetaPrefixMeasure (α0 := 1) (β0 := 1) (α1 := 1) (β1 := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Markov-Jeffreys/KT: Beta(1/2,1/2) priors for both transition rows. -/
noncomputable abbrev markovJeffreysPrefixMeasure : PrefixMeasure :=
  markovBetaPrefixMeasure (α0 := (1/2 : ℝ)) (β0 := (1/2 : ℝ)) (α1 := (1/2 : ℝ)) (β1 := (1/2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Positivity (no zero-mass prefixes) -/

private lemma initProb_pos (b : Bool) : 0 < initProb b := by
  simp [initProb]

private lemma stepProb_pos (α0 β0 α1 β1 : ℝ)
    (hα0 : 0 < α0) (hβ0 : 0 < β0) (hα1 : 0 < α1) (hβ1 : 0 < β1)
    (c : TransCounts) (prev next : Bool) :
    0 < stepProb α0 β0 α1 β1 c prev next := by
  unfold stepProb
  set denom := stepDenom α0 β0 α1 β1 c prev
  have hdenom : 0 < denom := by
    simpa [denom] using stepDenom_pos (α0 := α0) (β0 := β0) (α1 := α1) (β1 := β1)
      hα0 hβ0 hα1 hβ1 c prev
  cases prev <;> cases next <;> simp [denom]
  all_goals
    refine div_pos ?_ hdenom
    -- Each numerator is a nat-cast plus a strictly positive hyperparameter.
    have hn : 0 ≤ ((0 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le 0)
    linarith

private lemma markovPrefixAux_ne_zero (α0 β0 α1 β1 : ℝ)
    (hα0 : 0 < α0) (hβ0 : 0 < β0) (hα1 : 0 < α1) (hβ1 : 0 < β1)
    (prev : Bool) (c : TransCounts) :
    ∀ xs : BinString, markovPrefixAux α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 prev c xs ≠ 0 := by
  intro xs
  induction xs generalizing prev c with
  | nil =>
      simp [markovPrefixAux]
  | cons b xs ih =>
      -- `simp` turns `x * y ≠ 0` into the conjunction of the two nonzero conditions.
      simp [markovPrefixAux]
      constructor
      · -- `stepProb` is strictly positive when all hyperparameters are.
        exact stepProb_pos (α0 := α0) (β0 := β0) (α1 := α1) (β1 := β1) hα0 hβ0 hα1 hβ1 c prev b
      · -- The tail recursion is nonzero by IH.
        simpa using ih (prev := b) (c := c.bump prev b)

private lemma markovPrefix_ne_zero (α0 β0 α1 β1 : ℝ)
    (hα0 : 0 < α0) (hβ0 : 0 < β0) (hα1 : 0 < α1) (hβ1 : 0 < β1) :
    ∀ xs : BinString, markovPrefix α0 β0 α1 β1 hα0 hβ0 hα1 hβ1 xs ≠ 0 := by
  intro xs
  cases xs with
  | nil =>
      simp [markovPrefix]
  | cons b xs =>
      -- `simp` turns `x * y ≠ 0` into the conjunction of the two nonzero conditions.
      simp [markovPrefix]
      constructor
      · exact initProb_pos b
      · exact markovPrefixAux_ne_zero (α0 := α0) (β0 := β0) (α1 := α1) (β1 := β1)
          hα0 hβ0 hα1 hβ1 b TransCounts.zero xs

/-- Any Markov-Beta prefix-measure with strictly positive hyperparameters assigns nonzero
probability to every finite prefix. -/
theorem markovBetaPrefixMeasure_ne_zero
    (α0 β0 α1 β1 : ℝ)
    (hα0 : 0 < α0) (hβ0 : 0 < β0) (hα1 : 0 < α1) (hβ1 : 0 < β1) :
    ∀ xs : BinString, (markovBetaPrefixMeasure (α0 := α0) (β0 := β0) (α1 := α1) (β1 := β1)
      hα0 hβ0 hα1 hβ1) xs ≠ 0 := by
  -- This is just `markovPrefix_ne_zero` for the underlying `toFun`.
  intro xs
  exact markovPrefix_ne_zero (α0 := α0) (β0 := β0) (α1 := α1) (β1 := β1) hα0 hβ0 hα1 hβ1 xs

end Mettapedia.Logic.UniversalPrediction
