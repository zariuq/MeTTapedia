import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic
import Mettapedia.Logic.EvidenceDirichlet
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure

/-!
# Markov-Dirichlet Predictors (Finite Alphabet, Order-1)

This file generalizes `Mettapedia.Logic.UniversalPrediction.MarkovBetaPredictor` from `Bool` to a
finite alphabet `Fin k` by using **Dirichlet priors per transition row**.

This now uses the shared finite-alphabet prefix-measure API in
`Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure`, so downstream results (finite
horizon KL bounds, hyperprior mixtures, etc.) can reuse the same infrastructure without duplicating
the “prefix additivity” boilerplate.

Intended use:
* as the next “tractable restriction” after i.i.d. exchangeability,
* and as the template for “Markov‑PLN”: sufficient statistics = transition-count matrix.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical BigOperators

open Mettapedia.Logic.EvidenceDirichlet

/-! ## Transition-count evidence -/

@[ext]
structure TransCounts (k : ℕ) where
  counts : Fin k → Fin k → ℕ
deriving DecidableEq

namespace TransCounts

variable {k : ℕ}

instance : Countable (TransCounts k) := by
  classical
  -- `TransCounts k` is determined by its matrix of natural counts.
  have hf : Function.Injective (fun c : TransCounts k => c.counts) := by
    intro c₁ c₂ h
    ext i j
    -- Unfold `counts` via the equality of functions.
    simpa using congrArg (fun f => f i j) h
  exact hf.countable

def zero : TransCounts k := ⟨fun _ _ => 0⟩

instance : Zero (TransCounts k) := ⟨zero⟩

/-- Pointwise addition of transition-count matrices. -/
def add (c₁ c₂ : TransCounts k) : TransCounts k :=
  ⟨fun i j => c₁.counts i j + c₂.counts i j⟩

instance : Add (TransCounts k) := ⟨add⟩

@[simp] theorem zero_counts (i j : Fin k) : (0 : TransCounts k).counts i j = 0 := rfl

@[simp] theorem add_counts (c₁ c₂ : TransCounts k) (i j : Fin k) :
    (c₁ + c₂).counts i j = c₁.counts i j + c₂.counts i j :=
  rfl

instance : AddCommMonoid (TransCounts k) where
  add := (· + ·)
  add_assoc c₁ c₂ c₃ := by
    ext i j
    simp [Nat.add_assoc]
  zero := 0
  zero_add c := by
    ext i j
    simp
  add_zero c := by
    ext i j
    simp
  add_comm c₁ c₂ := by
    ext i j
    simp [Nat.add_comm]
  nsmul n c := ⟨fun i j => n * c.counts i j⟩
  nsmul_zero c := by
    ext i j
    simp
  nsmul_succ n c := by
    ext i j
    -- `nsmul` on `ℕ` is multiplication, so this is `Nat.succ_mul` plus commutativity of addition.
    simp [Nat.succ_mul, Nat.add_comm]

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

/-- The single-transition matrix with a `1` at `(prev,next)` and `0` elsewhere. -/
def oneHot (prev next : Fin k) : TransCounts k :=
  ⟨fun i j => if i = prev ∧ j = next then 1 else 0⟩

@[simp] theorem oneHot_counts_self (prev next : Fin k) :
    (oneHot (k := k) prev next).counts prev next = 1 := by
  simp [oneHot]

@[simp] theorem oneHot_counts_of_ne {i j prev next : Fin k} (h : ¬(i = prev ∧ j = next)) :
    (oneHot (k := k) prev next).counts i j = 0 := by
  simp [oneHot, h]

/-- `bump` is exactly addition by a one-hot transition matrix. -/
theorem bump_eq_add_oneHot (c : TransCounts k) (prev next : Fin k) :
    bump c prev next = c + oneHot (k := k) prev next := by
  ext i j
  by_cases h : i = prev ∧ j = next
  · rcases h with ⟨rfl, rfl⟩
    simp [bump, oneHot]
  · simp [bump, oneHot, h]

/-- Row total count `∑ₐ N(prev,a)`. -/
def rowTotal (c : TransCounts k) (prev : Fin k) : ℕ :=
  ∑ a : Fin k, c.counts prev a

/-- Scan a tail `xs` starting from a previous symbol `prev`, accumulating transition counts.

Returns the updated counts together with the last symbol seen (or `prev` if `xs = []`). -/
def summaryAux (prev : Fin k) (c : TransCounts k) : List (Fin k) → TransCounts k × Fin k
  | [] => (c, prev)
  | b :: xs => summaryAux b (bump c prev b) xs

/-- Transition-count evidence for a finite string: counts plus the final symbol (if any). -/
def summary : List (Fin k) → Option (TransCounts k × Fin k)
  | [] => none
  | b :: xs => some (summaryAux b zero xs)

theorem summaryAux_append_singleton (prev : Fin k) (c : TransCounts k) (xs : List (Fin k))
    (b : Fin k) :
    summaryAux prev c (xs ++ [b]) =
      let r := summaryAux prev c xs
      (bump r.1 r.2 b, b) := by
  induction xs generalizing prev c with
  | nil =>
      simp [summaryAux]
  | cons x xs ih =>
      simp [summaryAux, ih, List.cons_append]

theorem summary_append_singleton (xs : List (Fin k)) (b : Fin k) :
    summary (xs ++ [b]) =
      match summary xs with
      | none => some (zero, b)
      | some r => some (bump r.1 r.2 b, b) := by
  cases xs with
  | nil =>
      simp [summary, summaryAux]
  | cons x xs =>
      simp [summary, summaryAux_append_singleton]

end TransCounts

/-! ## One-step predictive probabilities -/

namespace MarkovDirichlet

variable {k : ℕ}

/-- Denominator for the Dirichlet posterior-predictive probability at row `prev`. -/
def stepDenom (prior : Fin k → DirichletParams k) (c : TransCounts k) (prev : Fin k) : ℝ :=
  (c.rowTotal prev : ℝ) + (prior prev).totalConcentration

/-- Dirichlet posterior-predictive probability for the transition `prev → next`. -/
def stepProb (prior : Fin k → DirichletParams k) (c : TransCounts k) (prev next : Fin k) : ℝ :=
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

/-- Auxiliary recursion for `markovDirichletPrefixMeasure`: prefix probability for a tail `xs`
starting from previous symbol `prev` and transition counts `c`. -/
def prefixAux (prior : Fin k → DirichletParams k) (prev : Fin k) (c : TransCounts k) :
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

/-- `prefixAux` update for appending a single symbol, expressed via the transition-count state
computed by `TransCounts.summaryAux`.

This makes it explicit that the Markov-Dirichlet predictor’s recursion is a state machine whose
state is exactly `(counts, last)`. -/
theorem prefixAux_append_singleton (prior : Fin k → DirichletParams k) (prev : Fin k)
    (c : TransCounts k) (xs : List (Fin k)) (a : Fin k) :
    prefixAux (k := k) prior prev c (xs ++ [a]) =
      prefixAux (k := k) prior prev c xs *
        ENNReal.ofReal
          (stepProb (k := k) prior (TransCounts.summaryAux prev c xs).1 (TransCounts.summaryAux prev c xs).2 a) := by
  classical
  induction xs generalizing prev c with
  | nil =>
      simp [prefixAux, TransCounts.summaryAux]
  | cons b xs ih =>
      -- One step of the recursion; then apply IH to the tail.
      simp [prefixAux, TransCounts.summaryAux, ih, List.cons_append, mul_assoc]

/-! ## The Markov-Dirichlet predictor as a prefix measure -/

/-- Initial distribution for the first symbol, taken uniform on `Fin k`. -/
def initProb (_b : Fin k) : ℝ := (1 / (k : ℝ))

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

/-- Prefix probability (as `ENNReal`) for a whole word, obtained by composing the initial
distribution with the Markov(1) posterior-predictive recursion. -/
def prefixProb (prior : Fin k → DirichletParams k) : List (Fin k) → ENNReal
  | [] => 1
  | b :: xs =>
      ENNReal.ofReal (initProb (k := k) b) *
        prefixAux prior b (TransCounts.zero) xs

/-- Multiplicative update for the full prefix probability on nonempty words, expressed via the
transition-count state `TransCounts.summaryAux`. -/
theorem prefixProb_cons_append_singleton (prior : Fin k → DirichletParams k) (b : Fin k)
    (xs : List (Fin k)) (a : Fin k) :
    prefixProb (k := k) prior ((b :: xs) ++ [a]) =
      prefixProb (k := k) prior (b :: xs) *
        ENNReal.ofReal
          (stepProb (k := k) prior (TransCounts.summaryAux b TransCounts.zero xs).1
            (TransCounts.summaryAux b TransCounts.zero xs).2 a) := by
  -- Unfold `prefixProb` and delegate to the `prefixAux` lemma.
  simp [prefixProb, prefixAux_append_singleton, mul_assoc]

/-- Markov(1) predictor with independent Dirichlet priors per row, as a finite-alphabet `PrefixMeasure`. -/
noncomputable def markovDirichletPrefixMeasure (hk : 0 < k) (prior : Fin k → DirichletParams k) :
    FiniteAlphabet.PrefixMeasure (Fin k) where
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
noncomputable abbrev markovLaplace (k : ℕ) (hk : 0 < k) : FiniteAlphabet.PrefixMeasure (Fin k) :=
  markovDirichletPrefixMeasure (k := k) hk (fun _ => DirichletParams.uniformPrior)

/-- Markov-Jeffreys/KT: Dirichlet(1/2,…,1/2) priors for every transition row. -/
noncomputable abbrev markovJeffreys (k : ℕ) (hk : 0 < k) : FiniteAlphabet.PrefixMeasure (Fin k) :=
  markovDirichletPrefixMeasure (k := k) hk (fun _ =>
    DirichletParams.uniform (1/2 : ℝ) (by norm_num))

/-! ## Positivity / non-vanishing -/

private lemma initProb_pos (hk : 0 < k) (b : Fin k) : 0 < initProb (k := k) b := by
  unfold initProb
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  simpa using (one_div_pos.mpr hk')

private lemma stepProb_pos (hk : 0 < k) (prior : Fin k → DirichletParams k) (c : TransCounts k)
    (prev next : Fin k) :
    0 < stepProb prior c prev next := by
  unfold stepProb
  have hden : 0 < stepDenom prior c prev := stepDenom_pos hk prior c prev
  have hnum : 0 < (((c.counts prev next : ℕ) : ℝ) + (prior prev).priorParams next) := by
    have hcnt : 0 ≤ ((c.counts prev next : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hα : 0 < (prior prev).priorParams next := (prior prev).params_pos next
    linarith
  exact div_pos hnum hden

private lemma prefixAux_ne_zero (hk : 0 < k) (prior : Fin k → DirichletParams k) :
    ∀ (prev : Fin k) (c : TransCounts k) (xs : List (Fin k)),
      prefixAux (k := k) prior prev c xs ≠ 0 := by
  intro prev c xs
  induction xs generalizing prev c with
  | nil =>
      simp [prefixAux]
  | cons b xs ih =>
      -- Both factors are strictly positive reals, hence their `ENNReal.ofReal` is nonzero.
      have hb : 0 < stepProb prior c prev b := stepProb_pos (k := k) hk prior c prev b
      have hb0 : ENNReal.ofReal (stepProb prior c prev b) ≠ 0 := by
        exact (ENNReal.ofReal_ne_zero_iff).2 hb
      have htail :
          prefixAux (k := k) prior b (TransCounts.bump c prev b) xs ≠ 0 :=
        ih (prev := b) (c := TransCounts.bump c prev b)
      simpa [prefixAux] using mul_ne_zero hb0 htail

private lemma prefixProb_ne_zero (hk : 0 < k) (prior : Fin k → DirichletParams k) :
    ∀ xs : List (Fin k), prefixProb (k := k) prior xs ≠ 0 := by
  intro xs
  cases xs with
  | nil =>
      simp [prefixProb]
  | cons b xs =>
      have hb : 0 < initProb (k := k) b := initProb_pos (k := k) hk b
      have hb0 : ENNReal.ofReal (initProb (k := k) b) ≠ 0 := by
        exact (ENNReal.ofReal_ne_zero_iff).2 hb
      have htail :
          prefixAux (k := k) prior b TransCounts.zero xs ≠ 0 :=
        prefixAux_ne_zero (k := k) hk prior b TransCounts.zero xs
      simpa [prefixProb] using mul_ne_zero hb0 htail

/-- Any Markov-Dirichlet prefix measure with strictly positive parameters assigns nonzero
probability to every finite prefix. -/
theorem markovDirichletPrefixMeasure_ne_zero (hk : 0 < k) (prior : Fin k → DirichletParams k) :
    ∀ xs : List (Fin k), (markovDirichletPrefixMeasure (k := k) hk prior) xs ≠ 0 := by
  -- This is just `prefixProb_ne_zero` for the underlying `toFun`.
  intro xs
  exact prefixProb_ne_zero (k := k) hk prior xs

end MarkovDirichlet

end Mettapedia.Logic.UniversalPrediction
