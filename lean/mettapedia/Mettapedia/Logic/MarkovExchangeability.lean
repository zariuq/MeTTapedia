import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Fintype.BigOperators

/-!
# Markov Exchangeability (Transition-Count Sufficiency)

This file sets up the *next* tractable “domain restriction” beyond i.i.d. exchangeability:

*Markov exchangeability / partial exchangeability for Markov chains*.

For a (finite) sequence of random variables taking values in a state space `α`, Markov
exchangeability asserts that the probability of a finite trajectory depends only on:

* the **initial state**, and
* the **transition count matrix** `N(a,b)` recording how many `a → b` transitions occur.

This yields a natural “evidence” object for sequence domains:

* `MarkovEvidence := (start, N)`  (for `α = Bool`, this is a 2×2 count matrix).

In the literature (Diaconis–Freedman, 1980), Markov exchangeability is equivalent to being a
mixture of Markov chains; the transition counts are sufficient statistics for prediction.  Here we
only formalize the *sufficiency* direction (probability factors through transition counts), which
is the key ingredient for building “Markov-PLN”-style finite-dimensional predictors.
-/

noncomputable section

namespace Mettapedia.Logic.MarkovExchangeability

open scoped BigOperators
open MeasureTheory Finset

/-! ## Transition counts for finite trajectories -/

section TransitionCounts

variable {α : Type*} [DecidableEq α]
variable {n : ℕ}

/-- Count of `a → b` transitions in a length `n+1` trajectory `xs`.

We count indices `i : Fin n` and look at the adjacent pair `(xs i, xs (i+1))`. -/
def transCount (xs : Fin (n + 1) → α) (a b : α) : ℕ :=
  (univ.filter (fun i : Fin n => xs (Fin.castSucc i) = a ∧ xs (Fin.succ i) = b)).card

/-- Markov evidence for a length `n+1` trajectory: initial state + transition counts. -/
@[ext]
structure MarkovEvidence (α : Type*) where
  start : α
  trans : α → α → ℕ

/-- Compute Markov evidence from a trajectory. -/
def evidenceOf (xs : Fin (n + 1) → α) : MarkovEvidence α :=
  { start := xs 0
    trans := fun a b => transCount (n := n) xs a b }

@[simp] theorem evidenceOf_start (xs : Fin (n + 1) → α) : (evidenceOf (n := n) xs).start = xs 0 :=
  rfl

@[simp] theorem evidenceOf_trans (xs : Fin (n + 1) → α) (a b : α) :
    (evidenceOf (n := n) xs).trans a b = transCount (n := n) xs a b :=
  rfl

end TransitionCounts

/-! ## Finite Markov exchangeability -/

section FiniteMarkovExchangeable

variable {Ω α : Type*} [MeasurableSpace Ω] [DecidableEq α]

/-- Cylinder event that the finite trajectory of random variables `X` matches `vals`. -/
def cylinder {n : ℕ} (X : Fin (n + 1) → Ω → α) (vals : Fin (n + 1) → α) : Set Ω :=
  { ω | ∀ i, X i ω = vals i }

/-- Finite Markov exchangeability: probability depends only on Markov evidence
(initial state + transition counts). -/
def FiniteMarkovExchangeable (n : ℕ) (X : Fin (n + 1) → Ω → α) (μ : Measure Ω) : Prop :=
  ∀ vals₁ vals₂ : Fin (n + 1) → α,
    evidenceOf (n := n) vals₁ = evidenceOf (n := n) vals₂ →
      μ (cylinder X vals₁) = μ (cylinder X vals₂)

theorem finiteMarkovExchangeable_sameEvidence_sameProb {n : ℕ} {X : Fin (n + 1) → Ω → α}
    {μ : Measure Ω} (h : FiniteMarkovExchangeable (α := α) n X μ)
    (vals₁ vals₂ : Fin (n + 1) → α)
    (he : evidenceOf (n := n) vals₁ = evidenceOf (n := n) vals₂) :
    μ (cylinder X vals₁) = μ (cylinder X vals₂) :=
  h _ _ he

end FiniteMarkovExchangeable

end Mettapedia.Logic.MarkovExchangeability

