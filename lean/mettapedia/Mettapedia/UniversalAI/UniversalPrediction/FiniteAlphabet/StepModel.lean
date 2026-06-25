import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure

/-!
# Finite-Alphabet Step Models → Prefix Measures

Many tractable predictors (conjugate families, online Bayesian mixtures, etc.) are most naturally
specified as *state machines* that emit a 1-step predictive distribution.

This file packages the generic construction:

- a state type `σ`
- an initial state `s0 : σ`
- a step distribution `step : σ → α → ENNReal` that sums to `1` for each state
- a state update `update : σ → α → σ`

yields a `FiniteAlphabet.PrefixMeasure α` via the usual product-of-conditionals recursion.

This lets new models focus on the math in their `step/update` rules, without re-proving the
prefix-additivity boilerplate each time.
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet

open scoped Classical BigOperators

/-- A 1-step predictive model over a finite alphabet `α`.

`step s` is a probability mass function (in `ENNReal`) and `update` advances the internal state.
-/
structure StepModel (α σ : Type*) [Fintype α] where
  /-- Initial state -/
  s0 : σ
  /-- 1-step predictive distribution -/
  step : σ → α → ENNReal
  /-- State update after observing a symbol -/
  update : σ → α → σ
  /-- The step distribution sums to `1` for every state -/
  step_sum : ∀ s, (∑ a : α, step s a) = 1

namespace StepModel

variable {α σ : Type*} [Fintype α]

/-- Recursively compute the prefix weight of a word, starting from state `s`.

This is the product of step probabilities along the word, with `update` applied sequentially.
-/
def prefixAux (M : StepModel α σ) : σ → Word α → ENNReal
  | _s, [] => 1
  | s, a :: xs => M.step s a * prefixAux M (M.update s a) xs

@[simp] lemma prefixAux_nil (M : StepModel α σ) (s : σ) : M.prefixAux s [] = 1 := rfl

@[simp] lemma prefixAux_cons (M : StepModel α σ) (s : σ) (a : α) (xs : Word α) :
    M.prefixAux s (a :: xs) = M.step s a * M.prefixAux (M.update s a) xs := rfl

/-- Prefix additivity for `prefixAux`.

`∑ a, prefixAux s (xs ++ [a]) = prefixAux s xs`.
-/
lemma prefixAux_additive (M : StepModel α σ) (s : σ) :
    ∀ xs : Word α, (∑ a : α, M.prefixAux s (xs ++ [a])) = M.prefixAux s xs := by
  intro xs
  induction xs generalizing s with
  | nil =>
      -- `xs = []`: `prefixAux s [a] = step s a`.
      simpa [prefixAux] using (M.step_sum s)
  | cons b xs ih =>
      -- Factor out the fixed first step probability.
      have hmul :
          (∑ a : α, M.step s b * M.prefixAux (M.update s b) (xs ++ [a])) =
            M.step s b * ∑ a : α, M.prefixAux (M.update s b) (xs ++ [a]) := by
        simpa using
          (Finset.mul_sum (a := M.step s b) (s := (Finset.univ : Finset α))
            (f := fun a : α => M.prefixAux (M.update s b) (xs ++ [a]))).symm
      calc
        (∑ a : α, M.prefixAux s ((b :: xs) ++ [a]))
            = ∑ a : α, M.step s b * M.prefixAux (M.update s b) (xs ++ [a]) := by
                simp [List.cons_append]
        _ = M.step s b * ∑ a : α, M.prefixAux (M.update s b) (xs ++ [a]) := hmul
        _ = M.step s b * M.prefixAux (M.update s b) xs := by
              simp [ih]
        _ = M.prefixAux s (b :: xs) := by
              simp [prefixAux]

/-- The `FiniteAlphabet.PrefixMeasure` induced by a step model. -/
noncomputable def toPrefixMeasure (M : StepModel α σ) : PrefixMeasure α :=
  { toFun := fun xs => M.prefixAux M.s0 xs
    root_eq_one' := by
      simp [prefixAux]
    additive' := by
      intro xs
      simpa [prefixAux] using (prefixAux_additive (M := M) (s := M.s0) xs) }

@[simp] lemma toPrefixMeasure_apply (M : StepModel α σ) (xs : Word α) :
    M.toPrefixMeasure xs = M.prefixAux M.s0 xs := rfl

end StepModel

end Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet
