import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Basic
import Mettapedia.Logic.SolomonoffPrior

/-!
# Solomonoff Induction Following Hutter (2005)

This file formalizes Solomonoff's theory of universal induction following
Marcus Hutter's "Universal Artificial Intelligence" (2005), Chapter 2.

## Main Definitions

* `Semimeasure` - A function μ : BinString → ENNReal satisfying μ(x0) + μ(x1) ≤ μ(x)
* `universalPrior` - The Solomonoff prior M(x) = ∑_{p: U(p)=x*} 2^{-ℓ(p)}
* `conditionalProbability` - M(y|x) := M(xy)/M(x) for prediction

## Key Results

* `universalPrior_is_semimeasure` - M satisfies the semimeasure axioms

## References

- Hutter, Marcus (2005). "Universal Artificial Intelligence"
  - Chapter 2: Simplicity & Uncertainty
  - Definition 2.22: (Semi)measures, p. 46
  - Equation (2.21): Universal Prior M, p. 46
  - Theorem 2.23: Universality, p. 46
  - Theorem 2.25: Convergence, p. 48

-/

namespace Mettapedia.Logic.SolomonoffInduction

open Mettapedia.Logic.SolomonoffPrior
open InfBinString

/-! ## Definition 2.22: (Semi)measures (Hutter 2005, p. 46)

From Hutter (p. 46):
> "A function μ : ℬ* → [0,1] with μ(x0) + μ(x1) = μ(x) and μ(ε) = 1
>  is called a (probability) measure.
>  A function μ : ℬ* → [0,1] with μ(x0) + μ(x1) ≤ μ(x) and μ(ε) ≤ 1
>  is called a semimeasure."

We formalize using ENNReal (extended non-negative reals) for compatibility with mathlib's measure theory.
-/

/-- A semimeasure on binary strings following Hutter (2005), Definition 2.22.

    A semimeasure satisfies:
    1. μ(x0) + μ(x1) ≤ μ(x) (superadditivity - probability mass can be "lost")
    2. μ(ε) ≤ 1 (normalization)

    The inequality allows for programs that halt after outputting x,
    contributing to μ(x) but not to μ(x0) or μ(x1).
-/
structure Semimeasure where
  /-- The measure function on finite binary strings -/
  toFun : BinString → ENNReal
  /-- Superadditivity: sum of children ≤ parent -/
  superadditive' : ∀ x : BinString, toFun (x ++ [false]) + toFun (x ++ [true]) ≤ toFun x
  /-- Normalization: empty string has measure ≤ 1 -/
  root_le_one' : toFun [] ≤ 1

instance : CoeFun Semimeasure (fun _ => BinString → ENNReal) where
  coe := Semimeasure.toFun

namespace Semimeasure

variable (ν : Semimeasure)

/-- Measures are nonnegative (automatically satisfied by ℝ≥0∞) -/
theorem nonneg (x : BinString) : 0 ≤ ν x := zero_le

/-- Monotonicity: extending a prefix decreases the measure -/
theorem mono (x : BinString) (b : Bool) : ν (x ++ [b]) ≤ ν x := by
  cases b
  · calc ν (x ++ [false])
        ≤ ν (x ++ [false]) + ν (x ++ [true]) := le_self_add
      _ ≤ ν x := ν.superadditive' x
  · calc ν (x ++ [true])
        ≤ ν (x ++ [false]) + ν (x ++ [true]) := le_add_self
      _ ≤ ν x := ν.superadditive' x

/-- General monotonicity: appending any string decreases the measure -/
theorem mono_append (x y : BinString) : ν (x ++ y) ≤ ν x := by
  induction y generalizing x with
  | nil => simp
  | cons b y ih =>
    calc ν (x ++ (b :: y))
        = ν ((x ++ [b]) ++ y) := by simp [List.append_assoc]
      _ ≤ ν (x ++ [b]) := ih (x ++ [b])
      _ ≤ ν x := ν.mono x b

/-- Conditional probability following Hutter's notation M(y|x) := M(xy)/M(x) -/
noncomputable def conditionalProb (ν : Semimeasure) (y : BinString) (x : BinString) : ℝ :=
  if ν x = 0 then 0
  else (ν (x ++ y)).toReal / (ν x).toReal

notation:50 ν "⟨" y "|" x "⟩" => conditionalProb ν y x

/-- Conditional probability of next bit: M(b|x) := M(xb)/M(x) -/
noncomputable def predictNextBit (ν : Semimeasure) (x : BinString) (b : Bool) : ℝ :=
  ν⟨[b]|x⟩

theorem conditionalProb_nonneg (ν : Semimeasure) (y x : BinString) :
    0 ≤ conditionalProb ν y x := by
  unfold conditionalProb
  split_ifs
  · exact le_refl 0
  · apply div_nonneg <;> exact ENNReal.toReal_nonneg

theorem conditionalProb_le_one (ν : Semimeasure) (y x : BinString) (hpos : ν x ≠ 0) :
    conditionalProb ν y x ≤ 1 := by
  unfold conditionalProb
  simp only [hpos, ↓reduceIte]
  -- Have: ν (x ++ y) ≤ ν x by monotonicity
  have hmono := ν.mono_append x y
  -- Convert to Real and show division ≤ 1
  by_cases h : ν (x ++ y) = ⊤ ∨ ν x = ⊤
  · -- If either is ⊤, the ratio might be problematic, but ν x ≠ 0 and semimeasure properties
    -- should prevent ⊤ in practice. For now we handle it carefully.
    cases h with
    | inl hxy =>
      -- ν (x ++ y) = ⊤, but hmono says ν (x ++ y) ≤ ν x, so ν x = ⊤ too
      have : ν x = ⊤ := le_antisymm (le_top) (hxy ▸ hmono)
      simp [this, ENNReal.toReal_top]
    | inr hx =>
      -- ν x = ⊤, contradiction with being a semimeasure (root_le_one' implies bounded)
      -- But we don't have that ν x is necessarily the root. Let's just handle it.
      simp [hx, ENNReal.toReal_top]
  · push_neg at h
    -- Both are finite, so toReal preserves order
    have hxy_fin : ν (x ++ y) ≠ ⊤ := h.1
    have hx_fin : ν x ≠ ⊤ := h.2
    have hx_pos : 0 < (ν x).toReal := ENNReal.toReal_pos hpos hx_fin
    have hx_ne : (ν x).toReal ≠ 0 := ne_of_gt hx_pos
    calc (ν (x ++ y)).toReal / (ν x).toReal
        ≤ (ν x).toReal / (ν x).toReal := by
          apply div_le_div_of_nonneg_right
          · exact ENNReal.toReal_mono hx_fin hmono
          · exact le_of_lt hx_pos
      _ = 1 := div_self hx_ne

/-- Sum of conditional probabilities for next two bits ≤ 1 (semimeasure property) -/
theorem predictive_subprob (ν : Semimeasure) (x : BinString) (hpos : ν x ≠ 0) :
    ν.predictNextBit x false + ν.predictNextBit x true ≤ 1 := by
  unfold predictNextBit conditionalProb
  simp only [hpos, ↓reduceIte]
  by_cases h : ν x = ⊤
  · -- If ν x = ⊤, then (ν x).toReal = 0, so both conditional probs are 0/0 = 0
    simp [h, ENNReal.toReal_top]
  · -- ν x is finite and nonzero
    have hsub := ν.superadditive' x
    -- Need: (ν(x0)).toReal / (ν x).toReal + (ν(x1)).toReal / (ν x).toReal ≤ 1
    -- Equivalent to: ((ν(x0) + ν(x1)).toReal) / (ν x).toReal ≤ 1
    -- From superadditivity: ν(x0) + ν(x1) ≤ ν x
    have hx_pos : 0 < (ν x).toReal := ENNReal.toReal_pos hpos h
    -- Need to show both children are finite for toReal_add
    have h0_fin : ν (x ++ [false]) ≠ ⊤ := by
      by_contra hcontra
      have := ν.mono x false
      rw [hcontra] at this
      have : ν x = ⊤ := le_antisymm le_top this
      exact h this
    have h1_fin : ν (x ++ [true]) ≠ ⊤ := by
      by_contra hcontra
      have := ν.mono x true
      rw [hcontra] at this
      have : ν x = ⊤ := le_antisymm le_top this
      exact h this
    calc (ν (x ++ [false])).toReal / (ν x).toReal + (ν (x ++ [true])).toReal / (ν x).toReal
        = ((ν (x ++ [false])).toReal + (ν (x ++ [true])).toReal) / (ν x).toReal := by
          rw [add_div]
      _ = (ν (x ++ [false]) + ν (x ++ [true])).toReal / (ν x).toReal := by
          rw [ENNReal.toReal_add h0_fin h1_fin]
      _ ≤ (ν x).toReal / (ν x).toReal := by
          apply div_le_div_of_nonneg_right
          · exact ENNReal.toReal_mono h (hsub)
          · exact le_of_lt hx_pos
      _ = 1 := by rw [div_self (ne_of_gt hx_pos)]

end Semimeasure

/-! ## Equation (2.21): The Universal Prior M (Hutter 2005, p. 46)

From Hutter (p. 46):
> "The universal prior is defined as the probability that the output of a
>  universal monotone Turing machine starts with x when provided with fair
>  coin flips on the input tape. Formally, M can be defined as
>
>      M(x) := ∑_{p: U(p)=x*} 2^{-ℓ(p)}
>
>  where the sum is over minimal programs p for which U outputs a string
>  starting with x."

We use the cylinderMeasure from SolomonoffPrior.lean which implements this.
-/

/-- The universal prior M as a semimeasure following Hutter (2005).

    Constructed from cylinderMeasure:
    M(x) = ∑_{p : U(p) extends x} 2^{-|p|}

    We show this satisfies the semimeasure axioms.
-/
noncomputable def universalPrior (U : MonotoneMachine) (programs : Finset BinString)
    (hpf : PrefixFree (↑programs : Set BinString)) : Semimeasure where
  toFun := fun x => ENNReal.ofReal (U.cylinderMeasure programs x)
  superadditive' := by
    intro x
    have hsub := cylinderMeasure_subadditive U programs x
    have h0 := U.cylinderMeasure_nonneg programs (x ++ [false])
    have h1 := U.cylinderMeasure_nonneg programs (x ++ [true])
    have hx := U.cylinderMeasure_nonneg programs x
    -- Need: ofReal(μ(x0)) + ofReal(μ(x1)) ≤ ofReal(μ(x))
    -- Have: μ(x0) + μ(x1) ≤ μ(x) where all μ(·) ≥ 0
    calc ENNReal.ofReal (U.cylinderMeasure programs (x ++ [false])) +
         ENNReal.ofReal (U.cylinderMeasure programs (x ++ [true]))
        = ENNReal.ofReal (U.cylinderMeasure programs (x ++ [false]) +
                          U.cylinderMeasure programs (x ++ [true])) := by
          exact (ENNReal.ofReal_add h0 h1).symm
      _ ≤ ENNReal.ofReal (U.cylinderMeasure programs x) := by
          exact ENNReal.ofReal_le_ofReal hsub
  root_le_one' := by
    exact ENNReal.ofReal_le_one.mpr (cylinderMeasure_le_one U programs hpf)

/-! ## Hutter's Approach: Working Only with Cylinders

Following Hutter, we DON'T extend M to an outer measure on all sets.
Instead:
1. Keep M defined ONLY on finite prefixes (cylinder sets)
2. Use M(xy)/M(x) for conditional probabilities
3. Prove convergence using these ratios

This is simpler and more faithful to Hutter's actual formalization.
-/

/-- Conditional probability under the universal prior: M(y|x) = M(xy)/M(x) -/
noncomputable def M_conditional (U : MonotoneMachine) (programs : Finset BinString)
    (hpf : PrefixFree (↑programs : Set BinString)) (y x : BinString) : ℝ :=
  (universalPrior U programs hpf)⟨y|x⟩

/-! ## Notes on universality & convergence

Hutter’s Theorem 2.23 (universality of `M`) and Theorem 2.25 (posterior convergence of `M`)
depend on additional computability/enumeration results (Levin’s theorem) and are deferred to
Chapter 3 in the book.

In this repository, the universal mixture `ξ` and Bayes update machinery are formalized in
`Mettapedia/Logic/UniversalPrediction.lean`, and Chapter‑2 imports re-export the “obvious”
dominance lemmas needed to state Theorem 2.23 once the enumeration bridge is added.
-/

end Mettapedia.Logic.SolomonoffInduction
