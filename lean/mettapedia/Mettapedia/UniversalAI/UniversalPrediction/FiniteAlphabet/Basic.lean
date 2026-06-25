import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Universal Prediction Core (Finite Alphabet)

This file provides the *alphabet-parametric* core notions used throughout Hutter-style
universal prediction:

* `Semimeasure α` on finite words `List α` for a finite alphabet `α`
* universal mixtures `xiFun`
* dominance `Dominates`

The existing `Mettapedia.UniversalAI.UniversalPrediction` development is binary-focused
(`α := Bool`).  This file is the "Option (2)" extensible core: future conjugate
predictors (Dirichlet/Markov-Dirichlet, etc.) should target this API.
 -/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet

open scoped Classical BigOperators

universe u

abbrev Word (α : Type u) : Type u := List α

/-! ## Semimeasures -/

/-- A (sub)probability on cylinder events over a finite alphabet, represented as a function on
finite prefixes `x : List α`.

The defining axiom is the semimeasure inequality:
`sum_{a : α} μ(x ++ [a]) ≤ μ(x)`. -/
structure Semimeasure (α : Type*) [Fintype α] where
  /-- Prefix mass `μ(x)` for a finite word `x`. -/
  toFun : Word α → ENNReal
  /-- Semimeasure inequality: `∑ₐ μ(xa) ≤ μ(x)`. -/
  superadditive' : ∀ x : Word α, (∑ a : α, toFun (x ++ [a])) ≤ toFun x
  /-- Root bound: `μ(ε) ≤ 1`. -/
  root_le_one' : toFun [] ≤ 1

instance {α : Type*} [Fintype α] : CoeFun (Semimeasure α) (fun _ => Word α → ENNReal) where
  coe := Semimeasure.toFun

namespace Semimeasure

variable {α : Type u} [Fintype α]

@[simp] theorem root_le_one (μ : Semimeasure α) : μ ([] : Word α) ≤ 1 :=
  μ.root_le_one'

/-- Any one-step extension is bounded by the parent prefix. -/
theorem append_singleton_le (μ : Semimeasure α) (x : Word α) (a : α) : μ (x ++ [a]) ≤ μ x := by
  classical
  have hterm : μ (x ++ [a]) ≤ ∑ b : α, μ (x ++ [b]) := by
    -- `f a ≤ ∑ b, f b` for nonnegative `ENNReal` terms.
    have hnonneg : ∀ b : α, 0 ≤ μ (x ++ [b]) := fun _ => by simp
    simpa using
      (Finset.single_le_sum (s := (Finset.univ : Finset α)) (f := fun b => μ (x ++ [b]))
        (by intro b hb; exact hnonneg b) (by simp : a ∈ (Finset.univ : Finset α)))
  exact hterm.trans (μ.superadditive' x)

/-- Monotonicity on append: `μ(xy) ≤ μ(x)`. -/
theorem mono_append (μ : Semimeasure α) (x y : Word α) : μ (x ++ y) ≤ μ x := by
  induction y generalizing x with
  | nil =>
      simp
  | cons a y ih =>
      -- `μ(x ++ a :: y) ≤ μ(x ++ [a]) ≤ μ(x)`.
      have h1 : μ ((x ++ [a]) ++ y) ≤ μ (x ++ [a]) := ih (x := x ++ [a])
      have h2 : μ (x ++ [a]) ≤ μ x := append_singleton_le (μ := μ) (x := x) a
      simpa [List.append_assoc] using h1.trans h2

/-- Semimeasures are bounded by `1`. -/
theorem le_one (μ : Semimeasure α) (x : Word α) : μ x ≤ 1 := by
  have hmono : μ x ≤ μ ([] : Word α) := by
    simpa using (mono_append (μ := μ) ([] : Word α) x)
  exact hmono.trans (root_le_one (μ := μ))

theorem ne_top (μ : Semimeasure α) (x : Word α) : μ x ≠ (⊤ : ENNReal) := by
  have hle : μ x ≤ 1 := le_one (μ := μ) x
  have htop : (1 : ENNReal) < ⊤ := by simp
  exact (lt_top_iff_ne_top).1 (lt_of_le_of_lt hle htop)

end Semimeasure

/-! ## Universal mixtures (alphabet-parametric) -/

/-- Weighted mixture of semimeasures, `xi(x) := ∑' i, w i * ν i x`. -/
noncomputable def xiFun {α : Type u} {ι : Type*} [Fintype α] (ν : ι → Semimeasure α) (w : ι → ENNReal)
    (x : Word α) : ENNReal :=
  ∑' i, w i * ν i x

/-- Trivial dominance: a term is bounded by the full mixture. -/
theorem xi_dominates_index {α ι : Type*} [Fintype α] (ν : ι → Semimeasure α) (w : ι → ENNReal)
    (i : ι) (x : Word α) :
    w i * ν i x ≤ xiFun ν w x := by
  unfold xiFun
  simpa using (ENNReal.le_tsum (f := fun j => w j * ν j x) i)

/-- The mixture preserves the semimeasure (superadditivity) inequality. -/
theorem xi_superadditive {α ι : Type*} [Fintype α] (ν : ι → Semimeasure α) (w : ι → ENNReal)
    (x : Word α) :
    (∑ a : α, xiFun ν w (x ++ [a])) ≤ xiFun ν w x := by
  classical
  -- Swap the finite sum over `a` with the `tsum` over `i` by expressing the finite sum as a `tsum`.
  have hswap :
      (∑ a : α, xiFun ν w (x ++ [a])) =
        ∑' i : ι, ∑ a : α, w i * ν i (x ++ [a]) := by
    calc
      (∑ a : α, xiFun ν w (x ++ [a]))
          = ∑' a : α, xiFun ν w (x ++ [a]) := by
              simp [tsum_fintype]
      _ = ∑' i : ι, ∑' a : α, w i * ν i (x ++ [a]) := by
              -- Expand `xiFun` and commute the two `tsum`s.
              -- Avoid rewriting the outer `tsum` over the finite type `α` into a `Finset.sum`.
              simpa [xiFun, -tsum_fintype] using
                (ENNReal.tsum_comm (f := fun a i => w i * ν i (x ++ [a])))
      _ = ∑' i : ι, ∑ a : α, w i * ν i (x ++ [a]) := by
              refine tsum_congr ?_
              intro i
              simp [tsum_fintype]
  -- Now apply semimeasure inequality inside the `tsum`.
  have hterm : ∀ i : ι, (∑ a : α, w i * ν i (x ++ [a])) ≤ w i * ν i x := by
    intro i
    -- Factor out `w i` and use `ν i`'s semimeasure inequality.
    have hfac :
        (∑ a : α, w i * ν i (x ++ [a])) = w i * ∑ a : α, ν i (x ++ [a]) := by
      simpa using
        (Finset.mul_sum (a := w i) (f := fun a : α => ν i (x ++ [a]))
          (s := (Finset.univ : Finset α))).symm
    rw [hfac]
    -- Multiply by the nonnegative constant `w i` (left multiplication).
    exact mul_le_mul_of_nonneg_left ((ν i).superadditive' x) (by simp)
  calc
    (∑ a : α, xiFun ν w (x ++ [a]))
        = ∑' i : ι, ∑ a : α, w i * ν i (x ++ [a]) := hswap
    _ ≤ ∑' i : ι, w i * ν i x := by
          exact ENNReal.tsum_le_tsum hterm
    _ = xiFun ν w x := by
          simp [xiFun]

/-- A mixture of semimeasures is a semimeasure provided the weights sum to at most `1`. -/
noncomputable def xiSemimeasure {α ι : Type*} [Fintype α] (ν : ι → Semimeasure α) (w : ι → ENNReal)
    (hw : (∑' i, w i) ≤ 1) : Semimeasure α :=
  { toFun := xiFun ν w
    superadditive' := xi_superadditive ν w
    root_le_one' := by
      -- `xi([]) = ∑' i, w i * ν i [] ≤ ∑' i, w i * 1 = ∑' i, w i ≤ 1`.
      have hterm : ∀ i : ι, w i * ν i ([] : Word α) ≤ w i := by
        intro i
        have hroot : ν i ([] : Word α) ≤ 1 := (ν i).root_le_one'
        simpa [mul_one] using mul_le_mul_of_nonneg_left hroot (by simp)
      have hsum : (∑' i : ι, w i * ν i ([] : Word α)) ≤ ∑' i : ι, w i := by
        simpa [xiFun] using (ENNReal.tsum_le_tsum hterm)
      exact hsum.trans hw }

/-! ## Dominance -/

/-- `xi` dominates `nu` with constant `c` if `c * nu(x) ≤ xi(x)` for all prefixes `x`. -/
def Dominates {α : Type*} (xi nu : Word α → ENNReal) (c : ENNReal) : Prop :=
  ∀ x : Word α, c * nu x ≤ xi x

theorem Dominates.eq_zero_of_eq_zero {α : Type*} {xi nu : Word α → ENNReal} {c : ENNReal}
    (h : Dominates xi nu c) (hc0 : c ≠ 0) (x : Word α) (hx : xi x = 0) : nu x = 0 := by
  have hle : c * nu x ≤ 0 := by simpa [hx] using h x
  have heq : c * nu x = 0 := le_antisymm hle (by simp)
  rcases mul_eq_zero.1 heq with hc | hnu
  · exact (hc0 hc).elim
  · exact hnu

end Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet
