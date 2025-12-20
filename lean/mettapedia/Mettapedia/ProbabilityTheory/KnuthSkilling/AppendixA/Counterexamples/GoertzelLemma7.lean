import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core.Induction.Construction

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples

open Classical
open scoped NNReal

open Mettapedia.ProbabilityTheory.KnuthSkilling
open KnuthSkillingAlgebra
open Real

/-!
# Counterexample: “new = old” does not imply a B-witness (Goertzel Lemma 7 pitfall)

Goertzel’s Lemma 7 (and some informal readings of K&S A.3.4) use:

1. If `X ⊕ d^u = Y ⊕ d^v` with `u > v`, cancel `d^v` to get `X ⊕ d^(u-v) = Y`.
2. Conclude this “creates a B-witness” for `u-v`, i.e. some old-grid value equals `d^(u-v)`.

Step (2) is not derivable from the algebraic equality `X ⊕ d^(u-v) = Y` alone: it requires
extra structure (e.g. a group/inverses, or a stronger cancellation/unique-decomposition property).

This file gives a concrete additive model where:
- `B` is globally empty: no old-grid value equals `d^u` for any `u>0`;
- yet there exist old-grid values `X, Y` with `X ⊕ d = Y`.
-/

section

private lemma nat_iterate_add_left_eq_mul (x : ℝ≥0) : ∀ n : ℕ,
    Nat.iterate (fun z : ℝ≥0 => x + z) n x = ((n + 1 : ℕ) : ℝ≥0) * x
  | 0 => by simp
  | n + 1 => by
      have ih := nat_iterate_add_left_eq_mul x n
      have h_step :
          Nat.iterate (fun z : ℝ≥0 => x + z) (n + 1) x
            = x + Nat.iterate (fun z : ℝ≥0 => x + z) n x := by
        simp [Function.iterate_succ_apply']
      rw [h_step, ih]
      have hcoeff : (((n + 1 : ℕ) : ℝ≥0) + 1) = ((n + 2 : ℕ) : ℝ≥0) := by
        have hn : (n + 1 + 1 : ℕ) = n + 2 := by omega
        calc
          ((n + 1 : ℕ) : ℝ≥0) + 1 = ((n + 1 + 1 : ℕ) : ℝ≥0) := by
            simpa using (Nat.cast_add (n + 1) 1).symm
          _ = ((n + 2 : ℕ) : ℝ≥0) := by
            simpa [hn]
      calc
        x + ((n + 1 : ℕ) : ℝ≥0) * x
            = ((n + 1 : ℕ) : ℝ≥0) * x + x := by
                simp [add_assoc, add_comm, add_left_comm]
        _ = (((n + 1 : ℕ) : ℝ≥0) + 1) * x := by
                simp [add_mul, one_mul]
        _ = ((n + 2 : ℕ) : ℝ≥0) * x := by
                exact congrArg (fun a : ℝ≥0 => a * x) hcoeff

noncomputable local instance : KnuthSkillingAlgebra ℝ≥0 where
  op := (· + ·)
  ident := 0
  op_assoc := by intro x y z; simp [add_assoc]
  op_ident_right := by intro x; simp
  op_ident_left := by intro x; simp
  op_strictMono_left := by intro y x₁ x₂ hx; exact add_lt_add_right hx y
  op_strictMono_right := by intro x y₁ y₂ hy; exact add_lt_add_left hy x
  op_archimedean := by
    intro x y hx
    have hx' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (y : ℝ) / (x : ℝ) < n :=
      exists_nat_gt ((y : ℝ) / (x : ℝ))
    refine ⟨n, ?_⟩
    have hy_lt_nx : (y : ℝ) < (n : ℝ) * (x : ℝ) := by
      have := mul_lt_mul_of_pos_right hn hx'
      simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt hx'), mul_one] using this
    have hy_lt_n1x : (y : ℝ) < ((n + 1 : ℕ) : ℝ) * (x : ℝ) := by
      have hx_nonneg : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hx'
      have hn_le : (n : ℝ) * (x : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (x : ℝ) := by
        gcongr
        exact Nat.cast_le.2 (Nat.le_succ n)
      exact lt_of_lt_of_le hy_lt_nx hn_le
    have hy_lt_n1x' : y < ((n + 1 : ℕ) : ℝ≥0) * x := by
      exact_mod_cast hy_lt_n1x
    have h_iter : Nat.iterate (fun z : ℝ≥0 => x + z) n x = ((n + 1 : ℕ) : ℝ≥0) * x :=
      nat_iterate_add_left_eq_mul x n
    have : y < Nat.iterate (fun z : ℝ≥0 => x + z) n x := by
      simpa [h_iter] using hy_lt_n1x'
    simpa [KnuthSkillingAlgebra.op] using this
  ident_le := by intro x; exact bot_le

private noncomputable def i0 : Fin 2 := 0
private noncomputable def i1 : Fin 2 := 1

noncomputable def F2 : AtomFamily ℝ≥0 2 :=
  { atoms := fun i =>
      if h : i = i0 then (1 : ℝ≥0)
      else ⟨Real.sqrt 2, by positivity⟩
    pos := by
      intro i
      by_cases h : i = i0
      · subst h
        simpa [KnuthSkillingAlgebra.ident] using (show (0 : ℝ≥0) < 1 from zero_lt_one)
      · have : (0 : ℝ) < Real.sqrt 2 := by
          have : (0 : ℝ) < (2 : ℝ) := by norm_num
          simpa using Real.sqrt_pos.2 this
        -- Reduce the goal to `0 < √2` in `ℝ≥0`, then cast.
        have : (0 : ℝ≥0) < ⟨Real.sqrt 2, by positivity⟩ := by
          exact_mod_cast this
        simpa [if_neg h, KnuthSkillingAlgebra.ident] using this }

private lemma F2_atom0 : F2.atoms i0 = (1 : ℝ≥0) := by
  simp [F2, i0]

private lemma F2_atom1 : F2.atoms i1 = ⟨Real.sqrt 2, by positivity⟩ := by
  have : (i1 : Fin 2) ≠ i0 := by decide
  simp [F2, i0, i1, this]

private lemma iterate_op_add_eq_mul (x : ℝ≥0) : ∀ n : ℕ, iterate_op x n = (n : ℝ≥0) * x
  | 0 => by simp [iterate_op, KnuthSkillingAlgebra.ident]
  | n + 1 => by
      have ih := iterate_op_add_eq_mul x n
      calc
        iterate_op x (n + 1) = op x (iterate_op x n) := by
          simp [iterate_op_succ]
        _ = x + (n : ℝ≥0) * x := by simpa [KnuthSkillingAlgebra.op, ih]
        _ = (n : ℝ≥0) * x + x := by simp [add_comm, add_left_comm, add_assoc]
        _ = ((n : ℝ≥0) + 1) * x := by simp [add_mul, one_mul]
        _ = ((n + 1 : ℕ) : ℝ≥0) * x := by simp [Nat.cast_add, Nat.cast_one]

private lemma mu_F2 (r : Multi 2) :
    ((mu (α := ℝ≥0) F2 r : ℝ≥0) : ℝ) = (r i0 : ℝ) + (r i1 : ℝ) * Real.sqrt 2 := by
  classical
  -- Evaluate `mu` by unfolding the fold over `Fin 2 = {0,1}`.
  unfold mu
  -- Normalize `List.finRange 2` and the `foldl` step-by-step.
  simp [List.finRange_succ, List.finRange_zero, KnuthSkillingAlgebra.op, KnuthSkillingAlgebra.ident,
    op_ident_left, op_ident_right, add_assoc, add_left_comm, add_comm]
  -- Rewrite the two atom iterates.
  have h0 : ((iterate_op (α := ℝ≥0) (F2.atoms i0) (r i0) : ℝ≥0) : ℝ) = (r i0 : ℝ) := by
    -- atom0 = 1
    simp [F2_atom0, iterate_op_add_eq_mul, one_mul]
  have h1 :
      ((iterate_op (α := ℝ≥0) (F2.atoms i1) (r i1) : ℝ≥0) : ℝ) = (r i1 : ℝ) * Real.sqrt 2 := by
    -- atom1 = √2
    simp [F2_atom1, iterate_op_add_eq_mul, mul_assoc]
  -- Collect terms.
  have h0' :
      ((iterate_op (α := ℝ≥0) (F2.atoms 0) (r 0) : ℝ≥0) : ℝ) = (r 0 : ℝ) := by
    simpa [i0] using h0
  have h1' :
      ((iterate_op (α := ℝ≥0) (F2.atoms 1) (r 1) : ℝ≥0) : ℝ) = (r 1 : ℝ) * Real.sqrt 2 := by
    simpa [i1] using h1
  calc
    ((iterate_op (α := ℝ≥0) (F2.atoms 0) (r 0) : ℝ≥0) : ℝ) +
          ((iterate_op (α := ℝ≥0) (F2.atoms 1) (r 1) : ℝ≥0) : ℝ)
        = (r 0 : ℝ) + (r 1 : ℝ) * Real.sqrt 2 := by
            simpa [h0', h1']
    _ = (r i0 : ℝ) + (r i1 : ℝ) * Real.sqrt 2 := by
          simp [i0, i1]

noncomputable def d : ℝ≥0 := ⟨2 - Real.sqrt 2, by
  have hs : (Real.sqrt 2 : ℝ) < 2 := by
    exact lt_trans Real.sqrt_two_lt_three_halves (by norm_num)
  have : (0 : ℝ) < 2 - Real.sqrt 2 := by linarith
  exact this.le⟩

lemma d_pos : (KnuthSkillingAlgebra.ident : ℝ≥0) < d := by
  have hs : (Real.sqrt 2 : ℝ) < 2 := by
    exact lt_trans Real.sqrt_two_lt_three_halves (by norm_num)
  have : (0 : ℝ) < 2 - Real.sqrt 2 := by linarith
  exact_mod_cast this

private lemma iterate_op_d (u : ℕ) :
    ((iterate_op (α := ℝ≥0) d u : ℝ≥0) : ℝ) = (u : ℝ) * (2 - Real.sqrt 2) := by
  simp [d, iterate_op_add_eq_mul, mul_assoc]

lemma B_empty_for_F2_d : ∀ r u, 0 < u → r ∉ extensionSetB F2 d u := by
  intro r u hu hrB
  have hEq : mu F2 r = iterate_op d u := by
    simpa [extensionSetB, Set.mem_setOf_eq] using hrB
  -- Coerce to ℝ and expand both sides.
  have hEqR :
      ((mu (α := ℝ≥0) F2 r : ℝ≥0) : ℝ) = ((iterate_op d u : ℝ≥0) : ℝ) :=
    congrArg (fun x : ℝ≥0 => (x : ℝ)) hEq
  have hmu :
      ((mu (α := ℝ≥0) F2 r : ℝ≥0) : ℝ) = (r i0 : ℝ) + (r i1 : ℝ) * Real.sqrt 2 :=
    mu_F2 r
  have hit : ((iterate_op d u : ℝ≥0) : ℝ) = (u : ℝ) * (2 - Real.sqrt 2) := iterate_op_d u
  -- Rearrange to isolate `sqrt 2` with a positive nat coefficient:
  --   (r₁ + u) * √2 = 2u - r₀
  have hLin :
      ((r i1 : ℕ) + u : ℕ) * Real.sqrt 2 = (2 : ℝ) * (u : ℝ) - (r i0 : ℝ) := by
    have hEq' :
        (r i0 : ℝ) + (r i1 : ℝ) * Real.sqrt 2 =
          (u : ℝ) * 2 - (u : ℝ) * Real.sqrt 2 := by
      -- Put both sides in the same normal form.
      have : (r i0 : ℝ) + (r i1 : ℝ) * Real.sqrt 2 = (u : ℝ) * (2 - Real.sqrt 2) := by
        simpa [hmu, hit] using hEqR
      simpa [sub_eq_add_neg, mul_sub, mul_assoc, mul_add, add_assoc, add_left_comm, add_comm] using this
    -- Move the `√2` terms to the left.
    -- (r₁ + u) * √2 = 2u - r₀
    have : ((r i1 : ℝ) + (u : ℝ)) * Real.sqrt 2 = (2 : ℝ) * (u : ℝ) - (r i0 : ℝ) := by
      linarith [hEq']
    simpa [Nat.cast_add, add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using this

  -- RHS is an integer (as a real); LHS is irrational, contradiction.
  have hirr : Irrational (Real.sqrt 2) := by
    simpa using (Nat.Prime.irrational_sqrt (p := 2) (by norm_num))
  have hirr_mul : Irrational (((r i1 : ℕ) + u : ℕ) * Real.sqrt 2) := by
    -- `Irrational.mul_natCast` gives `Irrational (√2 * n)`; commute the product.
    simpa [mul_comm] using hirr.mul_natCast (m := (r i1 : ℕ) + u) (by omega)
  -- Express the RHS as an integer cast.
  let z : ℤ := (2 * u : ℤ) - (r i0 : ℤ)
  have hz : (2 : ℝ) * (u : ℝ) - (r i0 : ℝ) = (z : ℝ) := by
    simp [z, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Nat.cast_ofNat, two_mul, mul_assoc]
  have : ((r i1 : ℕ) + u : ℕ) * Real.sqrt 2 = (z : ℝ) := by
    simpa [hz] using hLin
  exact hirr_mul.ne_int z this

/-!
Now exhibit `X, Y` old-grid values with `X ⊕ d = Y`.
Take `X = √2` and `Y = 2`.
-/

noncomputable def rX : Multi 2 := fun i => if i = i0 then 0 else 1
noncomputable def rY : Multi 2 := fun i => if i = i0 then 2 else 0

lemma mu_rX : ((mu (α := ℝ≥0) F2 rX : ℝ≥0) : ℝ) = Real.sqrt 2 := by
  have : (rX i0 : ℝ) = 0 := by simp [rX, i0]
  have : (rX i1 : ℝ) = 1 := by
    have : (i1 : Fin 2) ≠ i0 := by decide
    simp [rX, i1, i0, this]
  simpa [mu_F2, rX, i0, i1, this, one_mul, zero_add, add_zero]

lemma mu_rY : ((mu (α := ℝ≥0) F2 rY : ℝ≥0) : ℝ) = 2 := by
  have : (rY i0 : ℝ) = 2 := by simp [rY, i0]
  have : (rY i1 : ℝ) = 0 := by
    have : (i1 : Fin 2) ≠ i0 := by decide
    simp [rY, i1, i0, this]
  simpa [mu_F2, rY, i0, i1, this, zero_mul, add_zero]

theorem exists_old_new_eq_old_while_B_empty :
    (∀ r u, 0 < u → r ∉ extensionSetB F2 d u) ∧
    (∃ (r_old_x r_old_y : Multi 2),
        op (mu F2 r_old_x) (iterate_op d 1) = mu F2 r_old_y) := by
  refine ⟨B_empty_for_F2_d, ?_⟩
  refine ⟨rX, rY, ?_⟩
  -- In ℝ≥0 with addition, `iterate_op d 1 = d`, so √2 + (2 - √2) = 2.
  apply Subtype.ext
  change ((mu (α := ℝ≥0) F2 rX : ℝ≥0) : ℝ) + ((iterate_op d 1 : ℝ≥0) : ℝ) =
    ((mu (α := ℝ≥0) F2 rY : ℝ≥0) : ℝ)
  -- Rewrite the old-grid values and `iterate_op d 1`.
  rw [mu_rX, mu_rY]
  -- `iterate_op d 1 = d` and `d = 2 - √2`.
  simp [iterate_op_one, d, add_assoc, add_left_comm, add_comm]

end

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples
