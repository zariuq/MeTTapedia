/-
# Counterexample: Negative Values Without Identity

K&S claim (p.42): "fidelity ensures that other elements are quantified by positive values."

This file proves that claim is FALSE for unbounded distributive lattices.

## The Gap

K&S's positivity proof (p.45) uses "we may set m(⊥) = 0". But distributive lattices
don't require ⊥. For (ℤ, ≤) — a valid distributive lattice with no bottom — the
Hölder representation theorem applies but produces NEGATIVE values.

## Main Results

1. `Int.instKSSemigroupBase` — ℤ satisfies K&S semigroup axioms
2. `MultiplicativeInt.no_anomalous_pair` — ℤ has no anomalous pairs
3. `holder_embedding_produces_negatives` — THE embedding from `holder_not_anom` has Φ(-1) < 0

The key insight: positivity comes from `ident_le : ∀ x, ident ≤ x`, not from
the representation theorem itself.
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Basic
import OrderedSemigroups.Holder
import Mathlib.Algebra.Group.TypeTags.Basic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples

open KSSemigroupBase

/-! ## Part 1: ℤ as a KSSemigroupBase -/

/-- ℤ is a distributive lattice (every chain is). -/
example : DistribLattice ℤ := inferInstance

/-- ℤ has no bottom element. -/
theorem Int.unbounded_below : ¬∃ bot : ℤ, ∀ n : ℤ, bot ≤ n := by
  intro ⟨bot, hbot⟩; have := hbot (bot - 1); omega

/-- **ℤ is a KSSemigroupBase** with `op = (+)`. -/
instance Int.instKSSemigroupBase : KSSemigroupBase ℤ where
  op := (· + ·)
  op_assoc := add_assoc
  op_strictMono_left := fun y => by intro a b hab; show a + y < b + y; omega
  op_strictMono_right := fun x => by intro a b hab; show x + a < x + b; omega

theorem Int.op_eq_add : ∀ a b : ℤ, op a b = a + b := fun _ _ => rfl

/-- ℤ cannot satisfy `ident_le` (identity-as-minimum). -/
theorem Int.cannot_satisfy_ident_le : ¬(∀ n : ℤ, (0 : ℤ) ≤ n) := by push_neg; use -1; omega

/-! ## Part 2: Bounded Lattices DO Give Positivity -/

/-- When we have ⊥ and normalize v(⊥) = 0, fidelity gives positivity. -/
theorem positivity_from_bounded_lattice {α : Type*} [Lattice α] [OrderBot α]
    (v : α → ℝ) (hFidelity : ∀ a b : α, a < b → v a < v b)
    (hNormalized : v ⊥ = 0) (x : α) (hx : ⊥ < x) : 0 < v x :=
  calc 0 = v ⊥ := hNormalized.symm
       _ < v x := hFidelity ⊥ x hx

/-! ## Part 3: ℤ Has No Anomalous Pairs -/

/-- ℤ has no anomalous pairs — the Archimedean property rules them out.

An anomalous pair (a,b) requires ∀n, `n·a < n·b < (n+1)·a` or vice versa.
For ℤ, if a < b, then for large n, n·(b-a) ≥ a, contradicting the bound. -/
theorem Int.no_anomalous_pair_additive :
    ∀ a b : ℤ, ¬(∀ n : ℕ+, (n * a < n * b ∧ n * b < (n + 1) * a) ∨
                          (n * a > n * b ∧ n * b > (n + 1) * a)) := by
  intro a b hanom
  have h1 := hanom 1; simp only [PNat.val_ofNat, one_mul, Nat.cast_one] at h1
  rcases h1 with ⟨ha_lt_b, hb_lt_2a⟩ | ⟨ha_gt_b, hb_gt_2a⟩
  · -- Case: a < b < 2a (requires a > 0)
    have ha_pos : 0 < a := by omega
    have hba_ge_one : 1 ≤ b - a := by omega
    have key : ∀ m : ℕ, 0 < m → m * (b - a) < a → m < a := by intro m _ h; nlinarith
    let m := a.natAbs + 1
    have hm_pos : 0 < m := by omega
    have hanom_m := hanom ⟨m, hm_pos⟩; simp only [PNat.mk_coe] at hanom_m
    rcases hanom_m with ⟨_, hm_b_lt⟩ | ⟨hm_a_gt, _⟩
    · have h_key : (m : ℤ) * (b - a) < a := by nlinarith
      have := key m hm_pos h_key
      have : (m : ℤ) = a.natAbs + 1 := by simp [m]
      have : a = a.natAbs := (Int.natAbs_of_nonneg (by omega : 0 ≤ a)).symm
      omega
    · have : (m : ℤ) * a > (m : ℤ) * b := hm_a_gt; nlinarith
  · -- Case: a > b > 2a (requires a < 0)
    have ha_neg : a < 0 := by omega
    let m := (-a).natAbs + 1
    have hm_pos : 0 < m := by omega
    have hanom_m := hanom ⟨m, hm_pos⟩; simp only [PNat.mk_coe] at hanom_m
    rcases hanom_m with ⟨hm_a_lt, _⟩ | ⟨_, hm_b_gt⟩
    · have : (m : ℤ) * a < (m : ℤ) * b := hm_a_lt; nlinarith
    · have h_key : (m : ℤ) * (b - a) > a := by nlinarith
      have hba_neg : b - a ≤ -1 := by omega
      have : (m : ℤ) = (-a).natAbs + 1 := by simp [m]
      have : -a = (-a).natAbs := (Int.natAbs_of_nonneg (by omega : 0 ≤ -a)).symm
      nlinarith

/-! ## Part 4: Setting Up Multiplicative ℤ for Hölder -/

open Multiplicative in
instance : IsOrderedCancelSemigroup (Multiplicative ℤ) where
  mul_le_mul_left' {a b} hab c := by
    have h : toAdd a ≤ toAdd b := toAdd_le.mpr hab
    rw [← toAdd_le, toAdd_mul, toAdd_mul]; omega
  le_of_mul_le_mul_left' {a b} c hab := by
    rw [← toAdd_le, toAdd_mul, toAdd_mul] at hab; rw [← toAdd_le]; omega
  le_of_mul_le_mul_right' {a b} c hab := by
    rw [← toAdd_le, toAdd_mul, toAdd_mul] at hab; rw [← toAdd_le]; omega
  mul_le_mul_right' {a b} hab c := by
    have h : toAdd a ≤ toAdd b := toAdd_le.mpr hab
    rw [← toAdd_le, toAdd_mul, toAdd_mul]; omega

open Multiplicative in
instance : Pow (Multiplicative ℤ) ℕ+ where
  pow x n := ofAdd (n * toAdd x)

open Multiplicative in
instance : PNatPowAssoc (Multiplicative ℤ) where
  ppow_add m n x := by
    show ofAdd ((m + n : ℕ+) * toAdd x) = ofAdd (m * toAdd x) * ofAdd (n * toAdd x)
    rw [← ofAdd_add]; congr 1; push_cast; ring
  ppow_one x := by
    show ofAdd ((1 : ℕ+) * toAdd x) = x
    have h : (1 : ℕ+).val * toAdd x = toAdd x := one_mul (toAdd x)
    rw [h]; exact ofAdd_toAdd x

open Multiplicative in
/-- `Multiplicative ℤ` has no anomalous pairs. -/
theorem MultiplicativeInt.no_anomalous_pair : ¬has_anomalous_pair (α := Multiplicative ℤ) := by
  intro ⟨a, b, hanom⟩
  let a' := toAdd a; let b' := toAdd b
  have hanom' : ∀ n : ℕ+, (n * a' < n * b' ∧ n * b' < (n + 1) * a') ∨
                         (n * a' > n * b' ∧ n * b' > (n + 1) * a') := by
    intro n; have h := hanom n
    simp only [HPow.hPow, Pow.pow, ofAdd_lt] at h; exact h
  exact Int.no_anomalous_pair_additive a' b' hanom'

/-! ## Part 5: The Main Theorem -/

/-- **Main Theorem**: If ℤ has no anomalous pairs, `holder_not_anom` gives an embedding
with negative values.

The premise `hna : ¬has_anomalous_pair` is what `holder_not_anom` requires.
Inside the proof, we explicitly call `holder_not_anom hna` to get the embedding.

The proof then shows that embedding has Φ(-1) < 0:
1. Φ is additive: Φ(a+b) = Φ(a) + Φ(b)
2. Φ(0) = 0
3. Φ is strictly monotone (from order isomorphism)
4. Φ(1) > 0 (since 0 < 1)
5. Φ(-1) = -Φ(1) < 0 -/
theorem holder_embedding_produces_negatives
    (hna : ¬has_anomalous_pair (α := Multiplicative ℤ)) :
    ∃ (G : Subsemigroup (Multiplicative ℝ)) (Θ : Multiplicative ℤ ≃*o G),
      Multiplicative.toAdd (Θ (Multiplicative.ofAdd (-1)) : Multiplicative ℝ) < 0 := by
  -- Apply Hölder's theorem to get the embedding
  obtain ⟨G, ⟨Θ⟩⟩ := holder_not_anom hna
  refine ⟨G, Θ, ?_⟩
  let Φ : ℤ → ℝ := fun n => Multiplicative.toAdd (Θ (Multiplicative.ofAdd n) : Multiplicative ℝ)
  -- Φ is additive
  have hAdditive : ∀ a b : ℤ, Φ (a + b) = Φ a + Φ b := by
    intro a b; simp only [Φ]
    have hmul : Θ (Multiplicative.ofAdd a * Multiplicative.ofAdd b) =
                Θ (Multiplicative.ofAdd a) * Θ (Multiplicative.ofAdd b) :=
      Θ.map_mul _ _
    rw [show Multiplicative.ofAdd a * Multiplicative.ofAdd b =
            Multiplicative.ofAdd (a + b) from (ofAdd_add a b).symm] at hmul
    have hcoe : (↑(Θ (Multiplicative.ofAdd a) * Θ (Multiplicative.ofAdd b)) : Multiplicative ℝ) =
                (Θ (Multiplicative.ofAdd a) : Multiplicative ℝ) *
                (Θ (Multiplicative.ofAdd b) : Multiplicative ℝ) := by simp only [MulMemClass.coe_mul]
    conv_lhs => rw [hmul]; rw [hcoe, toAdd_mul]
  -- Φ(0) = 0
  have hZero : Φ 0 = 0 := by
    have h : Φ 0 = Φ 0 + Φ 0 := by rw [← hAdditive 0 0]; ring_nf
    linarith
  -- Φ is strictly monotone
  have hStrictMono : StrictMono Φ := by
    intro a b hab; simp only [Φ]
    have h : Multiplicative.ofAdd a < Multiplicative.ofAdd b := by rwa [Multiplicative.ofAdd_lt]
    have hΘ : Θ (Multiplicative.ofAdd a) < Θ (Multiplicative.ofAdd b) := by
      rw [show (Θ (Multiplicative.ofAdd a) < Θ (Multiplicative.ofAdd b)) ↔
              (Multiplicative.ofAdd a < Multiplicative.ofAdd b) from
          ⟨fun hlt => (OrderIsoClass.map_le_map_iff Θ).mp (le_of_lt hlt) |>
            fun hle => lt_of_le_of_ne hle (fun heq => by rw [heq] at hlt; exact lt_irrefl _ hlt),
           fun hlt => lt_of_le_of_ne ((OrderIsoClass.map_le_map_iff Θ).mpr (le_of_lt hlt))
              (fun heq => by
                have := (OrderIsoClass.map_le_map_iff Θ).mp (le_of_eq heq.symm)
                exact not_lt.mpr this hlt)⟩]
      exact h
    have hcoe : (Θ (Multiplicative.ofAdd a) : Multiplicative ℝ) <
                (Θ (Multiplicative.ofAdd b) : Multiplicative ℝ) := Subtype.coe_lt_coe.mpr hΘ
    exact Multiplicative.toAdd_lt.mpr hcoe
  -- Φ(1) > 0
  have hOne : 0 < Φ 1 := by have := hStrictMono (by omega : (0:ℤ) < 1); rw [hZero] at this; exact this
  -- Φ(-1) < 0
  have hNegOne : Φ (-1) + Φ 1 = 0 := by rw [← hAdditive (-1) 1]; simp only [neg_add_cancel, hZero]
  show Φ (-1) < 0; linarith

/-- **Corollary**: Applying `holder_not_anom` to ℤ produces an embedding with negative values.

This combines:
1. `MultiplicativeInt.no_anomalous_pair` — ℤ has no anomalous pairs
2. `holder_embedding_produces_negatives` — applies `holder_not_anom` and shows Φ(-1) < 0 -/
theorem Int.holder_embedding_has_negatives :
    ∃ (G : Subsemigroup (Multiplicative ℝ)) (Θ : Multiplicative ℤ ≃*o G),
      Multiplicative.toAdd (Θ (Multiplicative.ofAdd (-1)) : Multiplicative ℝ) < 0 :=
  holder_embedding_produces_negatives MultiplicativeInt.no_anomalous_pair

/-! ## Summary

**What we proved:**
1. ℤ is a valid `KSSemigroupBase` — satisfies K&S semigroup axioms
2. ℤ cannot satisfy `ident_le` — no identity-as-minimum
3. ℤ has no anomalous pairs — Hölder/Alimov theorem applies
4. The Hölder embedding has Φ(-1) < 0 — positivity fails

**The key insight:**
K&S's positivity comes from `ident_le : ∀ x, ident ≤ x`, NOT from the representation
theorem. The Hölder path works perfectly for ℤ but produces negative values. -/

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples
