import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mettapedia.Logic.SolomonoffPrior
import Mettapedia.Logic.UniversalPrediction

/-!
# Optimal Weights (Coding-Theorem Utilities)

This file contains low-level utilities used to formalize the “optimal choice of weights”
discussion in Hutter (2005) §3.6.4 (Theorem 3.70), relating arbitrary weight functions
`v : BinString → ENNReal` with `∑' x, v x ≤ 1` to the universal prefix-free weights
`x ↦ 2^{-Kpf[U](x)}`.

The main proof is carried out in `Mettapedia/Logic/UniversalPrediction/Optimality.lean`; this
file provides reusable dyadic / encoding lemmas to keep that file from ballooning further.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical BigOperators

open Mettapedia.Logic.SolomonoffPrior

/-! ## Fixed-length binary encodings -/

/-- Fixed-length big-endian binary encoding of `k` in `L` bits.

Intended for use under the side-condition `k < 2^L`. -/
def natToBinLen : ℕ → ℕ → BinString
  | 0, _ => []
  | L + 1, k =>
      let pow : ℕ := 2 ^ L
      let msb : ℕ := k / pow
      let rest : ℕ := k % pow
      (decide (msb = 1)) :: natToBinLen L rest

@[simp] theorem length_natToBinLen (L k : ℕ) : (natToBinLen L k).length = L := by
  induction L generalizing k with
  | zero => simp [natToBinLen]
  | succ L ih => simp [natToBinLen, ih]

private lemma binToReal_cons (b : Bool) (s : BinString) :
    binToReal (b :: s) = binToReal s / 2 + (if b then (1 : ℝ) / 2 else 0) := by
  simp [binToReal]

/-- `natToBinLen` represents dyadic rationals:
`binToReal (natToBinLen L k) = k / 2^L` when `k < 2^L`. -/
theorem binToReal_natToBinLen_of_lt {L k : ℕ} (hk : k < 2 ^ L) :
    binToReal (natToBinLen L k) = (k : ℝ) / (2 : ℝ) ^ L := by
  induction L generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst this
      simp [natToBinLen, binToReal]
  | succ L ih =>
      let pow : ℕ := 2 ^ L
      have hpow_pos : 0 < pow := by
        exact pow_pos (by decide : (0 : ℕ) < 2) L
      have hk' : k < pow * 2 := by
        -- `2^(L+1) = 2 * 2^L`
        simpa [pow, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hk
      have hmsb_le : k / pow ≤ 1 := by
        have : k / pow < 2 := Nat.div_lt_of_lt_mul (by simpa [pow] using hk')
        omega
      have hrest_lt : k % pow < pow := Nat.mod_lt _ hpow_pos
      have hk_rest : k % pow < 2 ^ L := by simpa [pow] using hrest_lt
      have hdiv_add_mod : k = (k / pow) * pow + k % pow := by
        simpa [pow, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.div_add_mod k pow).symm
      have htail :
          binToReal (natToBinLen L (k % pow)) = ((k % pow : ℕ) : ℝ) / (2 : ℝ) ^ L :=
        ih (k := k % pow) hk_rest
      have hmsb_cases : k / pow = 0 ∨ k / pow = 1 :=
        (Nat.le_one_iff_eq_zero_or_eq_one.mp hmsb_le)
      have hmsb_term :
          (if decide (k / pow = 1) then (1 : ℝ) / 2 else 0) =
            ((k / pow : ℕ) : ℝ) / 2 := by
        rcases hmsb_cases with h0 | h1
        · -- `k / pow = 0`
          simp [h0]
        · -- `k / pow = 1`
          simp [h1]
      calc
        binToReal (natToBinLen (L + 1) k)
            = binToReal (natToBinLen L (k % pow)) / 2 +
                (if decide (k / pow = 1) then (1 : ℝ) / 2 else 0) := by
                  simp [natToBinLen, pow, binToReal_cons]
        _ = (((k % pow : ℕ) : ℝ) / (2 : ℝ) ^ L) / 2 + ((k / pow : ℕ) : ℝ) / 2 := by
              -- Rewrite the tail via IH, and the MSB term via `hmsb_term`.
              calc
                binToReal (natToBinLen L (k % pow)) / 2 +
                    (if decide (k / pow = 1) then (1 : ℝ) / 2 else 0)
                    =
                    (binToReal (natToBinLen L (k % pow)) / 2) + ((k / pow : ℕ) : ℝ) / 2 := by
                      simpa [add_comm, add_left_comm, add_assoc] using congrArg
                        (fun t => binToReal (natToBinLen L (k % pow)) / 2 + t) hmsb_term
                _ = (((k % pow : ℕ) : ℝ) / (2 : ℝ) ^ L) / 2 + ((k / pow : ℕ) : ℝ) / 2 := by
                      simp [htail]
        _ = (((k / pow : ℕ) : ℝ) * (2 : ℝ) ^ L + ((k % pow : ℕ) : ℝ)) / (2 : ℝ) ^ (L + 1) := by
              field_simp [pow_succ]
              ring
        _ = (k : ℝ) / (2 : ℝ) ^ (L + 1) := by
              have hpow' : (pow : ℝ) = (2 : ℝ) ^ L := by simp [pow]
              have : (k : ℝ) = ((k / pow : ℕ) : ℝ) * (2 : ℝ) ^ L + ((k % pow : ℕ) : ℝ) := by
                have := congrArg (fun n : ℕ => (n : ℝ)) hdiv_add_mod
                simpa [Nat.cast_add, Nat.cast_mul, hpow'] using this
              simpa using congrArg (fun t => t / (2 : ℝ) ^ (L + 1)) this.symm

/-! ## Encoding helpers -/

/-- Helper: extend a function on an encodable type to `ℕ` using `encode`, mapping everything else
to a default value. -/
noncomputable def extendEncode {α : Type*} [Encodable α] (f : α → ENNReal) : ℕ → ENNReal :=
  Function.extend (fun a : α => Encodable.encode a) f 0

@[simp] lemma extendEncode_apply_encode {α : Type*} [Encodable α] (f : α → ENNReal) (a : α) :
    extendEncode f (Encodable.encode a) = f a := by
  classical
  -- `Function.extend` is a left-inverse on the range of an injective map.
  have h :=
    congrArg (fun hfun => hfun a)
      (Function.extend_comp (f := fun x : α => Encodable.encode x)
        (hf := Encodable.encode_injective) (g := f) (e' := (0 : ℕ → ENNReal)))
  -- Expand `extendEncode` and simplify.
  simpa [extendEncode, Function.comp] using h

@[simp] lemma tsum_extendEncode {α : Type*} [Encodable α] (f : α → ENNReal) :
    (∑' n : ℕ, extendEncode f n) = ∑' a : α, f a := by
  classical
  simpa [extendEncode] using
    (tsum_extend_zero (g := fun a : α => Encodable.encode a) (hg := Encodable.encode_injective) (f := f))

/-
## V1–V3 curriculum (Shannon–Fano coding)

We prove a (noncomputable) “coding theorem” style inequality sufficient for Hutter’s Theorem 3.70
in the current development:

V1. Reduce `v : BinString → ENNReal` to a weight function on `ℕ` using `encode`,
    and define prefix sums `pref n`.
V2. For each `x` with `v x ≠ 0`, choose a dyadic interval fully contained in the base interval
    `[pref (encode x), pref (encode x) + v x)`. This gives a prefix-free codeword `p_x`.
V3. Build a prefix-free machine `M_v` that halts exactly on these codewords with output `x`,
    use universality of `U` to relate `Kpf[U](x)` to the code length, and conclude
    `v x ≤ C * 2^{-Kpf[U](x)}` for a uniform constant `C`.

This route does **not** use computability of `v`; it is the cleanest way to close the remaining
`Optimality.lean` stub under our current `UniversalPFM` interface.
-/

open scoped Classical

namespace OptimalWeights

open Mettapedia.Logic.SolomonoffPrior

/-! ### Dyadic interval placement -/

private lemma two_pow_pos (L : ℕ) : (0 : ℝ) < (2 : ℝ) ^ L := by
  exact pow_pos (by norm_num : (0 : ℝ) < 2) L

private lemma two_zpow_neg_pos (L : ℕ) : (0 : ℝ) < (2 : ℝ) ^ (-(L : ℤ)) := by
  have : (0 : ℝ) < (2 : ℝ) := by norm_num
  exact zpow_pos this (-(L : ℤ))

/-- If `2^{-L} < b/2`, then there is a dyadic interval of length `2^{-L}` fully contained in
`[a, a+b)`, provided `0 ≤ a` and `a+b ≤ 1`. -/
private lemma dyadicInterval_natToBinLen_subset_Ico
    {a b : ℝ} (ha : 0 ≤ a) (hab : a + b ≤ 1) {L : ℕ}
    (hL : (2 : ℝ) ^ (-(L : ℤ)) < b / 2) :
    ∃ k : ℕ, k < 2 ^ L ∧
      dyadicInterval (natToBinLen L k) ⊆ Set.Ico a (a + b) := by
  classical
  have hb_pos : 0 < b := by
    -- `b/2 > 0` from `2^{-L} > 0` and `2^{-L} < b/2`.
    have hpos : 0 < b / 2 := lt_of_lt_of_le (two_zpow_neg_pos L) hL.le
    linarith
  -- Choose the dyadic point `k/2^L` just above `a`.
  let powR : ℝ := (2 : ℝ) ^ L
  have hpowR_pos : 0 < powR := two_pow_pos L
  let k : ℕ := Nat.ceil (a * powR)
  have hk_lower : a ≤ (k : ℝ) / powR := by
    -- `a * powR ≤ k` by `le_ceil`, then divide by `powR`.
    have : a * powR ≤ (k : ℝ) := by
      simpa [k] using (Nat.le_ceil (a * powR))
    have hpowR_ne0 : powR ≠ 0 := by exact ne_of_gt hpowR_pos
    -- divide both sides by `powR` using multiplication by `powR⁻¹`.
    have hk' : a * powR * powR⁻¹ ≤ (k : ℝ) * powR⁻¹ := by
      exact mul_le_mul_of_nonneg_right this (inv_nonneg.2 hpowR_pos.le)
    simpa [powR, div_eq_mul_inv, mul_assoc, hpowR_ne0] using hk'
  have hk_upper_lt : (k : ℝ) / powR + (2 : ℝ) ^ (-(L : ℤ)) < a + b := by
    -- `k < a*powR + 1` (ceil_lt_add_one) gives `k/powR < a + 1/powR = a + 2^{-L}`.
    have hk_lt : (k : ℝ) < a * powR + 1 := by
      simpa [k] using
        (Nat.ceil_lt_add_one (a := a * powR) (ha := mul_nonneg ha hpowR_pos.le))
    have hpowR_ne0 : powR ≠ 0 := by exact ne_of_gt hpowR_pos
    have hk_div_lt : (k : ℝ) / powR < a + 1 / powR := by
      have hk' : (k : ℝ) * powR⁻¹ < (a * powR + 1) * powR⁻¹ := by
        exact mul_lt_mul_of_pos_right hk_lt (inv_pos.2 hpowR_pos)
      have : (a * powR + 1) * powR⁻¹ = a + 1 / powR := by
        field_simp [hpowR_ne0]
      simpa [powR, div_eq_mul_inv, this, hpowR_ne0] using hk'
    -- Convert `1/powR` to `2^{-L}`.
    have h_inv_pow : (1 : ℝ) / powR = (2 : ℝ) ^ (-(L : ℤ)) := by
      -- `powR = 2^L`, so `1/powR = 2^{-L}`.
      simp [powR, zpow_neg, zpow_natCast, div_eq_mul_inv]
    -- Now add another `2^{-L}` and use `2^{-L} < b/2`.
    have h2lt : (2 : ℝ) ^ (-(L : ℤ)) + (2 : ℝ) ^ (-(L : ℤ)) < b := by
      -- from `2^{-L} < b/2`
      linarith [hL]
    calc
      (k : ℝ) / powR + (2 : ℝ) ^ (-(L : ℤ))
          < (a + 1 / powR) + (2 : ℝ) ^ (-(L : ℤ)) := by
              linarith [hk_div_lt]
      _ = a + ((1 : ℝ) / powR + (2 : ℝ) ^ (-(L : ℤ))) := by ring
      _ = a + ((2 : ℝ) ^ (-(L : ℤ)) + (2 : ℝ) ^ (-(L : ℤ))) := by
              simp [h_inv_pow]
      _ < a + b := by linarith [h2lt]
  -- Show `k < 2^L` so `natToBinLen` represents `k/2^L`.
  have hk_lt_pow : k < 2 ^ L := by
    -- `2 * 2^{-L} < b`
    have h2pow_lt_b : (2 : ℝ) ^ (-(L : ℤ)) * 2 < b := by linarith [hL]
    -- `a ≤ 1 - b`, hence `a < 1 - 2 * 2^{-L}`
    have ha_le : a ≤ 1 - b := by linarith [hab]
    have ha_lt : a < 1 - (2 : ℝ) ^ (-(L : ℤ)) * 2 := by
      have : 1 - b < 1 - (2 : ℝ) ^ (-(L : ℤ)) * 2 := by linarith [h2pow_lt_b]
      exact lt_of_le_of_lt ha_le this
    -- Multiply by `2^L` and simplify `2^{-L} * 2^L = 1`.
    have hpowR_ne0 : powR ≠ 0 := by exact ne_of_gt hpowR_pos
    have ha_mul_le : a * powR ≤ powR - 2 := by
      have ha_mul_lt : a * powR < (1 - (2 : ℝ) ^ (-(L : ℤ)) * 2) * powR := by
        exact mul_lt_mul_of_pos_right ha_lt hpowR_pos
      have hz : (2 : ℝ) ^ (-(L : ℤ)) * powR = 1 := by
        -- `2^{-L} * 2^L = 1`
        have hpowR_ne0 : (2 : ℝ) ^ L ≠ 0 := by
          exact pow_ne_zero _ (by norm_num)
        -- `simp` turns `2^{-L}` into `(2^L)⁻¹` and cancels with `2^L`.
        simp [powR, zpow_neg, zpow_natCast, hpowR_ne0]
      have hz' : ((2 : ℝ) ^ L)⁻¹ * powR = 1 := by
        have h2pow_ne0 : (2 : ℝ) ^ L ≠ 0 := by
          exact pow_ne_zero _ (by norm_num)
        simp [powR, h2pow_ne0]
      have : (1 - (2 : ℝ) ^ (-(L : ℤ)) * 2) * powR = powR - 2 := by
        calc
          (1 - (2 : ℝ) ^ (-(L : ℤ)) * 2) * powR
              = powR - ((2 : ℝ) ^ (-(L : ℤ)) * 2) * powR := by ring
          _ = powR - 2 * (((2 : ℝ) ^ L)⁻¹ * powR) := by
                -- normalize `2^{-L}` to `(2^L)⁻¹` for `simp`.
                simp [powR, zpow_neg, zpow_natCast, mul_comm]
          _ = powR - 2 := by simp [hz']
      have ha_mul_lt' : a * powR < powR - 2 := by
        -- `ha_mul_lt` is `a * powR < (1 - 2^{-L} * 2) * powR`.
        -- Rewrite the RHS via the computed identity.
        exact lt_of_lt_of_eq ha_mul_lt this
      exact le_of_lt ha_mul_lt'
    -- Use `Nat.ceil_le` to bound `k` by `2^L - 1`.
    have hk_le : k ≤ 2 ^ L - 1 := by
      -- `a * powR ≤ (2^L - 1 : ℝ)`
      have hcast : a * powR ≤ ((2 ^ L - 1 : ℕ) : ℝ) := by
        have : a * powR ≤ powR - 1 := by linarith [ha_mul_le]
        -- rewrite `powR - 1` as `(2^L - 1 : ℕ)` cast
        have hpos : (1 : ℕ) ≤ 2 ^ L := by
          exact Nat.one_le_pow _ _ (by decide : (1 : ℕ) ≤ 2)
        have : a * powR ≤ ((2 ^ L : ℕ) : ℝ) - 1 := by
          simpa [powR, (by norm_cast : ((2 : ℝ) ^ L) = (2 ^ L : ℝ))] using this
        -- `(2^L : ℝ) - 1 = ((2^L - 1 : ℕ) : ℝ)`
        simpa [Nat.cast_sub hpos] using this
      -- `ceil(a*powR) ≤ 2^L - 1`
      have : Nat.ceil (a * powR) ≤ 2 ^ L - 1 := (Nat.ceil_le).2 hcast
      simpa [k] using this
    have hlt : 2 ^ L - 1 < 2 ^ L :=
      Nat.sub_lt (Nat.pow_pos (a := 2) (n := L) (by decide : (0 : ℕ) < 2)) (by decide)
    exact lt_of_le_of_lt hk_le hlt
  refine ⟨k, ⟨hk_lt_pow, ?_⟩⟩
  intro y hy
  -- Unfold dyadic interval and use the bounds on endpoints.
  have hk_real :
      binToReal (natToBinLen L k) = (k : ℝ) / (2 : ℝ) ^ L := by
    simpa using binToReal_natToBinLen_of_lt (L := L) (k := k) hk_lt_pow
  have hlen : (natToBinLen L k).length = L := by simp
  unfold dyadicInterval at hy
  rcases hy with ⟨hyL, hyR⟩
  -- lower bound
  have hy_ge_a : a ≤ y := by
    have : (k : ℝ) / (2 : ℝ) ^ L ≤ y := by
      simpa [hk_real] using hyL
    exact le_trans hk_lower this
  -- upper bound
  have hy_lt_ab : y < a + b := by
    have : y < (k : ℝ) / (2 : ℝ) ^ L + (2 : ℝ) ^ (-(L : ℤ)) := by
      simpa [hk_real, hlen] using hyR
    exact lt_of_lt_of_le this hk_upper_lt.le
  exact ⟨hy_ge_a, by simpa [add_assoc] using hy_lt_ab⟩

/-
### V1: `v` on `BinString` → `vNat` on `ℕ`, and prefix sums
-/

variable (v : BinString → ENNReal)

private noncomputable def vNat : ℕ → ENNReal :=
  extendEncode v

private noncomputable def pref (n : ℕ) : ENNReal :=
  (Finset.range n).sum (fun i => vNat v i)

@[simp] private lemma pref_zero : pref v 0 = 0 := by
  simp [pref]

private lemma pref_succ (n : ℕ) : pref v (n + 1) = pref v n + vNat v n := by
  simp [pref, Finset.sum_range_succ]

private lemma pref_le_tsum (n : ℕ) : pref v n ≤ ∑' i : ℕ, vNat v i := by
  simpa [pref] using (ENNReal.sum_le_tsum (s := Finset.range n) (f := vNat v))

private lemma tsum_vNat_eq (v : BinString → ENNReal) :
    (∑' i : ℕ, vNat v i) = ∑' x : BinString, v x := by
  simp [vNat]

private lemma pref_le_one (hv_sum : (∑' x : BinString, v x) ≤ 1) (n : ℕ) : pref v n ≤ 1 := by
  have : (∑' i : ℕ, vNat v i) ≤ 1 := by
    simpa [tsum_vNat_eq (v := v)] using hv_sum
  exact (pref_le_tsum (v := v) n).trans this

/-!
### V3: Main coding lemma for Theorem 3.70 (in the current machine model)

This is the lemma we will use to discharge the remaining `Optimality.lean` stub.
-/

/-- **V2** (Shannon–Fano style code, without universality).

Given `v : BinString → ENNReal` with `∑' v ≤ 1`, we can (noncomputably) build a prefix-free machine
`Mv` and a chosen codeword `code x` such that:

* `Mv.compute (code x) = some x` for all `x` with `v x ≠ 0`;
* `v x ≤ 4 * 2^{-|code x|}` for all `x`.

This is the “dyadic interval inside base interval” step (V2) packaged as a reusable lemma; V3 then
composes it with universality of `U` to get the `kpfWeight` bound. -/
theorem exists_prefixFreeMachine_const_mul_pow2_len
    (v : BinString → ENNReal) (hv_sum : (∑' x : BinString, v x) ≤ 1) :
    ∃ (Mv : PrefixFreeMachine) (code : BinString → BinString),
      (∀ x : BinString, v x ≠ 0 → Mv.compute (code x) = some x) ∧
        ∀ x : BinString, v x ≤ (4 : ENNReal) * (2 : ENNReal) ^ (-(code x).length : ℤ) := by
  classical
  -- V1: pointwise finiteness follows from `∑' v ≤ 1`.
  have v_le_one : ∀ x : BinString, v x ≤ 1 := by
    intro x
    have hx : v x ≤ ∑' y : BinString, v y := by
      simpa using (ENNReal.le_tsum (f := v) x)
    exact hx.trans hv_sum
  have v_ne_top : ∀ x : BinString, v x ≠ (⊤ : ENNReal) := by
    intro x
    have : v x < (⊤ : ENNReal) := lt_of_le_of_lt (v_le_one x) (by simp)
    exact ne_of_lt this

  -- V1: prefix sums are monotone.
  have pref_mono : ∀ {m n : ℕ}, m ≤ n → pref v m ≤ pref v n := by
    intro m n hmn
    have hsub : Finset.range m ⊆ Finset.range n := Finset.range_mono hmn
    have hnonneg : ∀ i, 0 ≤ vNat v i := by intro i; exact zero_le _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro i _ _; exact hnonneg i)
    simpa [pref] using this

  -- Base interval for a string `x`: `[pref n, pref n + v x)` where `n = encode x`.
  let baseLeft (x : BinString) : ℝ := (pref v (Encodable.encode x)).toReal
  let baseWidth (x : BinString) : ℝ := (v x).toReal
  let baseInterval (x : BinString) : Set ℝ := Set.Ico (baseLeft x) (baseLeft x + baseWidth x)

  have vNat_encode (x : BinString) : vNat v (Encodable.encode x) = v x := by
    dsimp [vNat]
    exact extendEncode_apply_encode (f := v) x

  have baseLeft_add_width_eq (x : BinString) :
      baseLeft x + baseWidth x = (pref v (Encodable.encode x + 1)).toReal := by
    classical
    let n : ℕ := Encodable.encode x
    have htop_left : pref v n ≠ (⊤ : ENNReal) := by
      exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum n) (by simp))
    have htoReal_add :
        (pref v n + v x).toReal = (pref v n).toReal + (v x).toReal := by
      simpa using ENNReal.toReal_add htop_left (v_ne_top x)
    have htoReal_add' :
        (pref v n).toReal + (v x).toReal = (pref v n + v x).toReal := by
      simpa using htoReal_add.symm
    have hvNat : vNat v n = v x := by
      simpa [n] using vNat_encode x
    have hsum : pref v (n + 1) = pref v n + v x := by
      simp [pref_succ (v := v) n, hvNat]
    calc
      baseLeft x + baseWidth x
          = (pref v n).toReal + (v x).toReal := by
              simp [baseLeft, baseWidth, n]
      _ = (pref v n + v x).toReal := htoReal_add'
      _ = (pref v (n + 1)).toReal := by simp [hsum]
      _ = (pref v (Encodable.encode x + 1)).toReal := by simp [n]

  have baseLeft_nonneg (x : BinString) : 0 ≤ baseLeft x := by
    exact ENNReal.toReal_nonneg

  have baseInterval_le_one (x : BinString) : baseLeft x + baseWidth x ≤ 1 := by
    have hpref : pref v (Encodable.encode x + 1) ≤ 1 :=
      pref_le_one (v := v) hv_sum (Encodable.encode x + 1)
    have : (pref v (Encodable.encode x + 1)).toReal ≤ 1 := by
      have htop : pref v (Encodable.encode x + 1) ≠ (⊤ : ENNReal) :=
        ne_of_lt (lt_of_le_of_lt hpref (by simp))
      have : (pref v (Encodable.encode x + 1)).toReal ≤ (1 : ENNReal).toReal :=
        ENNReal.toReal_mono (by simp) hpref
      simpa using this
    simpa [baseLeft_add_width_eq (x := x)] using this

  have LExist (x : BinString) (hx0 : v x ≠ 0) :
      ∃ L : ℕ, (2 : ℝ) ^ (-(L : ℤ)) < baseWidth x / 2 := by
    have hb_pos : 0 < baseWidth x := by
      have : 0 < (v x).toReal := ENNReal.toReal_pos hx0 (v_ne_top x)
      simpa [baseWidth] using this
    have hb2_pos : 0 < baseWidth x / 2 := by linarith [hb_pos]
    obtain ⟨L, hL⟩ : ∃ L : ℕ, ((1 / 2 : ℝ) ^ L) < baseWidth x / 2 :=
      exists_pow_lt_of_lt_one hb2_pos (by norm_num)
    refine ⟨L, ?_⟩
    simpa using hL

  let L_of (x : BinString) : ℕ :=
    if hx0 : v x = 0 then 0 else Nat.find (LExist x hx0)

  have L_of_spec (x : BinString) (hx0 : v x ≠ 0) :
      (2 : ℝ) ^ (-(L_of x : ℤ)) < baseWidth x / 2 := by
    simpa [L_of, hx0] using (Nat.find_spec (LExist x hx0))

  have kExist (x : BinString) (hx0 : v x ≠ 0) :
      ∃ k : ℕ, k < 2 ^ L_of x ∧ dyadicInterval (natToBinLen (L_of x) k) ⊆ baseInterval x := by
    have ha : 0 ≤ baseLeft x := baseLeft_nonneg x
    have hab : baseLeft x + baseWidth x ≤ 1 := baseInterval_le_one x
    have hL : (2 : ℝ) ^ (-(L_of x : ℤ)) < baseWidth x / 2 := L_of_spec x hx0
    simpa [baseInterval] using
      (dyadicInterval_natToBinLen_subset_Ico (a := baseLeft x) (b := baseWidth x) ha hab (L := L_of x) hL)

  let code : BinString → BinString :=
    fun x =>
      if hx0 : v x = 0 then [] else
        natToBinLen (L_of x) (Classical.choose (kExist x hx0))

  -- `code x` sits inside `baseInterval x`, and its length is chosen so that `v x ≤ 4 * 2^{-|code x|}`.
  have code_spec :
      ∀ x : BinString, v x ≠ 0 →
        dyadicInterval (code x) ⊆ baseInterval x ∧
          baseWidth x ≤ 4 * (2 : ℝ) ^ (-(code x).length : ℤ) := by
    intro x hx0
    have hk := Classical.choose_spec (kExist x hx0)
    have hcode : code x = natToBinLen (L_of x) (Classical.choose (kExist x hx0)) := by
      simp [code, hx0]
    have hsubset : dyadicInterval (code x) ⊆ baseInterval x := by
      simpa [hcode] using hk.2
    have hlen : (code x).length = L_of x := by
      simp [hcode]
    -- Bound `baseWidth x` by `4 * 2^{-L_of x}` using minimality of `Nat.find`.
    have hb_le_one : baseWidth x ≤ 1 := by
      have : (v x).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) (v_le_one x)
      simpa [baseWidth] using this
    have hL : (2 : ℝ) ^ (-(L_of x : ℤ)) < baseWidth x / 2 := L_of_spec x hx0
    have hLpos : 0 < L_of x := by
      by_contra h0
      have hL0 : L_of x = 0 := Nat.eq_zero_of_not_pos h0
      have : (1 : ℝ) < baseWidth x / 2 := by simpa [hL0] using hL
      linarith [hb_le_one, this]
    have hmin :
        ¬ (2 : ℝ) ^ (-((L_of x - 1 : ℕ) : ℤ)) < baseWidth x / 2 := by
      have hlt : L_of x - 1 < L_of x := Nat.pred_lt (Nat.ne_zero_of_lt hLpos)
      -- `L_of x = Nat.find (LExist x hx0)` in the nonzero case.
      have hlt' : L_of x - 1 < Nat.find (LExist x hx0) := by
        simpa [L_of, hx0] using hlt
      -- `Nat.find_min` gives minimality of the chosen `L_of`.
      simpa [L_of, hx0] using (Nat.find_min (LExist x hx0) hlt')
    have hbge : baseWidth x / 2 ≤ (2 : ℝ) ^ (-((L_of x - 1 : ℕ) : ℤ)) := le_of_not_gt hmin
    have hzpow :
        (2 : ℝ) ^ (-((L_of x - 1 : ℕ) : ℤ)) = (2 : ℝ) * (2 : ℝ) ^ (-(L_of x : ℤ)) := by
      have h2ne0 : (2 : ℝ) ≠ 0 := by norm_num
      have hExp : (-((L_of x - 1 : ℕ) : ℤ)) = (-(L_of x : ℤ)) + 1 := by
        have h1 : (1 : ℕ) ≤ L_of x := Nat.succ_le_iff.2 hLpos
        have hsub : ((L_of x - 1 : ℕ) : ℤ) = (L_of x : ℤ) - 1 := by
          simpa using (Int.ofNat_sub h1)
        -- `-(L-1) = -L + 1` in `ℤ`.
        calc
          -((L_of x - 1 : ℕ) : ℤ) = -((L_of x : ℤ) - 1) := by simp [hsub]
          _ = (-(L_of x : ℤ)) + 1 := by ring
      calc
        (2 : ℝ) ^ (-((L_of x - 1 : ℕ) : ℤ)) = (2 : ℝ) ^ ((-(L_of x : ℤ)) + 1) := by
          simp [hExp]
        _ = (2 : ℝ) ^ (-(L_of x : ℤ)) * (2 : ℝ) ^ (1 : ℤ) := by
          simp [zpow_add₀, h2ne0]
        _ = (2 : ℝ) * (2 : ℝ) ^ (-(L_of x : ℤ)) := by ring_nf
    have hb_le : baseWidth x ≤ 4 * (2 : ℝ) ^ (-(L_of x : ℤ)) := by
      -- from `b/2 ≤ 2^{-(L-1)} = 2 * 2^{-L}`
      have : baseWidth x / 2 ≤ 2 * (2 : ℝ) ^ (-(L_of x : ℤ)) := by
        simpa [hzpow, mul_assoc, mul_left_comm, mul_comm] using hbge
      linarith
    refine ⟨hsubset, ?_⟩
    simpa [hlen] using hb_le

  -- Build a prefix-free machine that halts on the chosen codes.
  let Mv : PrefixFreeMachine :=
    { compute := fun p =>
        if h : ∃ x : BinString, v x ≠ 0 ∧ code x = p then some (Classical.choose h) else none
      prefix_free := by
        intro p q hpq hpne hp
        classical
        -- If `p` halts, it is `code x` for some `x`. Any strict extension would force
        -- overlap of dyadic intervals, contradicting disjointness of base intervals.
        by_contra hq
        have hp' : ∃ x : BinString, v x ≠ 0 ∧ code x = p := by
          simpa using hp
        have hq' : ∃ y : BinString, v y ≠ 0 ∧ code y = q := by
          classical
          by_cases h : ∃ y : BinString, v y ≠ 0 ∧ code y = q
          · exact h
          · exfalso
            -- If there is no witness, `compute q = none`, contradicting `hq : compute q ≠ none`.
            apply hq
            simp [h]
        rcases hp' with ⟨x, hx0, rfl⟩
        rcases hq' with ⟨y, hy0, rfl⟩
        -- prefix implies interval nesting
        have hsub : dyadicInterval (code y) ⊆ dyadicInterval (code x) :=
          prefix_implies_interval_subset _ _ hpq
        -- `dyadicInterval (code y)` is nonempty (contains its left endpoint)
        have hy_nonempty : (dyadicInterval (code y)).Nonempty := by
          refine ⟨binToReal (code y), ?_⟩
          unfold dyadicInterval
          constructor
          · exact le_rfl
          ·
            have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
            have : (0 : ℝ) < (2 : ℝ) ^ (-(code y).length : ℤ) := by
              exact zpow_pos h2pos (-(code y).length : ℤ)
            linarith
        -- But then `dyadicInterval (code y)` is contained in both base intervals; this forces `x = y`,
        -- contradicting strict prefix.
        have hxI := (code_spec x hx0).1
        have hyI := (code_spec y hy0).1
        have hy_in_x : dyadicInterval (code y) ⊆ baseInterval x := hsub.trans hxI
        rcases hy_nonempty with ⟨t, ht⟩
        have ht_x : t ∈ baseInterval x := hy_in_x (by simpa using ht)
        have ht_y : t ∈ baseInterval y := hyI (by simpa using ht)
        have hn : Encodable.encode x = Encodable.encode y := by
          by_contra hne
          cases lt_or_gt_of_ne hne with
          | inl hlt =>
              have hmono :
                  pref v (Encodable.encode x + 1) ≤ pref v (Encodable.encode y) :=
                pref_mono (m := Encodable.encode x + 1) (n := Encodable.encode y) (Nat.succ_le_iff.2 hlt)
              have htop1 : pref v (Encodable.encode x + 1) ≠ (⊤ : ENNReal) := by
                exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode x + 1)) (by simp))
              have htop2 : pref v (Encodable.encode y) ≠ (⊤ : ENNReal) := by
                exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode y)) (by simp))
              have hx_toReal :
                  (pref v (Encodable.encode x + 1)).toReal ≤ (pref v (Encodable.encode y)).toReal :=
                (ENNReal.toReal_le_toReal htop1 htop2).2 hmono
              have hRight : baseLeft x + baseWidth x = (pref v (Encodable.encode x + 1)).toReal :=
                baseLeft_add_width_eq (x := x)
              have hLeft : baseLeft y = (pref v (Encodable.encode y)).toReal := by
                simp [baseLeft]
              have hle : baseLeft x + baseWidth x ≤ baseLeft y := by
                linarith [hx_toReal, hRight, hLeft]
              have hdisj : Disjoint (baseInterval y) (baseInterval x) := by
                refine Set.disjoint_left.mpr ?_
                intro t ht_y ht_x
                have : baseLeft x + baseWidth x ≤ t := le_trans hle ht_y.1
                exact (not_le_of_gt ht_x.2) this
              exact (Set.disjoint_left.mp hdisj ht_y) ht_x
          | inr hgt =>
              have hmono :
                  pref v (Encodable.encode y + 1) ≤ pref v (Encodable.encode x) :=
                pref_mono (m := Encodable.encode y + 1) (n := Encodable.encode x) (Nat.succ_le_iff.2 hgt)
              have htop1 : pref v (Encodable.encode y + 1) ≠ (⊤ : ENNReal) := by
                exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode y + 1)) (by simp))
              have htop2 : pref v (Encodable.encode x) ≠ (⊤ : ENNReal) := by
                exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode x)) (by simp))
              have hy_toReal :
                  (pref v (Encodable.encode y + 1)).toReal ≤ (pref v (Encodable.encode x)).toReal :=
                (ENNReal.toReal_le_toReal htop1 htop2).2 hmono
              have hRight : baseLeft y + baseWidth y = (pref v (Encodable.encode y + 1)).toReal :=
                baseLeft_add_width_eq (x := y)
              have hLeft : baseLeft x = (pref v (Encodable.encode x)).toReal := by
                simp [baseLeft]
              have hle : baseLeft y + baseWidth y ≤ baseLeft x := by
                linarith [hy_toReal, hRight, hLeft]
              have hdisj : Disjoint (baseInterval x) (baseInterval y) := by
                refine Set.disjoint_left.mpr ?_
                intro t ht_x ht_y
                have : baseLeft y + baseWidth y ≤ t := le_trans hle ht_x.1
                exact (not_le_of_gt ht_y.2) this
              exact (Set.disjoint_left.mp hdisj ht_x) ht_y
        have hxy : x = y := Encodable.encode_injective hn
        subst hxy
        exact hpne rfl }

  have hhalt_code : ∀ x : BinString, v x ≠ 0 → Mv.compute (code x) = some x := by
    intro x hx0
    -- This follows from injectivity of codes; `Mv.compute` selects the unique `x` for its code.
    classical
    -- We use the witness `x` itself.
    have h : ∃ y : BinString, v y ≠ 0 ∧ code y = code x := ⟨x, hx0, rfl⟩
    have hy : v (Classical.choose h) ≠ 0 ∧ code (Classical.choose h) = code x :=
      Classical.choose_spec h
    -- If `code (choose h) = code x`, then (by base interval disjointness) `choose h = x`.
    have hchoose : Classical.choose h = x := by
      -- `dyadicInterval (code x)` is nonempty, so it cannot lie in two disjoint base intervals.
      have hxI := (code_spec x hx0).1
      have hyI := (code_spec (Classical.choose h) hy.1).1
      have hnonempty : (dyadicInterval (code x)).Nonempty := by
        refine ⟨binToReal (code x), ?_⟩
        unfold dyadicInterval
        constructor
        · exact le_rfl
        ·
          have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
          have : (0 : ℝ) < (2 : ℝ) ^ (-(code x).length : ℤ) := by
            exact zpow_pos h2pos (-(code x).length : ℤ)
          linarith
      rcases hnonempty with ⟨t, ht⟩
      have ht_x : t ∈ baseInterval x := hxI (by simpa using ht)
      have ht_y : t ∈ baseInterval (Classical.choose h) := by
        -- use `hy.2` to rewrite
        have : dyadicInterval (code x) ⊆ dyadicInterval (code (Classical.choose h)) := by
          simp [hy.2]
        exact hyI (by simpa [hy.2] using ht)
      have hn : Encodable.encode (Classical.choose h) = Encodable.encode x := by
        -- if unequal, base intervals would be disjoint, contradicting `t ∈ ⋂`.
        by_contra hne
        cases lt_or_gt_of_ne hne with
        | inl hlt =>
            have hmono :
                pref v (Encodable.encode (Classical.choose h) + 1) ≤ pref v (Encodable.encode x) :=
              pref_mono (m := Encodable.encode (Classical.choose h) + 1) (n := Encodable.encode x)
                (Nat.succ_le_iff.2 hlt)
            have htop1 : pref v (Encodable.encode (Classical.choose h) + 1) ≠ (⊤ : ENNReal) := by
              exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode (Classical.choose h) + 1))
                (by simp))
            have htop2 : pref v (Encodable.encode x) ≠ (⊤ : ENNReal) := by
              exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode x)) (by simp))
            have hx_toReal :
                (pref v (Encodable.encode (Classical.choose h) + 1)).toReal ≤ (pref v (Encodable.encode x)).toReal :=
              (ENNReal.toReal_le_toReal htop1 htop2).2 hmono
            have hRight : baseLeft (Classical.choose h) + baseWidth (Classical.choose h) =
                (pref v (Encodable.encode (Classical.choose h) + 1)).toReal :=
              baseLeft_add_width_eq (x := Classical.choose h)
            have hLeft : baseLeft x = (pref v (Encodable.encode x)).toReal := by simp [baseLeft]
            have hle : baseLeft (Classical.choose h) + baseWidth (Classical.choose h) ≤ baseLeft x := by
              linarith [hx_toReal, hRight, hLeft]
            have hdisj : Disjoint (baseInterval x) (baseInterval (Classical.choose h)) := by
              refine Set.disjoint_left.mpr ?_
              intro t ht_x' ht_y'
              have : baseLeft (Classical.choose h) + baseWidth (Classical.choose h) ≤ t :=
                le_trans hle ht_x'.1
              exact (not_le_of_gt ht_y'.2) this
            exact (Set.disjoint_left.mp hdisj ht_x) ht_y
        | inr hgt =>
            have hmono :
                pref v (Encodable.encode x + 1) ≤ pref v (Encodable.encode (Classical.choose h)) :=
              pref_mono (m := Encodable.encode x + 1) (n := Encodable.encode (Classical.choose h))
                (Nat.succ_le_iff.2 hgt)
            have htop1 : pref v (Encodable.encode x + 1) ≠ (⊤ : ENNReal) := by
              exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode x + 1)) (by simp))
            have htop2 : pref v (Encodable.encode (Classical.choose h)) ≠ (⊤ : ENNReal) := by
              exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode (Classical.choose h))) (by simp))
            have hx_toReal :
                (pref v (Encodable.encode x + 1)).toReal ≤ (pref v (Encodable.encode (Classical.choose h))).toReal :=
              (ENNReal.toReal_le_toReal htop1 htop2).2 hmono
            have hRight : baseLeft x + baseWidth x = (pref v (Encodable.encode x + 1)).toReal :=
              baseLeft_add_width_eq (x := x)
            have hLeft : baseLeft (Classical.choose h) = (pref v (Encodable.encode (Classical.choose h))).toReal := by
              simp [baseLeft]
            have hle : baseLeft x + baseWidth x ≤ baseLeft (Classical.choose h) := by
              linarith [hx_toReal, hRight, hLeft]
            have hdisj : Disjoint (baseInterval (Classical.choose h)) (baseInterval x) := by
              refine Set.disjoint_left.mpr ?_
              intro t ht_y' ht_x'
              have : baseLeft x + baseWidth x ≤ t := le_trans hle ht_y'.1
              exact (not_le_of_gt ht_x'.2) this
            exact (Set.disjoint_left.mp hdisj ht_y) ht_x
      exact Encodable.encode_injective hn
    -- now compute value
    simp [Mv, h, hchoose]

  have hv_le_code :
      ∀ x : BinString, v x ≤ (4 : ENNReal) * (2 : ENNReal) ^ (-(code x).length : ℤ) := by
    intro x
    by_cases hx0 : v x = 0
    · simp [hx0]
    · have hxI := code_spec x hx0
      have hv_le_real : (v x).toReal ≤ 4 * (2 : ℝ) ^ (-(code x).length : ℤ) := hxI.2
      have htop : v x ≠ (⊤ : ENNReal) := v_ne_top x
      have hv_eq : v x = ENNReal.ofReal (v x).toReal := by
        exact (ENNReal.ofReal_toReal htop).symm
      have h4eq :
          ENNReal.ofReal (4 * (2 : ℝ) ^ (-(code x).length : ℤ)) =
            (4 : ENNReal) * (2 : ENNReal) ^ (-(code x).length : ℤ) := by
        -- `ENNReal` simplifies negative `zpow`s to inverses; normalize with `zpow_neg` first.
        have hz : (2 : ENNReal) ^ (-(code x).length : ℤ) = (2 ^ (code x).length : ENNReal)⁻¹ := by
          simpa [zpow_natCast] using (ENNReal.zpow_neg (2 : ENNReal) ((code x).length : ℤ))
        simp [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), hz]
      have hineq :
          ENNReal.ofReal (v x).toReal ≤ ENNReal.ofReal (4 * (2 : ℝ) ^ (-(code x).length : ℤ)) :=
        ENNReal.ofReal_le_ofReal hv_le_real
      calc
        v x = ENNReal.ofReal (v x).toReal := hv_eq
        _ ≤ ENNReal.ofReal (4 * (2 : ℝ) ^ (-(code x).length : ℤ)) := hineq
        _ = (4 : ENNReal) * (2 : ENNReal) ^ (-(code x).length : ℤ) := h4eq

  refine ⟨Mv, code, hhalt_code, hv_le_code⟩

theorem exists_const_mul_kpfWeight
    (U : PrefixFreeMachine) [UniversalPFM U]
    (v : BinString → ENNReal) (hv_sum : (∑' x : BinString, v x) ≤ 1) :
    ∃ C : ENNReal, C ≠ 0 ∧ ∀ x : BinString, v x ≤ C * kpfWeight (U := U) x := by
  classical
  -- V1: pointwise finiteness follows from `∑' v ≤ 1`.
  have v_le_one : ∀ x : BinString, v x ≤ 1 := by
    intro x
    have hx : v x ≤ ∑' y : BinString, v y := by
      simpa using (ENNReal.le_tsum (f := v) x)
    exact hx.trans hv_sum
  have v_ne_top : ∀ x : BinString, v x ≠ (⊤ : ENNReal) := by
    intro x
    have : v x < (⊤ : ENNReal) := lt_of_le_of_lt (v_le_one x) (by simp)
    exact ne_of_lt this

  -- V1: prefix sums are monotone.
  have pref_mono : ∀ {m n : ℕ}, m ≤ n → pref v m ≤ pref v n := by
    intro m n hmn
    have hsub : Finset.range m ⊆ Finset.range n := Finset.range_mono hmn
    have hnonneg : ∀ i, 0 ≤ vNat v i := by intro i; exact zero_le _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro i _ _; exact hnonneg i)
    simpa [pref] using this

  -- Base interval for a string `x`: `[pref n, pref n + v x)` where `n = encode x`.
  let baseLeft (x : BinString) : ℝ := (pref v (Encodable.encode x)).toReal
  let baseWidth (x : BinString) : ℝ := (v x).toReal
  let baseInterval (x : BinString) : Set ℝ := Set.Ico (baseLeft x) (baseLeft x + baseWidth x)

  -- V2: choose a dyadic interval inside each base interval.

  have vNat_encode (x : BinString) : vNat v (Encodable.encode x) = v x := by
    dsimp [vNat]
    exact extendEncode_apply_encode (f := v) x

  have baseLeft_add_width_eq (x : BinString) :
      baseLeft x + baseWidth x = (pref v (Encodable.encode x + 1)).toReal := by
    classical
    let n : ℕ := Encodable.encode x
    have htop_left : pref v n ≠ (⊤ : ENNReal) := by
      exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum n) (by simp))
    have htoReal_add :
        (pref v n + v x).toReal = (pref v n).toReal + (v x).toReal := by
      simpa using ENNReal.toReal_add htop_left (v_ne_top x)
    have htoReal_add' :
        (pref v n).toReal + (v x).toReal = (pref v n + v x).toReal := by
      simpa using htoReal_add.symm
    have hvNat : vNat v n = v x := by
      simpa [n] using vNat_encode x
    have hsum : pref v (n + 1) = pref v n + v x := by
      simp [pref_succ (v := v) n, hvNat]
    calc
      baseLeft x + baseWidth x
          = (pref v n).toReal + (v x).toReal := by
              simp [baseLeft, baseWidth, n]
      _ = (pref v n + v x).toReal := htoReal_add'
      _ = (pref v (n + 1)).toReal := by simp [hsum]
      _ = (pref v (Encodable.encode x + 1)).toReal := by simp [n]

  have baseLeft_nonneg (x : BinString) : 0 ≤ baseLeft x := by
    exact ENNReal.toReal_nonneg

  have baseInterval_le_one (x : BinString) : baseLeft x + baseWidth x ≤ 1 := by
    have hpref : pref v (Encodable.encode x + 1) ≤ 1 :=
      pref_le_one (v := v) hv_sum (Encodable.encode x + 1)
    have : (pref v (Encodable.encode x + 1)).toReal ≤ 1 := by
      have htop : pref v (Encodable.encode x + 1) ≠ (⊤ : ENNReal) :=
        ne_of_lt (lt_of_le_of_lt hpref (by simp))
      have : (pref v (Encodable.encode x + 1)).toReal ≤ (1 : ENNReal).toReal :=
        ENNReal.toReal_mono (by simp) hpref
      simpa using this
    simpa [baseLeft_add_width_eq (x := x)] using this

  have LExist (x : BinString) (hx0 : v x ≠ 0) :
      ∃ L : ℕ, (2 : ℝ) ^ (-(L : ℤ)) < baseWidth x / 2 := by
    have hb_pos : 0 < baseWidth x := by
      have : 0 < (v x).toReal := ENNReal.toReal_pos hx0 (v_ne_top x)
      simpa [baseWidth] using this
    have hb2_pos : 0 < baseWidth x / 2 := by linarith [hb_pos]
    obtain ⟨L, hL⟩ : ∃ L : ℕ, ((1 / 2 : ℝ) ^ L) < baseWidth x / 2 :=
      exists_pow_lt_of_lt_one hb2_pos (by norm_num)
    refine ⟨L, ?_⟩
    simpa using hL

  let L_of (x : BinString) : ℕ :=
    if hx0 : v x = 0 then 0 else Nat.find (LExist x hx0)

  have L_of_spec (x : BinString) (hx0 : v x ≠ 0) :
      (2 : ℝ) ^ (-(L_of x : ℤ)) < baseWidth x / 2 := by
    simpa [L_of, hx0] using (Nat.find_spec (LExist x hx0))

  have kExist (x : BinString) (hx0 : v x ≠ 0) :
      ∃ k : ℕ, k < 2 ^ L_of x ∧ dyadicInterval (natToBinLen (L_of x) k) ⊆ baseInterval x := by
    have ha : 0 ≤ baseLeft x := baseLeft_nonneg x
    have hab : baseLeft x + baseWidth x ≤ 1 := baseInterval_le_one x
    have hL : (2 : ℝ) ^ (-(L_of x : ℤ)) < baseWidth x / 2 := L_of_spec x hx0
    simpa [baseInterval] using
      (dyadicInterval_natToBinLen_subset_Ico (a := baseLeft x) (b := baseWidth x) ha hab (L := L_of x) hL)

  let code : BinString → BinString :=
    fun x =>
      if hx0 : v x = 0 then [] else
        natToBinLen (L_of x) (Classical.choose (kExist x hx0))

  -- `code x` sits inside `baseInterval x`, and its length is chosen so that `v x ≤ 4 * 2^{-|code x|}`.
  have code_spec :
      ∀ x : BinString, v x ≠ 0 →
        dyadicInterval (code x) ⊆ baseInterval x ∧
          baseWidth x ≤ 4 * (2 : ℝ) ^ (-(code x).length : ℤ) := by
    intro x hx0
    have hk := Classical.choose_spec (kExist x hx0)
    have hcode : code x = natToBinLen (L_of x) (Classical.choose (kExist x hx0)) := by
      simp [code, hx0]
    have hsubset : dyadicInterval (code x) ⊆ baseInterval x := by
      simpa [hcode] using hk.2
    have hlen : (code x).length = L_of x := by
      simp [hcode]
    -- Bound `baseWidth x` by `4 * 2^{-L_of x}` using minimality of `Nat.find`.
    have hb_le_one : baseWidth x ≤ 1 := by
      have : (v x).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) (v_le_one x)
      simpa [baseWidth] using this
    have hL : (2 : ℝ) ^ (-(L_of x : ℤ)) < baseWidth x / 2 := L_of_spec x hx0
    have hLpos : 0 < L_of x := by
      by_contra h0
      have hL0 : L_of x = 0 := Nat.eq_zero_of_not_pos h0
      have : (1 : ℝ) < baseWidth x / 2 := by simpa [hL0] using hL
      linarith [hb_le_one, this]
    have hmin :
        ¬ (2 : ℝ) ^ (-((L_of x - 1 : ℕ) : ℤ)) < baseWidth x / 2 := by
      have hlt : L_of x - 1 < L_of x := Nat.pred_lt (Nat.ne_zero_of_lt hLpos)
      -- `L_of x = Nat.find (LExist x hx0)` in the nonzero case.
      have hlt' : L_of x - 1 < Nat.find (LExist x hx0) := by
        simpa [L_of, hx0] using hlt
      -- `Nat.find_min` gives minimality of the chosen `L_of`.
      simpa [L_of, hx0] using (Nat.find_min (LExist x hx0) hlt')
    have hbge : baseWidth x / 2 ≤ (2 : ℝ) ^ (-((L_of x - 1 : ℕ) : ℤ)) := le_of_not_gt hmin
    have hzpow :
        (2 : ℝ) ^ (-((L_of x - 1 : ℕ) : ℤ)) = (2 : ℝ) * (2 : ℝ) ^ (-(L_of x : ℤ)) := by
      have h2ne0 : (2 : ℝ) ≠ 0 := by norm_num
      have hExp : (-((L_of x - 1 : ℕ) : ℤ)) = (-(L_of x : ℤ)) + 1 := by
        have h1 : (1 : ℕ) ≤ L_of x := Nat.succ_le_iff.2 hLpos
        have hsub : ((L_of x - 1 : ℕ) : ℤ) = (L_of x : ℤ) - 1 := by
          simpa using (Int.ofNat_sub h1)
        -- `-(L-1) = -L + 1` in `ℤ`.
        calc
          -((L_of x - 1 : ℕ) : ℤ) = -((L_of x : ℤ) - 1) := by simp [hsub]
          _ = (-(L_of x : ℤ)) + 1 := by ring
      calc
        (2 : ℝ) ^ (-((L_of x - 1 : ℕ) : ℤ)) = (2 : ℝ) ^ ((-(L_of x : ℤ)) + 1) := by
          simp [hExp]
        _ = (2 : ℝ) ^ (-(L_of x : ℤ)) * (2 : ℝ) ^ (1 : ℤ) := by
          simp [zpow_add₀, h2ne0]
        _ = (2 : ℝ) * (2 : ℝ) ^ (-(L_of x : ℤ)) := by ring_nf
    have hb_le : baseWidth x ≤ 4 * (2 : ℝ) ^ (-(L_of x : ℤ)) := by
      -- from `b/2 ≤ 2^{-(L-1)} = 2 * 2^{-L}`
      have : baseWidth x / 2 ≤ 2 * (2 : ℝ) ^ (-(L_of x : ℤ)) := by
        simpa [hzpow, mul_assoc, mul_left_comm, mul_comm] using hbge
      linarith
    refine ⟨hsubset, ?_⟩
    simpa [hlen] using hb_le

  -- V3: Build a prefix-free machine that halts on the chosen codes.
  let Mv : PrefixFreeMachine :=
    { compute := fun p =>
        if h : ∃ x : BinString, v x ≠ 0 ∧ code x = p then some (Classical.choose h) else none
      prefix_free := by
        intro p q hpq hpne hp
        classical
        -- If `p` halts, it is `code x` for some `x`. Any strict extension would force
        -- overlap of dyadic intervals, contradicting disjointness of base intervals.
        by_contra hq
        have hp' : ∃ x : BinString, v x ≠ 0 ∧ code x = p := by
          simpa using hp
        have hq' : ∃ y : BinString, v y ≠ 0 ∧ code y = q := by
          -- from `compute q ≠ none`
          classical
          by_cases h : ∃ y : BinString, v y ≠ 0 ∧ code y = q
          · exact h
          · exfalso
            -- If there is no witness, `compute q = none`, contradicting `hq : compute q ≠ none`.
            apply hq
            simp [h]
        rcases hp' with ⟨x, hx0, rfl⟩
        rcases hq' with ⟨y, hy0, rfl⟩
        -- prefix implies interval nesting
        have hsub : dyadicInterval (code y) ⊆ dyadicInterval (code x) :=
          prefix_implies_interval_subset _ _ hpq
        -- `dyadicInterval (code y)` is nonempty (contains its left endpoint)
        have hy_nonempty : (dyadicInterval (code y)).Nonempty := by
          refine ⟨binToReal (code y), ?_⟩
          unfold dyadicInterval
          constructor
          · exact le_rfl
          ·
            have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
            have : (0 : ℝ) < (2 : ℝ) ^ (-(code y).length : ℤ) := by
              exact zpow_pos h2pos (-(code y).length : ℤ)
            linarith
        -- But then `dyadicInterval (code y)` is contained in both base intervals; this forces `x = y`,
        -- contradicting strict prefix.
        have hxI := (code_spec x hx0).1
        have hyI := (code_spec y hy0).1
        have hy_in_x : dyadicInterval (code y) ⊆ baseInterval x := hsub.trans hxI
        -- pick a point in `dyadicInterval (code y)` and show it lies in both base intervals
        rcases hy_nonempty with ⟨t, ht⟩
        have ht_x : t ∈ baseInterval x := hy_in_x (by simpa using ht)
        have ht_y : t ∈ baseInterval y := hyI (by simpa using ht)
        -- disjointness of base intervals when `encode x ≠ encode y`
        have hn : Encodable.encode x = Encodable.encode y := by
          by_contra hne
          -- wlog `encode x < encode y`
          cases lt_or_gt_of_ne hne with
          | inl hlt =>
              -- right endpoint of `x` is at most left endpoint of `y`
              have hmono : pref v (Encodable.encode x + 1) ≤ pref v (Encodable.encode y) :=
                pref_mono (m := Encodable.encode x + 1) (n := Encodable.encode y) (Nat.succ_le_iff.2 hlt)
              have htop1 : pref v (Encodable.encode x + 1) ≠ (⊤ : ENNReal) := by
                exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode x + 1)) (by simp))
              have htop2 : pref v (Encodable.encode y) ≠ (⊤ : ENNReal) := by
                exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode y)) (by simp))
              have hx_toReal : (pref v (Encodable.encode x + 1)).toReal ≤ (pref v (Encodable.encode y)).toReal :=
                (ENNReal.toReal_le_toReal htop1 htop2).2 hmono
              -- show `t` cannot be in both intervals
              have : baseLeft x + baseWidth x ≤ baseLeft y := by
                -- right endpoint of `x` is `pref (encode x + 1)`
                have htop_left : pref v (Encodable.encode x) ≠ (⊤ : ENNReal) := by
                  exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode x)) (by simp))
                have hvNat : vNat v (Encodable.encode x) = v x := by
                  dsimp [vNat]
                  exact extendEncode_apply_encode (f := v) x
                have htoReal_add :
                    (pref v (Encodable.encode x) + v x).toReal =
                      (pref v (Encodable.encode x)).toReal + (v x).toReal := by
                  simpa using ENNReal.toReal_add htop_left (v_ne_top x)
                have : (pref v (Encodable.encode x + 1)).toReal =
                      (pref v (Encodable.encode x)).toReal + (v x).toReal := by
                  simpa [pref_succ (v := v) (Encodable.encode x), hvNat] using htoReal_add
                have : baseLeft x + baseWidth x = (pref v (Encodable.encode x + 1)).toReal := by
                  simp [baseLeft, baseWidth, this, add_comm]
                -- left endpoint of `y` is `pref (encode y)`
                have : baseLeft y = (pref v (Encodable.encode y)).toReal := by simp [baseLeft]
                linarith [hx_toReal, this]
              have hdisj :
                  Disjoint (baseInterval x) (baseInterval y) := by
                refine Set.disjoint_left.mpr ?_
                intro t ht_x'
                -- `t < right_x ≤ left_y`, so `t ∉ [left_y, right_y)`.
                have ht_lt : t < baseLeft y := lt_of_lt_of_le ht_x'.2 this
                intro ht_y'
                exact (not_lt_of_ge ht_y'.1) ht_lt
              exact (Set.disjoint_left.mp hdisj ht_x) ht_y
          | inr hgt =>
              -- symmetric contradiction (swap `x` and `y`)
              have hmono : pref v (Encodable.encode y + 1) ≤ pref v (Encodable.encode x) :=
                pref_mono (m := Encodable.encode y + 1) (n := Encodable.encode x) (Nat.succ_le_iff.2 hgt)
              have htop1 : pref v (Encodable.encode y + 1) ≠ (⊤ : ENNReal) := by
                exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode y + 1)) (by simp))
              have htop2 : pref v (Encodable.encode x) ≠ (⊤ : ENNReal) := by
                exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode x)) (by simp))
              have hy_toReal : (pref v (Encodable.encode y + 1)).toReal ≤ (pref v (Encodable.encode x)).toReal :=
                (ENNReal.toReal_le_toReal htop1 htop2).2 hmono
              have : baseLeft y + baseWidth y ≤ baseLeft x := by
                have htop_left : pref v (Encodable.encode y) ≠ (⊤ : ENNReal) := by
                  exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode y)) (by simp))
                have hvNat : vNat v (Encodable.encode y) = v y := by
                  dsimp [vNat]
                  exact extendEncode_apply_encode (f := v) y
                have htoReal_add :
                    (pref v (Encodable.encode y) + v y).toReal =
                      (pref v (Encodable.encode y)).toReal + (v y).toReal := by
                  simpa using ENNReal.toReal_add htop_left (v_ne_top y)
                have : (pref v (Encodable.encode y + 1)).toReal =
                      (pref v (Encodable.encode y)).toReal + (v y).toReal := by
                  simpa [pref_succ (v := v) (Encodable.encode y), hvNat] using htoReal_add
                have : baseLeft y + baseWidth y = (pref v (Encodable.encode y + 1)).toReal := by
                  simp [baseLeft, baseWidth, this, add_comm]
                have : baseLeft x = (pref v (Encodable.encode x)).toReal := by simp [baseLeft]
                linarith [hy_toReal, this]
              have hdisj :
                  Disjoint (baseInterval y) (baseInterval x) := by
                refine Set.disjoint_left.mpr ?_
                intro t ht_y'
                have ht_lt : t < baseLeft x := lt_of_lt_of_le ht_y'.2 this
                intro ht_x'
                exact (not_lt_of_ge ht_x'.1) ht_lt
              exact (Set.disjoint_left.mp hdisj ht_y) ht_x
        have hxy : x = y := Encodable.encode_injective hn
        subst hxy
        exact hpne rfl }

  -- Universal simulation constant for `Mv`.
  obtain ⟨c, hc⟩ := UniversalPFM.universal (U := U) (M := Mv)
  let C : ENNReal := (4 : ENNReal) * (2 : ENNReal) ^ (c : ℤ)
  refine ⟨C, by
    have h4 : (4 : ENNReal) ≠ 0 := by norm_num
    have h2 : (2 : ENNReal) ≠ 0 := by norm_num
    have hc' : (2 : ENNReal) ^ (c : ℤ) ≠ 0 := by
      -- `ENNReal` does not form a `GroupWithZero` (since `⊤` is nonzero but not invertible),
      -- so use the dedicated positivity lemma.
      exact ne_of_gt (ENNReal.zpow_pos (a := (2 : ENNReal)) (by norm_num) (by simp) (c : ℤ))
    exact mul_ne_zero h4 hc', ?_⟩
  intro x
  by_cases hx0 : v x = 0
  · simp [C, hx0]
  · -- simulate the code for `x` on `U` and compare weights
    have hhalt : Mv.compute (code x) = some x := by
      -- This follows from injectivity of codes; `Mv.compute` selects the unique `x` for its code.
      classical
      -- We use the witness `x` itself.
      have h : ∃ y : BinString, v y ≠ 0 ∧ code y = code x := ⟨x, hx0, rfl⟩
      have hy : v (Classical.choose h) ≠ 0 ∧ code (Classical.choose h) = code x := Classical.choose_spec h
      -- If `code (choose h) = code x`, then (by base interval disjointness) `choose h = x`.
      have hchoose : Classical.choose h = x := by
        -- `dyadicInterval (code x)` is nonempty, so it cannot lie in two disjoint base intervals.
        have hxI := (code_spec x hx0).1
        have hyI := (code_spec (Classical.choose h) hy.1).1
        have hnonempty : (dyadicInterval (code x)).Nonempty := by
          refine ⟨binToReal (code x), ?_⟩
          unfold dyadicInterval
          constructor
          · exact le_rfl
          ·
            have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
            have : (0 : ℝ) < (2 : ℝ) ^ (-(code x).length : ℤ) := by
              exact zpow_pos h2pos (-(code x).length : ℤ)
            linarith
        rcases hnonempty with ⟨t, ht⟩
        have ht_x : t ∈ baseInterval x := hxI (by simpa using ht)
        have ht_y : t ∈ baseInterval (Classical.choose h) := by
          -- use `hy.2` to rewrite
          have : dyadicInterval (code x) ⊆ dyadicInterval (code (Classical.choose h)) := by
            simp [hy.2]
          exact hyI (by simpa [hy.2] using ht)
        have hn : Encodable.encode (Classical.choose h) = Encodable.encode x := by
          -- if unequal, base intervals would be disjoint, contradicting `t ∈ ⋂`.
          by_contra hne
          cases lt_or_gt_of_ne hne with
          | inl hlt =>
              have hmono : pref v (Encodable.encode (Classical.choose h) + 1) ≤ pref v (Encodable.encode x) :=
                pref_mono (m := Encodable.encode (Classical.choose h) + 1) (n := Encodable.encode x) (Nat.succ_le_iff.2 hlt)
              have htop1 : pref v (Encodable.encode (Classical.choose h) + 1) ≠ (⊤ : ENNReal) := by
                exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode (Classical.choose h) + 1)) (by simp))
              have htop2 : pref v (Encodable.encode x) ≠ (⊤ : ENNReal) := by
                exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode x)) (by simp))
              have hx_toReal : (pref v (Encodable.encode (Classical.choose h) + 1)).toReal ≤ (pref v (Encodable.encode x)).toReal :=
                (ENNReal.toReal_le_toReal htop1 htop2).2 hmono
              have hRight :
                  baseLeft (Classical.choose h) + baseWidth (Classical.choose h) =
                    (pref v (Encodable.encode (Classical.choose h) + 1)).toReal :=
                baseLeft_add_width_eq (x := Classical.choose h)
              have hLeft : baseLeft x = (pref v (Encodable.encode x)).toReal := by simp [baseLeft]
              have hle : baseLeft (Classical.choose h) + baseWidth (Classical.choose h) ≤ baseLeft x := by
                linarith [hx_toReal, hRight, hLeft]
              have hdisj : Disjoint (baseInterval (Classical.choose h)) (baseInterval x) := by
                refine Set.disjoint_left.mpr ?_
                intro t ht_choose
                have ht_lt : t < baseLeft x := lt_of_lt_of_le ht_choose.2 hle
                intro ht_x'
                exact (not_lt_of_ge ht_x'.1) ht_lt
              exact (Set.disjoint_left.mp hdisj ht_y) ht_x
          | inr hgt =>
              -- symmetric (`encode x < encode (choose h)`)
              have hmono : pref v (Encodable.encode x + 1) ≤ pref v (Encodable.encode (Classical.choose h)) :=
                pref_mono (m := Encodable.encode x + 1) (n := Encodable.encode (Classical.choose h)) (Nat.succ_le_iff.2 hgt)
              have htop1 : pref v (Encodable.encode x + 1) ≠ (⊤ : ENNReal) := by
                exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode x + 1)) (by simp))
              have htop2 : pref v (Encodable.encode (Classical.choose h)) ≠ (⊤ : ENNReal) := by
                exact ne_of_lt (lt_of_le_of_lt (pref_le_one (v := v) hv_sum (Encodable.encode (Classical.choose h))) (by simp))
              have hx_toReal : (pref v (Encodable.encode x + 1)).toReal ≤ (pref v (Encodable.encode (Classical.choose h))).toReal :=
                (ENNReal.toReal_le_toReal htop1 htop2).2 hmono
              have hRight : baseLeft x + baseWidth x = (pref v (Encodable.encode x + 1)).toReal :=
                baseLeft_add_width_eq (x := x)
              have hLeft : baseLeft (Classical.choose h) = (pref v (Encodable.encode (Classical.choose h))).toReal := by
                simp [baseLeft]
              have hle : baseLeft x + baseWidth x ≤ baseLeft (Classical.choose h) := by
                linarith [hx_toReal, hRight, hLeft]
              have hdisj : Disjoint (baseInterval x) (baseInterval (Classical.choose h)) := by
                refine Set.disjoint_left.mpr ?_
                intro t ht_x'
                have ht_lt : t < baseLeft (Classical.choose h) := lt_of_lt_of_le ht_x'.2 hle
                intro ht_y'
                exact (not_lt_of_ge ht_y'.1) ht_lt
              exact (Set.disjoint_left.mp hdisj ht_x) ht_y
        exact Encodable.encode_injective hn
      -- now compute value
      simp [Mv, h, hchoose]
    obtain ⟨q, hq_comp, hq_len⟩ := hc (code x) x hhalt
    have hK : KolmogorovComplexity.prefixComplexity U x ≤ q.length :=
      Mettapedia.Logic.SolomonoffPrior.complexity_le_program_length U x q hq_comp
    have hK' : (KolmogorovComplexity.prefixComplexity U x : ℤ) ≤ (code x).length + c := by
      exact le_trans (Int.ofNat_le.2 hK) (Int.ofNat_le.2 hq_len)
    have hExp :
        (-( (code x).length + c : ℤ)) ≤ -(KolmogorovComplexity.prefixComplexity U x : ℤ) :=
      Int.neg_le_neg hK'
    have hkpf :
        (2 : ENNReal) ^ (-( (code x).length + c : ℤ)) ≤ kpfWeight (U := U) x := by
      have h2le : (1 : ENNReal) ≤ 2 := by simp
      simpa [kpfWeight] using (ENNReal.zpow_le_of_le h2le hExp)
    have hxI := (code_spec x hx0)
    have hv_le_real : (v x).toReal ≤ 4 * (2 : ℝ) ^ (-(code x).length : ℤ) := hxI.2
    have hv_le : v x ≤ (4 : ENNReal) * (2 : ENNReal) ^ (-(code x).length : ℤ) := by
      have htop : v x ≠ (⊤ : ENNReal) := v_ne_top x
      have hv_eq : v x = ENNReal.ofReal (v x).toReal := by
        exact (ENNReal.ofReal_toReal htop).symm
      have hdy :
          ENNReal.ofReal ((2 : ℝ) ^ (-(code x).length : ℤ)) =
            (2 : ENNReal) ^ (-(code x).length : ℤ) := by
        simpa using KolmogorovComplexity.ofReal_two_zpow_neg_nat (n := (code x).length)
      have h4eq :
          ENNReal.ofReal (4 * (2 : ℝ) ^ (-(code x).length : ℤ)) =
            (4 : ENNReal) * (2 : ENNReal) ^ (-(code x).length : ℤ) := by
        -- `ENNReal` simplifies negative `zpow`s to inverses; normalize with `zpow_neg` first.
        have hz : (2 : ENNReal) ^ (-(code x).length : ℤ) = (2 ^ (code x).length : ENNReal)⁻¹ := by
          simpa [zpow_natCast] using (ENNReal.zpow_neg (2 : ENNReal) ((code x).length : ℤ))
        simp [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), hz]
      have hineq :
          ENNReal.ofReal (v x).toReal ≤ ENNReal.ofReal (4 * (2 : ℝ) ^ (-(code x).length : ℤ)) :=
        ENNReal.ofReal_le_ofReal hv_le_real
      -- Avoid `simp` loops: just rewrite with the two equalities.
      calc
        v x = ENNReal.ofReal (v x).toReal := hv_eq
        _ ≤ ENNReal.ofReal (4 * (2 : ℝ) ^ (-(code x).length : ℤ)) := hineq
        _ = (4 : ENNReal) * (2 : ENNReal) ^ (-(code x).length : ℤ) := h4eq
    have h2ne0 : (2 : ENNReal) ≠ 0 := by norm_num
    have h2neTop : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
    have hzpow :
        (2 : ENNReal) ^ (-(code x).length : ℤ) =
          (2 : ENNReal) ^ (-( (code x).length + c : ℤ)) * (2 : ENNReal) ^ (c : ℤ) := by
      have hExp' : (-(code x).length : ℤ) = (-( (code x).length + c : ℤ)) + (c : ℤ) := by omega
      rw [hExp']
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (ENNReal.zpow_add (x := (2 : ENNReal)) h2ne0 h2neTop (-( (code x).length + c : ℤ)) (c : ℤ))
    have : (4 : ENNReal) * (2 : ENNReal) ^ (-(code x).length : ℤ) =
          C * (2 : ENNReal) ^ (-( (code x).length + c : ℤ)) := by
      simp [C, hzpow, mul_assoc, mul_left_comm, mul_comm]
    have hmul :
        C * (2 : ENNReal) ^ (-( (code x).length + c : ℤ)) ≤ C * kpfWeight (U := U) x :=
      mul_le_mul_right hkpf C
    exact le_trans (by simpa [this] using hv_le) hmul

end OptimalWeights

end Mettapedia.Logic.UniversalPrediction
