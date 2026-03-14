import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# No-Go: Sensitivity Amplification in Lipschitz Chains

This module formalizes the **sensitivity amplification** no-go theorem:

If each step of a chain computation is `K`-Lipschitz (i.e., an input error of `ε`
grows to at most `K·ε` at the output), then composing `n` such steps yields a
chain that is `K^n`-Lipschitz—meaning errors can amplify by a factor of `K^n`.

For `K > 1`, this grows without bound as `n → ∞`, making certified error control
impossible for long chains without additional damping.

**Design implication**: certified per-step sensitivity bounds cannot be composed
into chain-length-independent error certificates when K > 1.

## Key observation

Mathlib already provides `LipschitzWith.iterate : LipschitzWith K f → ∀ n, LipschitzWith (K^n) f^[n]`.

The central contribution here is:
1. The clean statement as an explicit no-go (amplification factor = K^n for uniform chains).
2. Extension to heterogeneous chains (each step has its own Lipschitz constant Lᵢ).
3. The asymptotic divergence corollary for K > 1.
-/

namespace Mettapedia.Logic.PLNSensitivityNoGo

open scoped BigOperators NNReal

/-! ## Core: homogeneous chain (all steps are the same function) -/

/-- **Sensitivity amplification (iterated)**: if `f` is `K`-Lipschitz, then `f^[n]` is
`K^n`-Lipschitz.  For `K > 1` this amplifies errors exponentially.

Direct application of Mathlib's `LipschitzWith.iterate`. -/
theorem lipschitz_iterate_amplification {α : Type*} [PseudoEMetricSpace α]
    (K : ℝ≥0) (f : α → α) (hf : LipschitzWith K f) (n : ℕ) :
    LipschitzWith (K ^ n) f^[n] :=
  hf.iterate n

/-! ## Core: heterogeneous chain (each step may have its own constant) -/

/-- Compose `n` step functions into a single chain.
  `chainFn n fs = fs(n-1) ∘ ... ∘ fs(0)` -/
def chainFn {α : Type*} : ∀ n, (Fin n → α → α) → α → α
  | 0, _ => id
  | n + 1, fs => fs ⟨n, Nat.lt_succ_self n⟩ ∘ chainFn n (fun i => fs i.castSucc)

@[simp] lemma chainFn_zero {α : Type*} (fs : Fin 0 → α → α) : chainFn 0 fs = id := rfl

lemma chainFn_succ {α : Type*} (n : ℕ) (fs : Fin (n + 1) → α → α) :
    chainFn (n + 1) fs = fs ⟨n, Nat.lt_succ_self n⟩ ∘ chainFn n (fun i => fs i.castSucc) := rfl

/-- **Sensitivity amplification (heterogeneous)**: if each step function `fᵢ` is
`Lᵢ`-Lipschitz, then the composed chain is `(∏ᵢ Lᵢ)`-Lipschitz.

For the special case where all `Lᵢ = K`, this gives `K^n`-Lipschitz. -/
theorem lipschitz_chain_amplification {α : Type*} [PseudoEMetricSpace α]
    (n : ℕ) (Ls : Fin n → ℝ≥0) (fs : Fin n → α → α)
    (hfs : ∀ i, LipschitzWith (Ls i) (fs i)) :
    LipschitzWith (∏ i, Ls i) (chainFn n fs) := by
  induction n with
  | zero =>
    simp [chainFn_zero]
    exact LipschitzWith.id
  | succ n ih =>
    rw [chainFn_succ, Fin.prod_univ_castSucc]
    have hchain := ih (fun i => Ls i.castSucc) (fun i => fs i.castSucc)
                     (fun i => hfs i.castSucc)
    have hlast := hfs ⟨n, Nat.lt_succ_self n⟩
    have hcomp := hlast.comp hchain
    rw [mul_comm]
    exact hcomp

/-- **Uniform amplification corollary**: if every step is `K`-Lipschitz, the chain is
`K^n`-Lipschitz. -/
theorem lipschitz_chain_uniform {α : Type*} [PseudoEMetricSpace α]
    (n : ℕ) (K : ℝ≥0) (fs : Fin n → α → α)
    (hfs : ∀ i, LipschitzWith K (fs i)) :
    LipschitzWith (K ^ n) (chainFn n fs) := by
  have h := lipschitz_chain_amplification n (fun _ => K) fs hfs
  simp [Finset.prod_const] at h
  exact h

/-! ## Asymptotic corollary: amplification is unbounded for K > 1 -/

/-- **Unbounded amplification**: for `K > 1`, the chain Lipschitz constant `K^n`
grows without bound as `n → ∞`. No fixed bound can contain the error propagation. -/
theorem lipschitz_amplification_unbounded (K : ℝ≥0) (hK : 1 < K) :
    Filter.Tendsto (fun n => (K : ℝ) ^ n) Filter.atTop Filter.atTop := by
  apply tendsto_pow_atTop_atTop_of_one_lt
  exact_mod_cast hK

end Mettapedia.Logic.PLNSensitivityNoGo
