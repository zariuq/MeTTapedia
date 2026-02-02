import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mettapedia.Logic.UniversalPrediction
import Mettapedia.Logic.UniversalPrediction.LossBounds
import Mettapedia.Logic.UniversalPrediction.ErrorBounds
import Mettapedia.Logic.UniversalPrediction.Convergence
import Mettapedia.Logic.UniversalPrediction.FiniteHorizon
import Mettapedia.Logic.UniversalPrediction.HutterEnumerationTheorem
import Mettapedia.Logic.UniversalPrediction.HutterEnumerationTheoremSemimeasure
import Mettapedia.Logic.UniversalPrediction.HutterV3Kpf

/-!
# Solomonoff Bridge: Connecting Chapter 2 to Chapter 3

This file bridges “Chapter 2 computability” to “Chapter 3 prediction bounds” in the style of
Hutter (2005).

## What is theorem-grade here (no toy axioms)

This development proves the **mixture route**:

1. Fix a concrete enumeration theorem (Levin/Hutter style) giving a countable family of
   lower-semicomputable semimeasures (or prefix measures), indexed by `Nat.Partrec.Code`.
2. Form a universal mixture `M` using a provably summable weight function (`encodeWeight`).
3. Apply the generic Chapter‑3 dominance→regret lemma:

   `Dominates M μ c  ⟹  Dₙ(μ‖M) ≤ log(1/c)`.

Concretely, this file exposes two canonical mixtures:
* `M₁`: mixture over lower-semicomputable **prefix measures**
* `M₂`: mixture over lower-semicomputable **semimeasures** (closer to Hutter’s Chapter‑2 class)

and provides theorem-grade dominance/regret statements:
* `relEntropy_le_log_inv_M₁`
* `relEntropy_le_log_inv_M₂`

## What is *not* claimed yet

Hutter’s book also relates the dominance constant to algorithmic complexity, e.g. a schematic
form `c = 2^{-K(μ)}` (and further “coding theorem” statements comparing `M(x)` to `2^{-K(x)}`).
Those require additional AIT infrastructure tying the chosen enumeration/weights to a genuine
Kolmogorov complexity of environments.  This file keeps such statements clearly separated as
optional scaffolding (and never as masked placeholders).

## References

- Hutter (2005): "Universal Artificial Intelligence", Chapter 2-3
- Solomonoff (1964): "A Formal Theory of Inductive Inference"
- Levin (1974): "Laws of information conservation"
- Li & Vitányi (2008): "An Introduction to Kolmogorov Complexity"

-/

namespace Mettapedia.Logic.UniversalPrediction.SolomonoffBridge

open scoped Classical BigOperators ENNReal

open Mettapedia.Logic.SolomonoffPrior
open Mettapedia.Logic.SolomonoffInduction
open Mettapedia.Logic.UniversalPrediction
open FiniteHorizon

/-! ## Part 1: A Concrete “Solomonoff-style” Universal Mixture (No Toy Axioms)

Hutter (2005) ultimately wants the universal predictor to be a mixture over the class
`M` of **enumerable (lower semicomputable) semimeasures** (Chapter 2, §2.4).

We implement this via the “mixture route”:

* Use a concrete enumeration theorem to get a **countable** index set (here `Nat.Partrec.Code`)
  that surjects onto the target class (LSC prefix measures or semimeasures).
* Define the universal mixture `ξ` using the provably summable `encodeWeight`.
* Instantly obtain dominance and regret bounds from Chapter 3 (`FiniteHorizon`).

This file exposes two canonical universal mixtures:

* `M₁`: mixture over lower-semicomputable **prefix measures** (already enough for the
  finite-horizon regret bounds stated for `μ : PrefixMeasure`).
* `M₂`: mixture over lower-semicomputable **semimeasures** (closer to Hutter’s Chapter‑2 class).
-/

/-- Universal mixture over lower-semicomputable **prefix measures** (V3, concrete enumeration). -/
noncomputable abbrev M₁ : Semimeasure :=
  HutterEnumerationTheorem.lscPrefixMeasureEnumeration.toPrefixMeasureEnumeration.xi

/-- Universal mixture over lower-semicomputable **semimeasures** (V3, concrete enumeration). -/
noncomputable abbrev M₂ : Semimeasure :=
  HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration.xi

/-- Universal mixture over lower-semicomputable **semimeasures** using `2^{-Kpf}` weights
(Hutter-style V3 with an explicit universal prefix-free machine `U`). -/
noncomputable abbrev M₃ (U : PrefixFreeMachine) [UniversalPFM U] : Semimeasure :=
  HutterV3Kpf.M₃ (U := U)

/-! ## Part 2: Dominance/Regret (Theorem-grade, no axiomatized dominance) -/

/-- Dominance→regret bound for `M₁` against any lower-semicomputable prefix measure. -/
theorem relEntropy_le_log_inv_M₁ (μ : PrefixMeasure)
    (hμ : Mettapedia.Logic.UniversalPrediction.HutterEnumeration.LowerSemicomputablePrefixMeasure μ)
    (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧ Dominates M₁ μ c ∧ relEntropy μ M₁ n ≤ Real.log (1 / c.toReal) := by
  simpa [M₁] using
    (Mettapedia.Logic.UniversalPrediction.relEntropy_le_log_inv_of_LSC_concrete (μ := μ) hμ n)

/-- Dominance→regret bound for `M₂` against any lower-semicomputable prefix measure. -/
theorem relEntropy_le_log_inv_M₂ (μ : PrefixMeasure)
    (hμ : Mettapedia.Logic.UniversalPrediction.HutterEnumeration.LowerSemicomputablePrefixMeasure μ)
    (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧ Dominates M₂ μ c ∧ relEntropy μ M₂ n ≤ Real.log (1 / c.toReal) := by
  simpa [M₂] using
    (Mettapedia.Logic.UniversalPrediction.relEntropy_le_log_inv_of_LSC_semimeasure_concrete
      (μ := μ) hμ n)

/-! ### Interpreting the dominance constant as a “code length”

The theorems above return an abstract dominance constant `c > 0`.

For our concrete V3 mixture `M₂`, the proof actually constructs `c` as a weight of the form
`encodeWeight code = (1/2)^(encode code + 1)`.  This is the cleanest “faithful-to-Hutter”
statement we can currently make without importing a full Kolmogorov complexity-of-environments
layer. -/

theorem log_inv_encodeWeight (c : Nat.Partrec.Code) :
    Real.log (1 / (encodeWeight c).toReal) = (Encodable.encode c + 1) * Real.log 2 := by
  -- `encodeWeight c = (1/2)^(encode c + 1)` and `log (2^n) = n * log 2`.
  classical
  have hpow :
      (encodeWeight c).toReal = ((2 : ℝ)⁻¹) ^ (Encodable.encode c + 1) := by
    -- `toReal` commutes with `pow` and `toReal (2⁻¹) = (2:ℝ)⁻¹`.
    simp [encodeWeight, ENNReal.toReal_pow]
  -- Rewrite `1 / (1/2)^n = 2^n`.
  have hdiv :
      (1 : ℝ) / (encodeWeight c).toReal = (2 : ℝ) ^ (Encodable.encode c + 1) := by
    -- Use `hpow` and `inv_pow`.
    have h2ne0 : (2 : ℝ) ≠ 0 := by norm_num
    -- `((2:ℝ)⁻¹)^n = (2^n)⁻¹`.
    calc
      (1 : ℝ) / (encodeWeight c).toReal
          = (1 : ℝ) / (((2 : ℝ)⁻¹) ^ (Encodable.encode c + 1)) := by simp [hpow]
      _ = (1 : ℝ) / ((2 : ℝ) ^ (Encodable.encode c + 1))⁻¹ := by
            simp [inv_pow]
      _ = (2 : ℝ) ^ (Encodable.encode c + 1) := by
            simp [div_eq_mul_inv]
  -- Now take logs.
  calc
    Real.log (1 / (encodeWeight c).toReal)
        = Real.log ((2 : ℝ) ^ (Encodable.encode c + 1)) := by simp [hdiv]
    _ = (Encodable.encode c + 1) * Real.log 2 := by simp [Real.log_pow]

theorem neg_log_encodeWeight (c : Nat.Partrec.Code) :
    -Real.log (encodeWeight c).toReal = (Encodable.encode c + 1) * Real.log 2 := by
  have hlog : Real.log (1 / (encodeWeight c).toReal) = -Real.log (encodeWeight c).toReal := by
    simp [one_div]
  -- Rewrite `-log` into `log (1/·)` and reuse `log_inv_encodeWeight`.
  calc
    -Real.log (encodeWeight c).toReal = Real.log (1 / (encodeWeight c).toReal) := by
      exact hlog.symm
    _ = (Encodable.encode c + 1) * Real.log 2 := log_inv_encodeWeight c

/-- **V3 (semimeasure enumeration)**: a code-level dominance→regret bound for `M₂`.

This exposes the concrete witness `code : Nat.Partrec.Code` and rewrites the RHS bound as a
“description length” term `(encode code + 1) * log 2`. -/
theorem relEntropy_le_codeLength_log2_M₂ (μ : PrefixMeasure)
    (hμ : Mettapedia.Logic.UniversalPrediction.HutterEnumeration.LowerSemicomputablePrefixMeasure μ)
    (n : ℕ) :
    ∃ code : Nat.Partrec.Code,
      Dominates M₂ μ (encodeWeight code) ∧
        relEntropy μ M₂ n ≤ (Encodable.encode code + 1) * Real.log 2 := by
  classical
  -- Get a code for `μ` viewed as a semimeasure.
  have hμ_sem :
      Mettapedia.Logic.UniversalPrediction.HutterEnumeration.LowerSemicomputableSemimeasure
        μ.toSemimeasure := by
    simpa [Mettapedia.Logic.UniversalPrediction.HutterEnumeration.LowerSemicomputableSemimeasure,
      Mettapedia.Logic.UniversalPrediction.HutterEnumeration.LowerSemicomputablePrefixMeasure] using hμ
  obtain ⟨code, hcode⟩ :=
    HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration.surj_eval μ.toSemimeasure hμ_sem
  -- Dominance is immediate from the mixture construction.
  have hdom : Dominates M₂ μ (encodeWeight code) := by
    intro x
    have hdom' :
        encodeWeight code * (HutterEnumerationTheoremSemimeasure.evalLSC code) x ≤ M₂ x := by
      -- `M₂ = xiEncodeSemimeasure evalLSC`.
      simpa [M₂, HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration,
        Mettapedia.Logic.UniversalPrediction.HutterEnumeration.LSCSemimeasureEnumeration.xi] using
        (xiEncode_dominates_index
          (ι := Nat.Partrec.Code) (ν := fun d => HutterEnumerationTheoremSemimeasure.evalLSC d)
          code x)
    have hcode_x : HutterEnumerationTheoremSemimeasure.evalLSC code x = μ x := by
      have := congrArg (fun ξ : Semimeasure => ξ x) hcode
      simpa [PrefixMeasure.toSemimeasure_apply] using this
    simpa [hcode_x] using hdom'
  have hc0 : encodeWeight code ≠ 0 := by
    unfold encodeWeight
    exact pow_ne_zero _ (by simp)
  have hbound :=
    relEntropy_le_log_inv_of_dominates (μ := μ) (ξ := M₂) (hdom := hdom) (hc0 := hc0) n
  refine ⟨code, hdom, ?_⟩
  simpa [neg_log_encodeWeight code] using hbound

/-! ### “V3” in Hutter’s preferred `K * log 2` form

For the `encodeWeight` mixtures `M₁/M₂`, the regret bound is naturally stated as
`log(1/c)` and can be rewritten as a code-length expression `(encode code + 1) * log 2`.

For the `kpfWeight` mixture `M₃(U)`, the dominance constant is literally `2^{-Kpf[U](code)}`
and the regret bound becomes `Kpf * log 2` directly. -/

/-- Code-level dominance→regret bound for `M₃(U)`, stated in the `Kpf * log 2` form. -/
theorem relEntropy_le_codeKpf_log2_M₃ (U : PrefixFreeMachine) [UniversalPFM U] (μ : PrefixMeasure)
    (hμ : Mettapedia.Logic.UniversalPrediction.HutterEnumeration.LowerSemicomputablePrefixMeasure μ)
    (n : ℕ) :
    ∃ code : Nat.Partrec.Code,
      Dominates (M₃ (U := U)) μ (HutterV3Kpf.codeWeight (U := U) code) ∧
        relEntropy μ (M₃ (U := U)) n ≤
          (KolmogorovComplexity.prefixComplexity U (HutterV3Kpf.codeToBinString code) : ℝ) *
            Real.log 2 := by
  simpa [M₃] using (HutterV3Kpf.relEntropy_le_codeKpf_log2_M₃ (U := U) (μ := μ) hμ n)

/-- Hutter-style V3 bound, stated using the *minimum* complexity `K(μ)` among all codes
enumerating `μ`. -/
theorem relEntropy_le_Kμ_log2_M₃ (U : PrefixFreeMachine) [UniversalPFM U] (μ : PrefixMeasure)
    (hμ : Mettapedia.Logic.UniversalPrediction.HutterEnumeration.LowerSemicomputablePrefixMeasure μ)
    (n : ℕ) :
    relEntropy μ (M₃ (U := U)) n ≤ (HutterV3Kpf.Kμ (U := U) μ : ℝ) * Real.log 2 := by
  simpa [M₃] using (HutterV3Kpf.relEntropy_le_Kμ_log2 (U := U) (μ := μ) hμ n)

/-- Machine invariance: `K(μ)` changes by at most an additive constant when switching universal
machines. -/
theorem invariance_Kμ (U V : PrefixFreeMachine) [UniversalPFM U] [UniversalPFM V] :
    ∃ c : ℕ, ∀ μ : PrefixMeasure,
      Mettapedia.Logic.UniversalPrediction.HutterEnumeration.LowerSemicomputablePrefixMeasure μ →
        HutterV3Kpf.Kμ (U := U) μ ≤ HutterV3Kpf.Kμ (U := V) μ + c ∧
        HutterV3Kpf.Kμ (U := V) μ ≤ HutterV3Kpf.Kμ (U := U) μ + c :=
  HutterV3Kpf.invariance_Kμ (U := U) (V := V)

/-- Hutter’s V3 dominance constant can be taken to be exactly `2^{-K(μ)}`. -/
theorem dominates_M₃_of_LSC_Kμ (U : PrefixFreeMachine) [UniversalPFM U] (μ : PrefixMeasure)
    (hμ : Mettapedia.Logic.UniversalPrediction.HutterEnumeration.LowerSemicomputablePrefixMeasure μ) :
    Dominates (M₃ (U := U)) μ ((2 : ENNReal) ^ (-(HutterV3Kpf.Kμ (U := U) μ : ℤ))) := by
  simpa [M₃] using (HutterV3Kpf.dominates_M₃_of_LSC_Kμ (U := U) (μ := μ) hμ)


/-! ## Part 3: Log-loss algebra (generic dominance bounds)

Theorem-grade dominance/regret for our concrete universal mixtures is provided above
(`relEntropy_le_log_inv_M₁`, `relEntropy_le_log_inv_M₂`).  The remaining lemmas in this file
are generic algebraic/logarithmic identities and (optional) coding-theorem scaffolding.
-/

/-! ## Part 2b: Log-loss / regret from dominance

The key “universal prediction” consequence of dominance is a **log-loss regret** bound.

At the level of finite prefixes, dominance gives:

`log (μ(x) / ξ(x)) ≤ log (1/c)`.

When the dominance constant is `c = 2^{-K}`, this becomes `≤ K * log 2`.
-/

theorem log_inv_two_zpow_neg (K : ℕ) :
    Real.log (1 / ((2 : ENNReal) ^ (-(K : ℤ))).toReal) = (K : ℝ) * Real.log 2 := by
  -- This is the standard identity: `log(1 / 2^{-K}) = log(2^K) = K * log 2`.
  simp only [one_div]
  rw [Real.log_inv]
  -- Rewrite `2^{-K}` as `(2^K)⁻¹`, and cancel the double inverse.
  conv_lhs =>
    rw [ENNReal.zpow_neg]
  rw [ENNReal.toReal_inv, Real.log_inv, neg_neg]
  -- Now `2^K` is a natural power.
  rw [zpow_natCast, ENNReal.toReal_pow]
  simp [Real.log_pow]

/-- Pointwise log-likelihood ratio bound specialized to `c = 2^{-K}`. -/
theorem log_ratio_le_K_log2_of_dominates_pow_two
    (μ : PrefixMeasure) (ξ : Semimeasure) (K : ℕ)
    (hdom : Dominates ξ μ ((2 : ENNReal) ^ (-(K : ℤ)))) (x : BinString) :
    Real.log ((μ x).toReal / (ξ x).toReal) ≤ (K : ℝ) * Real.log 2 := by
  have hc0 : ((2 : ENNReal) ^ (-(K : ℤ))) ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.zpow_pos (a := (2 : ENNReal)) (n := -(K : ℤ)) (by norm_num) (by simp)
  have h :=
    log_ratio_le_log_inv_of_dominates (μ := μ) (ξ := ξ) (hdom := hdom) (hc0 := hc0) (x := x)
  -- `simp` tends to normalize the RHS into `-log(c)`; convert our closed form accordingly.
  have hRHS : Real.log (1 / ((2 : ENNReal) ^ (-(K : ℤ))).toReal) = (K : ℝ) * Real.log 2 :=
    log_inv_two_zpow_neg K
  have hRHS' : -Real.log (((2 : ENNReal) ^ (-(K : ℤ))).toReal) = (K : ℝ) * Real.log 2 := by
    simpa [one_div] using hRHS
  simpa [hRHS'] using h

/-- Expected (finite-horizon) log-loss regret bound specialized to `c = 2^{-K}`.

This is the “constant regret” statement in log-loss, since it is uniform in `n`. -/
theorem relEntropy_le_K_log2_of_dominates_pow_two
    (μ : PrefixMeasure) (ξ : Semimeasure) (K : ℕ)
    (hdom : Dominates ξ μ ((2 : ENNReal) ^ (-(K : ℤ)))) (n : ℕ) :
    relEntropy μ ξ n ≤ (K : ℝ) * Real.log 2 := by
  have hc0 : ((2 : ENNReal) ^ (-(K : ℤ))) ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.zpow_pos (a := (2 : ENNReal)) (n := -(K : ℤ)) (by norm_num) (by simp)
  have h := relEntropy_le_log_inv_of_dominates (μ := μ) (ξ := ξ) (hdom := hdom) (hc0 := hc0) n
  have hRHS : Real.log (1 / ((2 : ENNReal) ^ (-(K : ℤ))).toReal) = (K : ℝ) * Real.log 2 :=
    log_inv_two_zpow_neg K
  have hRHS' : -Real.log (((2 : ENNReal) ^ (-(K : ℤ))).toReal) = (K : ℝ) * Real.log 2 := by
    simpa [one_div] using hRHS
  simpa [hRHS'] using h

/-! ## Part 3: Levin's Coding Theorem

The relationship between algorithmic probability M(x) and Kolmogorov complexity K(x).
-/

/-- Levin's Coding Theorem (Lower Bound): M(x) ≥ 2^{-K(x)}

    The shortest program for x contributes at least 2^{-K(x)} to M(x).
-/
theorem levin_lower_bound (U : PrefixFreeMachine) [UniversalPFM U]
    (M : Mettapedia.Logic.SolomonoffInduction.Semimeasure) (x : BinString)
    (_hx : ∃ p, U.compute p = some x)
    (hM_contains : ∀ p, U.compute p = some x →
      (2 : ENNReal)^(-(p.length : ℤ)) ≤ M x) :
    (2 : ENNReal)^(-(KolmogorovComplexity.prefixComplexity U x : ℤ)) ≤ M x := by
  -- Use the shortest program and its properties
  have ⟨hp_comp, hp_len⟩ := KolmogorovComplexity.shortestProgram_spec U x
  have h := hM_contains _ hp_comp
  rw [hp_len] at h
  exact h

/-- Weak Upper Bound: Any semimeasure satisfies M(x) ≤ M(ε) ≤ 1

    This follows directly from the semimeasure superadditivity property.
-/
theorem semimeasure_le_one (M : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (x : BinString) : M x ≤ 1 := by
  -- Use the fact that M(x) ≤ M(ε) by superadditivity and M(ε) ≤ 1
  induction x using List.reverseRecOn with
  | nil => exact M.root_le_one'
  | append_singleton xs b ih =>
    -- M(xs ++ [b]) ≤ M(xs) by superadditivity
    calc M (xs ++ [b])
        ≤ M xs := by
          have h := M.superadditive' xs
          cases b with
          | false => exact le_of_add_le_left h
          | true => exact le_of_add_le_right h
      _ ≤ 1 := ih

/-- Levin's Coding Theorem (Upper Bound): M(x) ≤ c · 2^{-K(x)}

    **The Coding Theorem (Levin 1974)**:
    For the universal semimeasure M(x) = Σ_{p: U(p)=x} 2^{-|p|}:

      K(x) = -log M(x) ± O(1)

    Equivalently: there exists a universal constant c such that
      M(x) ≤ c · 2^{-K(x)}

    **Proof Sketch** (from Li & Vitányi "An Introduction to Kolmogorov Complexity"):
    1. Programs outputting x form a prefix-free set
    2. The shortest program contributes 2^{-K(x)} to M(x)
    3. Longer programs contribute less individually, but there could be many
    4. The key insight: by prefix-freeness, the total contribution from
       programs of length K(x)+k is bounded by 2^k · 2^{-(K(x)+k)} · f(k)
       where f(k) accounts for the structure of prefix-free codes
    5. Summing over k gives M(x) ≤ c · 2^{-K(x)} for universal c

    **In this formalization**: We require M to be bounded by some multiple of 2^{-K(x)}.
    The constant c encapsulates the Coding Theorem.

    References:
    - Levin (1974): "Laws of information conservation"
    - Li & Vitányi (2008): "An Introduction to Kolmogorov Complexity", Theorem 4.3.3
    - Scholarpedia: https://www.scholarpedia.org/article/Algorithmic_probability
-/
theorem levin_upper_bound (U : PrefixFreeMachine) [UniversalPFM U]
    (M : Mettapedia.Logic.SolomonoffInduction.Semimeasure) (x : BinString)
    (_hx : ∃ p, U.compute p = some x)
    -- Hypothesis: M satisfies the Coding Theorem bound with constant c
    (hM_coding : ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      M x ≤ c * (2 : ENNReal)^(-(KolmogorovComplexity.prefixComplexity U x : ℤ))) :
    M x ≤ (Classical.choose hM_coding) *
      (2 : ENNReal)^(-(KolmogorovComplexity.prefixComplexity U x : ℤ)) :=
  (Classical.choose_spec hM_coding).2.2

/-- For any semimeasure, we can always take c = 2^{K(x)} to satisfy the upper bound.
    This gives a non-universal but always valid constant. -/
theorem levin_upper_bound_nonuniversal (U : PrefixFreeMachine) [UniversalPFM U]
    (M : Mettapedia.Logic.SolomonoffInduction.Semimeasure) (x : BinString)
    (_hx : ∃ p, U.compute p = some x) :
    M x ≤ (2 : ENNReal)^(KolmogorovComplexity.prefixComplexity U x : ℤ) *
      (2 : ENNReal)^(-(KolmogorovComplexity.prefixComplexity U x : ℤ)) := by
  -- 2^K(x) · 2^{-K(x)} = 2^K(x) · (2^K(x))⁻¹ = 1 ≥ M(x)
  have h1 : (2 : ENNReal)^(KolmogorovComplexity.prefixComplexity U x : ℤ) *
      (2 : ENNReal)^(-(KolmogorovComplexity.prefixComplexity U x : ℤ)) = 1 := by
    rw [ENNReal.zpow_neg, zpow_natCast, ENNReal.mul_inv_cancel]
    · exact pow_ne_zero _ (by norm_num)
    · exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  rw [h1]
  exact semimeasure_le_one M x

/-! ## Part 4: Application Bridge to Chapter 3 (via dominance)

All Chapter‑3 finite-horizon bounds in this project are derived from a dominance hypothesis
`Dominates ξ μ c`.  For our concrete “Solomonoff-style” mixtures `M₁` and `M₂`, this is already
available as a theorem (`relEntropy_le_log_inv_M₁`, `relEntropy_le_log_inv_M₂`).

To specialize further bounds (loss, squared error, etc.), combine those dominance constants
with the generic lemmas in:

* `Mettapedia/Logic/UniversalPrediction/FiniteHorizon.lean`
* `Mettapedia/Logic/UniversalPrediction/ErrorBounds.lean`
* `Mettapedia/Logic/UniversalPrediction/LossBounds.lean`
-/

/-! ## Summary (what this file actually proves)

* **Concrete universal mixtures:** `M₁` and `M₂` (no axioms; built from a concrete enumeration).
* **Dominance→regret specialized to those mixtures:** `relEntropy_le_log_inv_M₁` and
  `relEntropy_le_log_inv_M₂`.
* **Generic log-loss algebra:** helper lemmas for rewriting the RHS `log(1/c)` into more
  interpretable forms when `c` has a known expression (e.g. a power of `2`).

Further “Occam factor / Kolmogorov complexity” interpretations (the `2^{-K}` story) belong to the
next layer: relating our enumeration and weights to a formal complexity notion for environments.
-/

end Mettapedia.Logic.UniversalPrediction.SolomonoffBridge
