import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mettapedia.Logic.UniversalPrediction.FiniteHorizon
import Mettapedia.Logic.UniversalPrediction.HutterEnumerationTheoremSemimeasure

/-!
# Hutter V3 (Kpf Weights) for Enumerable Semimeasures

This file provides a “Hutter-happy” V3 universal mixture:

* enumerate all lower-semicomputable semimeasures (via `Nat.Partrec.Code`)
* weight codes by a **prefix-free Kolmogorov complexity** term `2^{-Kpf[U](code)}` (Kraft ≤ 1)
* obtain dominance/regret bounds of the form `Dₙ(μ‖M) ≤ K(μ) * log 2`

Compared to the `encodeWeight` mixture in `SolomonoffBridge.lean`, this is closer to the
book’s preferred Occam factor story `c = 2^{-K(μ)}`.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical BigOperators ENNReal

open Mettapedia.Logic.SolomonoffPrior
open Mettapedia.Logic.SolomonoffInduction

open FiniteHorizon
open HutterEnumerationTheoremSemimeasure

namespace HutterV3Kpf

/-! ## A small injection `Nat.Partrec.Code → BinString`

We pull back the Kraft-summable weights `x ↦ 2^{-Kpf[U](x)}` along an injection from codes
to binary strings.

Any injection would work (all choices differ by an additive constant in complexity), but using
`Nat.digits 2` keeps the proof elementary and self-contained.
-/

private def boolToDigit : Bool → ℕ
  | false => 0
  | true => 1

private def digitToBool (d : ℕ) : Bool :=
  decide (d = 1)

private lemma boolToDigit_digitToBool_of_lt_two {d : ℕ} (hd : d < 2) :
    boolToDigit (digitToBool d) = d := by
  cases d with
  | zero =>
      simp [digitToBool, boolToDigit]
  | succ d =>
      cases d with
      | zero =>
          simp [digitToBool, boolToDigit]
      | succ d =>
          -- Contradiction: `d+2 < 2`.
          exfalso
          have : 2 ≤ Nat.succ (Nat.succ d) :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le d))
          exact Nat.not_lt_of_ge this hd

/-- Canonical binary encoding of `n : ℕ` as a `BinString`. -/
def natToBinString (n : ℕ) : BinString :=
  (Nat.digits 2 n).map digitToBool

/-- Left inverse of `natToBinString`, used only to prove injectivity. -/
def binStringToNat (xs : BinString) : ℕ :=
  Nat.ofDigits 2 (xs.map boolToDigit)

lemma binStringToNat_natToBinString (n : ℕ) : binStringToNat (natToBinString n) = n := by
  classical
  unfold binStringToNat natToBinString
  -- Reduce to a statement about `Nat.digits 2 n`.
  have hmap :
      (Nat.digits 2 n).map (fun d => boolToDigit (digitToBool d)) = Nat.digits 2 n := by
    -- Show the map is pointwise the identity on the digits list.
    have :
        (Nat.digits 2 n).map (fun d => boolToDigit (digitToBool d)) =
          (Nat.digits 2 n).map id := by
      apply List.map_congr_left
      intro d hd
      have hd2 : d < 2 := by
        -- Digits are always < base (here base = 2).
        exact Nat.digits_lt_base (b := 2) (m := n) (d := d) (by decide) hd
      simpa using (boolToDigit_digitToBool_of_lt_two (d := d) hd2)
    simpa using this
  -- Apply `Nat.ofDigits` and use `Nat.ofDigits_digits`.
  calc
    Nat.ofDigits 2 ((Nat.digits 2 n).map digitToBool |>.map boolToDigit)
        = Nat.ofDigits 2 ((Nat.digits 2 n).map (fun d => boolToDigit (digitToBool d))) := by
            -- Expand the nested `map` and use `List.map_map`.
            rw [List.map_map]
            rfl
    _ = Nat.ofDigits 2 (Nat.digits 2 n) := by simp [hmap]
    _ = n := Nat.ofDigits_digits 2 n

lemma natToBinString_injective : Function.Injective natToBinString := by
  -- `binStringToNat` is a left inverse.
  have hleft : Function.LeftInverse binStringToNat natToBinString := by
    intro n
    exact binStringToNat_natToBinString n
  exact hleft.injective

/-- Encode a `Nat.Partrec.Code` as a binary string (injectively). -/
def codeToBinString (c : Nat.Partrec.Code) : BinString :=
  natToBinString (Encodable.encode c)

lemma codeToBinString_injective : Function.Injective codeToBinString := by
  intro c₁ c₂ h
  have hNat : Encodable.encode c₁ = Encodable.encode c₂ := by
    apply natToBinString_injective
    simpa [codeToBinString] using h
  exact Encodable.encode_injective hNat

/-! ## Environment complexity `K(μ)` (Hutter-style)

We define the complexity of a lower-semicomputable environment `μ` as the minimum prefix-free
complexity of a code witnessing `μ` in the Levin/Hutter semimeasure enumeration.

This is the natural constant that appears in Hutter’s V3 bound `Dₙ(μ‖M) ≤ K(μ) * log 2`.
-/

/-- Codes `c` that enumerate the semimeasure `μ.toSemimeasure`. -/
def codesFor (μ : PrefixMeasure) : Set Nat.Partrec.Code :=
  {c | HutterEnumerationTheoremSemimeasure.evalLSC c = μ.toSemimeasure}

/-- Complexity of a code, measured via `Kpf` after encoding it as a binary string. -/
noncomputable def codeK (U : PrefixFreeMachine) [UniversalPFM U] (c : Nat.Partrec.Code) : ℕ :=
  KolmogorovComplexity.prefixComplexity U (codeToBinString c)

/-- Environment complexity: the minimum `codeK` among all codes enumerating `μ`.

For non‑LSC `μ` this set may be empty, in which case `sInf` returns `0`; all theorems using
`Kμ` assume lower semicomputability and thus nonemptiness. -/
noncomputable def Kμ (U : PrefixFreeMachine) [UniversalPFM U] (μ : PrefixMeasure) : ℕ :=
  sInf (codeK (U := U) '' codesFor μ)

theorem codesFor_nonempty (μ : PrefixMeasure)
    (hμ : HutterEnumeration.LowerSemicomputablePrefixMeasure μ) :
    (codesFor μ).Nonempty := by
  -- Use the concrete semimeasure enumeration theorem to obtain a code for `μ.toSemimeasure`.
  have hμ_sem :
      HutterEnumeration.LowerSemicomputableSemimeasure μ.toSemimeasure := by
    simpa [HutterEnumeration.LowerSemicomputableSemimeasure,
      HutterEnumeration.LowerSemicomputablePrefixMeasure] using hμ
  rcases
      HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration.surj_eval μ.toSemimeasure hμ_sem
    with ⟨code, hcode⟩
  refine ⟨code, ?_⟩
  simpa [codesFor] using hcode

theorem image_codeK_nonempty (U : PrefixFreeMachine) [UniversalPFM U] (μ : PrefixMeasure)
    (hμ : HutterEnumeration.LowerSemicomputablePrefixMeasure μ) :
    (codeK (U := U) '' codesFor μ).Nonempty := by
  rcases codesFor_nonempty (μ := μ) hμ with ⟨code, hcode⟩
  refine ⟨codeK (U := U) code, ?_⟩
  exact ⟨code, hcode, rfl⟩

theorem exists_code_of_minK (U : PrefixFreeMachine) [UniversalPFM U] (μ : PrefixMeasure)
    (hμ : HutterEnumeration.LowerSemicomputablePrefixMeasure μ) :
    ∃ code : Nat.Partrec.Code,
      code ∈ codesFor μ ∧ codeK (U := U) code = Kμ (U := U) μ := by
  classical
  -- Since `ℕ` is well-ordered, `sInf` of a nonempty set is attained.
  have hne : (codeK (U := U) '' codesFor μ).Nonempty := image_codeK_nonempty (U := U) (μ := μ) hμ
  have hmem : Kμ (U := U) μ ∈ (codeK (U := U) '' codesFor μ) := Nat.sInf_mem (s := _) hne
  rcases hmem with ⟨code, hcode, hk⟩
  refine ⟨code, hcode, ?_⟩
  simpa [Kμ] using hk

/-! ## V3 weights and the universal mixture `M₃` -/

/-- V3 weight for codes: pull back `kpfWeight` along `codeToBinString`. -/
noncomputable def codeWeight (U : PrefixFreeMachine) [UniversalPFM U] (c : Nat.Partrec.Code) :
    ENNReal :=
  kpfWeight (U := U) (codeToBinString c)

theorem tsum_codeWeight_le_one (U : PrefixFreeMachine) [UniversalPFM U] :
    (∑' c : Nat.Partrec.Code, codeWeight (U := U) c) ≤ 1 := by
  have hsub :
      (∑' c : Nat.Partrec.Code, codeWeight (U := U) c) ≤
        ∑' x : BinString, kpfWeight (U := U) x := by
    simpa [codeWeight] using
      (ENNReal.tsum_comp_le_tsum_of_injective (f := codeToBinString)
        codeToBinString_injective (g := fun x : BinString => kpfWeight (U := U) x))
  exact hsub.trans (tsum_kpfWeight_le_one (U := U))

/-- `M₃`: the Hutter V3 universal semimeasure using `2^{-Kpf}` weights on the **semimeasure**
enumeration. -/
noncomputable def M₃ (U : PrefixFreeMachine) [UniversalPFM U] : Semimeasure :=
  xiSemimeasure
    (ν := fun c : Nat.Partrec.Code => HutterEnumerationTheoremSemimeasure.evalLSC c)
    (w := codeWeight (U := U))
    (hw := tsum_codeWeight_le_one (U := U))

/-! ## Regret bounds in the “`K * log 2`” form -/

theorem log_inv_two_zpow_neg (K : ℕ) :
    Real.log (1 / ((2 : ENNReal) ^ (-(K : ℤ))).toReal) = (K : ℝ) * Real.log 2 := by
  simp only [one_div]
  rw [Real.log_inv]
  conv_lhs =>
    rw [ENNReal.zpow_neg]
  rw [ENNReal.toReal_inv, Real.log_inv, neg_neg]
  rw [zpow_natCast, ENNReal.toReal_pow]
  simp [Real.log_pow]

theorem log_inv_codeWeight (U : PrefixFreeMachine) [UniversalPFM U] (c : Nat.Partrec.Code) :
    Real.log (1 / (codeWeight (U := U) c).toReal) =
      (KolmogorovComplexity.prefixComplexity U (codeToBinString c) : ℝ) * Real.log 2 := by
  simpa [codeWeight, kpfWeight] using
    (log_inv_two_zpow_neg (K := KolmogorovComplexity.prefixComplexity U (codeToBinString c)))

theorem log_inv_codeWeight' (U : PrefixFreeMachine) [UniversalPFM U] (c : Nat.Partrec.Code) :
    -Real.log (codeWeight (U := U) c).toReal =
      (KolmogorovComplexity.prefixComplexity U (codeToBinString c) : ℝ) * Real.log 2 := by
  have h := log_inv_codeWeight (U := U) c
  simpa [one_div] using h

theorem relEntropy_le_codeK_log2_of_code (U : PrefixFreeMachine) [UniversalPFM U] (μ : PrefixMeasure)
    (code : Nat.Partrec.Code) (hcode : HutterEnumerationTheoremSemimeasure.evalLSC code = μ.toSemimeasure)
    (n : ℕ) :
    relEntropy μ (M₃ (U := U)) n ≤ (codeK (U := U) code : ℝ) * Real.log 2 := by
  -- Dominance for a particular enumerated component is trivial for a mixture.
  have hdom : Dominates (M₃ (U := U)) μ (codeWeight (U := U) code) := by
    intro x
    have hdom' :
        codeWeight (U := U) code *
            (HutterEnumerationTheoremSemimeasure.evalLSC code) x ≤
          (M₃ (U := U)) x := by
      simpa [M₃] using
        (xiSemimeasure_dominates_index
          (ν := fun c : Nat.Partrec.Code => HutterEnumerationTheoremSemimeasure.evalLSC c)
          (w := codeWeight (U := U))
          (hw := tsum_codeWeight_le_one (U := U))
          code x)
    have hμx : HutterEnumerationTheoremSemimeasure.evalLSC code x = μ x := by
      have := congrArg (fun ξ : Semimeasure => ξ x) hcode
      simpa [PrefixMeasure.toSemimeasure_apply] using this
    simpa [hμx] using hdom'
  have hc0 : codeWeight (U := U) code ≠ 0 := by
    unfold codeWeight kpfWeight
    have hne0 : (2 : ENNReal) ≠ 0 := by norm_num
    have hneTop : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
    exact ne_of_gt (ENNReal.zpow_pos hne0 hneTop _)
  have hbound :=
    relEntropy_le_log_inv_of_dominates (μ := μ) (ξ := M₃ (U := U)) (hdom := hdom) (hc0 := hc0) n
  -- Rewrite the RHS to `codeK`.
  have hlog' := log_inv_codeWeight' (U := U) code
  simpa [codeK, hlog'] using hbound

theorem relEntropy_le_Kμ_log2 (U : PrefixFreeMachine) [UniversalPFM U] (μ : PrefixMeasure)
    (hμ : HutterEnumeration.LowerSemicomputablePrefixMeasure μ) (n : ℕ) :
    relEntropy μ (M₃ (U := U)) n ≤ (Kμ (U := U) μ : ℝ) * Real.log 2 := by
  rcases exists_code_of_minK (U := U) (μ := μ) hμ with ⟨code, hcode, hk⟩
  have hcode' : HutterEnumerationTheoremSemimeasure.evalLSC code = μ.toSemimeasure := hcode
  -- Apply the code-level bound and rewrite by the choice of minimal complexity.
  simpa [hk] using (relEntropy_le_codeK_log2_of_code (U := U) (μ := μ) (code := code) hcode' n)

/-! ## Invariance (machine robustness)

Hutter’s V3 constants are machine-dependent but only up to an additive constant.

We prove this for `Kμ`: switching between universal prefix-free machines changes `Kμ` by at most a
constant independent of `μ`.
-/

theorem codeK_le_codeK_add_const (U V : PrefixFreeMachine) [UniversalPFM U] [UniversalPFM V]
    (c : Nat.Partrec.Code) :
    codeK (U := U) c ≤ codeK (U := V) c + Classical.choose (KolmogorovComplexity.invariance_Kpf U V) :=
  (Classical.choose_spec (KolmogorovComplexity.invariance_Kpf U V)) (codeToBinString c)

theorem Kμ_le_Kμ_add (U V : PrefixFreeMachine) [UniversalPFM U] [UniversalPFM V]
    (μ : PrefixMeasure) (hμ : HutterEnumeration.LowerSemicomputablePrefixMeasure μ) :
    Kμ (U := U) μ ≤ Kμ (U := V) μ + Classical.choose (KolmogorovComplexity.invariance_Kpf U V) := by
  classical
  -- Pick a code achieving `Kμ(V,μ)` and compare code complexities using invariance of `Kpf`.
  rcases exists_code_of_minK (U := V) (μ := μ) hμ with ⟨code, hcode, hkV⟩
  have hInfU : Kμ (U := U) μ ≤ codeK (U := U) code := by
    -- `codeK U code` is in the image set defining `Kμ(U,μ)`.
    have hm : codeK (U := U) code ∈ codeK (U := U) '' codesFor μ := ⟨code, hcode, rfl⟩
    simpa [Kμ] using (Nat.sInf_le (s := codeK (U := U) '' codesFor μ) hm)
  have hcmp : codeK (U := U) code ≤ codeK (U := V) code + Classical.choose (KolmogorovComplexity.invariance_Kpf U V) :=
    codeK_le_codeK_add_const (U := U) (V := V) code
  -- Combine and rewrite `codeK(V,code)` to `Kμ(V,μ)` using `hkV`.
  have : Kμ (U := U) μ ≤ Kμ (U := V) μ + Classical.choose (KolmogorovComplexity.invariance_Kpf U V) := by
    calc
      Kμ (U := U) μ ≤ codeK (U := U) code := hInfU
      _ ≤ codeK (U := V) code + Classical.choose (KolmogorovComplexity.invariance_Kpf U V) := hcmp
      _ = Kμ (U := V) μ + Classical.choose (KolmogorovComplexity.invariance_Kpf U V) := by simp [hkV]
  exact this

theorem invariance_Kμ (U V : PrefixFreeMachine) [UniversalPFM U] [UniversalPFM V] :
    ∃ c : ℕ, ∀ μ : PrefixMeasure,
      HutterEnumeration.LowerSemicomputablePrefixMeasure μ →
        Kμ (U := U) μ ≤ Kμ (U := V) μ + c ∧ Kμ (U := V) μ ≤ Kμ (U := U) μ + c := by
  classical
  -- Get one-sided invariance constants from `invariance_Kpf` and take the max.
  let cUV : ℕ := Classical.choose (KolmogorovComplexity.invariance_Kpf U V)
  let cVU : ℕ := Classical.choose (KolmogorovComplexity.invariance_Kpf V U)
  refine ⟨Nat.max cUV cVU, ?_⟩
  intro μ hμ
  constructor
  · have h := Kμ_le_Kμ_add (U := U) (V := V) (μ := μ) hμ
    exact h.trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  · have h := Kμ_le_Kμ_add (U := V) (V := U) (μ := μ) hμ
    exact h.trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)

/-! ## “Occam factor” dominance in the `2^{-K(μ)}` form -/

theorem dominates_M₃_of_code (U : PrefixFreeMachine) [UniversalPFM U] (μ : PrefixMeasure)
    (code : Nat.Partrec.Code) (hcode : HutterEnumerationTheoremSemimeasure.evalLSC code = μ.toSemimeasure) :
    Dominates (M₃ (U := U)) μ (codeWeight (U := U) code) := by
  intro x
  have hdom' :
      codeWeight (U := U) code *
          (HutterEnumerationTheoremSemimeasure.evalLSC code) x ≤
        (M₃ (U := U)) x := by
    simpa [M₃] using
      (xiSemimeasure_dominates_index
        (ν := fun c : Nat.Partrec.Code => HutterEnumerationTheoremSemimeasure.evalLSC c)
        (w := codeWeight (U := U))
        (hw := tsum_codeWeight_le_one (U := U))
        code x)
  have hμx : HutterEnumerationTheoremSemimeasure.evalLSC code x = μ x := by
    have := congrArg (fun ξ : Semimeasure => ξ x) hcode
    simpa [PrefixMeasure.toSemimeasure_apply] using this
  simpa [hμx] using hdom'

/-- Hutter’s V3 dominance statement in the canonical `2^{-K(μ)}` form. -/
theorem dominates_M₃_of_LSC_Kμ (U : PrefixFreeMachine) [UniversalPFM U] (μ : PrefixMeasure)
    (hμ : HutterEnumeration.LowerSemicomputablePrefixMeasure μ) :
    Dominates (M₃ (U := U)) μ ((2 : ENNReal) ^ (-(Kμ (U := U) μ : ℤ))) := by
  classical
  rcases exists_code_of_minK (U := U) (μ := μ) hμ with ⟨code, hcode, hk⟩
  have hdom : Dominates (M₃ (U := U)) μ (codeWeight (U := U) code) :=
    dominates_M₃_of_code (U := U) (μ := μ) (code := code) hcode
  have hwt : codeWeight (U := U) code = ((2 : ENNReal) ^ (-(Kμ (U := U) μ : ℤ))) := by
    -- `codeWeight = 2^{-codeK}` and `codeK = Kμ` for the minimizing code.
    have hk' :
        (KolmogorovComplexity.prefixComplexity U (codeToBinString code) : ℤ) =
          (Kμ (U := U) μ : ℤ) := by
      have hkNat :
          KolmogorovComplexity.prefixComplexity U (codeToBinString code) = Kμ (U := U) μ := by
        simpa [codeK] using hk
      exact congrArg (fun n : ℕ => (n : ℤ)) hkNat
    simp [codeWeight, kpfWeight, hk']
  simpa [hwt] using hdom

theorem relEntropy_le_codeKpf_log2_M₃ (U : PrefixFreeMachine) [UniversalPFM U] (μ : PrefixMeasure)
    (hμ : HutterEnumeration.LowerSemicomputablePrefixMeasure μ) (n : ℕ) :
    ∃ code : Nat.Partrec.Code,
      Dominates (M₃ (U := U)) μ (codeWeight (U := U) code) ∧
        relEntropy μ (M₃ (U := U)) n ≤
          (KolmogorovComplexity.prefixComplexity U (codeToBinString code) : ℝ) * Real.log 2 := by
  classical
  -- Treat `μ` as a lower-semicomputable semimeasure.
  have hμ_sem :
      HutterEnumeration.LowerSemicomputableSemimeasure μ.toSemimeasure := by
    simpa [HutterEnumeration.LowerSemicomputableSemimeasure,
      HutterEnumeration.LowerSemicomputablePrefixMeasure] using hμ
  obtain ⟨code, hcode⟩ :=
    HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration.surj_eval μ.toSemimeasure hμ_sem
  have hdom : Dominates (M₃ (U := U)) μ (codeWeight (U := U) code) := by
    intro x
    -- Dominance for the indexed component is trivial for a mixture.
    have hdom' :
        codeWeight (U := U) code *
            (HutterEnumerationTheoremSemimeasure.evalLSC code) x ≤
          (M₃ (U := U)) x := by
      simpa [M₃] using
        (xiSemimeasure_dominates_index
          (ν := fun c : Nat.Partrec.Code => HutterEnumerationTheoremSemimeasure.evalLSC c)
          (w := codeWeight (U := U))
          (hw := tsum_codeWeight_le_one (U := U))
          code x)
    -- Rewrite `evalLSC code` to `μ.toSemimeasure`, then drop the coercion.
    have hμx : HutterEnumerationTheoremSemimeasure.evalLSC code x = μ x := by
      have := congrArg (fun ξ : Semimeasure => ξ x) hcode
      simpa [PrefixMeasure.toSemimeasure_apply] using this
    simpa [hμx] using hdom'
  have hc0 : codeWeight (U := U) code ≠ 0 := by
    -- `kpfWeight` is a positive power of 2.
    unfold codeWeight kpfWeight
    have hne0 : (2 : ENNReal) ≠ 0 := by norm_num
    have hneTop : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
    exact ne_of_gt (ENNReal.zpow_pos hne0 hneTop _)
  have hbound :=
    relEntropy_le_log_inv_of_dominates (μ := μ) (ξ := M₃ (U := U)) (hdom := hdom) (hc0 := hc0) n
  refine ⟨code, hdom, ?_⟩
  -- Rewrite the RHS `log(1/c)` in terms of a Kpf length.
  have hlog : Real.log (1 / (codeWeight (U := U) code).toReal) =
      (KolmogorovComplexity.prefixComplexity U (codeToBinString code) : ℝ) * Real.log 2 :=
    log_inv_codeWeight (U := U) code
  -- `simp` tends to rewrite `log(1/·)` into `-log`, so we provide that form explicitly.
  have hlog' :
      -Real.log (codeWeight (U := U) code).toReal =
        (KolmogorovComplexity.prefixComplexity U (codeToBinString code) : ℝ) * Real.log 2 := by
    simpa [one_div] using hlog
  simpa [hlog'] using hbound

end HutterV3Kpf

end Mettapedia.Logic.UniversalPrediction
