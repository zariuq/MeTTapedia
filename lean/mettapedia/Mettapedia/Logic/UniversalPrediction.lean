import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mettapedia.Computability.KolmogorovComplexity.PrefixComplexity
import Mettapedia.Logic.SolomonoffInduction

/-!
# Universal Sequence Prediction (Hutter 2005, Chapter 3)

This file starts the Chapter 3 development around *mixtures* of (semi)measures.

The key construction is the universal mixture

`ξ(x) := ∑' i, w i * ν i x`

where `ν i` ranges over a (countable) family of semimeasures and the weights `w i`
sum to at most 1. This gives a semimeasure `ξ` that (trivially) dominates each component.

This is designed to be the bridge from:
- Chapter 2: semimeasures and Solomonoff's `M`
- Chapter 3: universal prediction bounds based on dominance

Later, we will specialize `w i` to algorithmic weights such as `2^{-K(i)}` once
prefix-free Kolmogorov complexity is available.
-/

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical
open scoped BigOperators

open Mettapedia.Logic.SolomonoffPrior
open Mettapedia.Logic.SolomonoffInduction

abbrev BinString := Mettapedia.Logic.SolomonoffPrior.BinString
abbrev Semimeasure := Mettapedia.Logic.SolomonoffInduction.Semimeasure

/-! ## Algorithmic-style weights

Hutter’s universal mixture uses weights of the form `2^{-K(·)}` (prefix-free complexity).

For now, we provide:
1. A **provably summable** self-delimiting baseline `geometricWeight i = 2^{-(i+1)}`
2. A **provably summable** `encodeWeight` based on `Encodable.encode` (works for any countable index)
3. An **algorithmic weight** `kpfWeight` based on prefix-free Kolmogorov complexity `Kpf`,
   together with a Kraft/summability lemma.
-/

/-- A simple self-delimiting weight sequence: `w(i) = 2^{-(i+1)}`. -/
noncomputable def geometricWeight (i : ℕ) : ENNReal :=
  2 ^ (-1 - (i : ℤ))

theorem tsum_geometricWeight : (∑' i : ℕ, geometricWeight i) = 1 := by
  simpa [geometricWeight] using ENNReal.tsum_two_zpow_neg_add_one

theorem tsum_geometricWeight_le_one : (∑' i : ℕ, geometricWeight i) ≤ 1 := by
  simp [tsum_geometricWeight]

/-- A canonical “countable prior” weight based on `Encodable.encode`:

`w(i) := 2^{- (encode i + 1)}`.

This is not yet the full Hutter weight `2^{-K(i)}`, but it is a useful, provably summable
baseline for *any* countable family indexed by an `Encodable` type. -/
noncomputable def encodeWeight {ι : Type*} [Encodable ι] (i : ι) : ENNReal :=
  (2⁻¹ : ENNReal) ^ (Encodable.encode i + 1)

theorem tsum_encodeWeight_le_one {ι : Type*} [Encodable ι] :
    (∑' i : ι, encodeWeight i) ≤ 1 := by
  classical
  unfold encodeWeight
  have h := (ENNReal.tsum_geometric_two_encode_le_two (ι := ι))
  have hEq :
      (∑' i : ι, (2⁻¹ : ENNReal) ^ (Encodable.encode i + 1)) =
        (∑' i : ι, (2⁻¹ : ENNReal) ^ Encodable.encode i) * (2⁻¹ : ENNReal) := by
    calc
      (∑' i : ι, (2⁻¹ : ENNReal) ^ (Encodable.encode i + 1)) =
          ∑' i : ι, (2⁻¹ : ENNReal) ^ Encodable.encode i * (2⁻¹ : ENNReal) := by
            refine tsum_congr ?_
            intro i
            simp [pow_succ]
      _ = (∑' i : ι, (2⁻¹ : ENNReal) ^ Encodable.encode i) * (2⁻¹ : ENNReal) := by
            simpa using
              (ENNReal.tsum_mul_right
                (f := fun i : ι => (2⁻¹ : ENNReal) ^ Encodable.encode i) (a := (2⁻¹ : ENNReal)))
  rw [hEq]
  have hmul :
      (∑' i : ι, (2⁻¹ : ENNReal) ^ Encodable.encode i) * (2⁻¹ : ENNReal) ≤
        (2 : ENNReal) * (2⁻¹ : ENNReal) :=
    mul_le_mul_of_nonneg_right h (by simp)
  refine hmul.trans_eq ?_
  have h2ne0 : (2 : ENNReal) ≠ 0 := by norm_num
  have h2neinf : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
  simpa using (ENNReal.mul_inv_cancel h2ne0 h2neinf)

/-- Algorithmic weights using prefix-free Kolmogorov complexity `Kpf`. -/
noncomputable def kpfWeight (U : PrefixFreeMachine) [UniversalPFM U] (x : BinString) : ENNReal :=
  (2 : ENNReal) ^ (-(KolmogorovComplexity.prefixComplexity U x : ℤ))

theorem tsum_kpfWeight_le_one (U : PrefixFreeMachine) [UniversalPFM U] :
    (∑' x : BinString, kpfWeight (U := U) x) ≤ 1 := by
  simpa [kpfWeight] using (KolmogorovComplexity.tsum_weightByKpf_le_one_ennreal (U := U))

/-! ## Universal mixtures -/

/-- Weighted mixture of semimeasures, `ξ(x) := ∑' i, w i * ν i x`. -/
noncomputable def xiFun {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal) (x : BinString) :
    ENNReal :=
  ∑' i, w i * ν i x

/-- Trivial dominance: a term is bounded by the full mixture. -/
theorem xi_dominates_index {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal) (i : ι)
    (x : BinString) :
    w i * ν i x ≤ xiFun ν w x := by
  unfold xiFun
  simpa using (ENNReal.le_tsum (f := fun j => w j * ν j x) i)

/-- The mixture preserves the semimeasure (superadditivity) inequality. -/
theorem xi_superadditive {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal) (x : BinString) :
    xiFun ν w (x ++ [false]) + xiFun ν w (x ++ [true]) ≤ xiFun ν w x := by
  unfold xiFun
  have hsum :
      (∑' i, w i * ν i (x ++ [false])) + (∑' i, w i * ν i (x ++ [true])) =
        ∑' i, (w i * ν i (x ++ [false]) + w i * ν i (x ++ [true])) := by
    simpa using
      (ENNReal.tsum_add (f := fun i => w i * ν i (x ++ [false]))
        (g := fun i => w i * ν i (x ++ [true]))).symm
  calc
    (∑' i, w i * ν i (x ++ [false])) + (∑' i, w i * ν i (x ++ [true]))
        = ∑' i, (w i * ν i (x ++ [false]) + w i * ν i (x ++ [true])) := hsum
    _ ≤ ∑' i, w i * ν i x := by
        refine ENNReal.tsum_le_tsum ?_
        intro i
        calc
          w i * ν i (x ++ [false]) + w i * ν i (x ++ [true])
              = w i * (ν i (x ++ [false]) + ν i (x ++ [true])) := by simp [mul_add]
          _ ≤ w i * ν i x := by
              exact mul_le_mul_right ((ν i).superadditive' x) (w i)

/-- The mixture root mass is bounded by the sum of weights. -/
theorem xi_root_le_tsum_weights {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal) :
    xiFun ν w [] ≤ ∑' i, w i := by
  unfold xiFun
  have hterm : ∀ i, w i * ν i [] ≤ w i := by
    intro i
    simpa using (mul_le_mul_right ((ν i).root_le_one') (w i))
  simpa using (ENNReal.tsum_le_tsum hterm)

/-- If the weights sum to at most 1, the mixture is a semimeasure. -/
noncomputable def xiSemimeasure {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal)
    (hw : (∑' i, w i) ≤ 1) : Semimeasure :=
  { toFun := xiFun ν w
    superadditive' := xi_superadditive ν w
    root_le_one' := (xi_root_le_tsum_weights ν w).trans hw }

/-! ## Dominance -/

/-- `ξ` dominates `ν` with constant `c` if `c * ν(x) ≤ ξ(x)` for all `x`. -/
def Dominates (ξ ν : BinString → ENNReal) (c : ENNReal) : Prop :=
  ∀ x : BinString, c * ν x ≤ ξ x

theorem Dominates.le_div {ξ ν : BinString → ENNReal} {c : ENNReal} (h : Dominates ξ ν c)
    (hc0 : c ≠ 0) (hcTop : c ≠ (⊤ : ENNReal)) (x : BinString) :
    ν x ≤ ξ x / c := by
  have hmul : ν x * c ≤ ξ x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h x
  exact (ENNReal.le_div_iff_mul_le (a := ν x) (b := c) (c := ξ x) (Or.inl hc0) (Or.inl hcTop)).2
    hmul

theorem Dominates.eq_zero_of_eq_zero {ξ ν : BinString → ENNReal} {c : ENNReal} (h : Dominates ξ ν c)
    (hc0 : c ≠ 0) (x : BinString) (hx : ξ x = 0) : ν x = 0 := by
  have hle : c * ν x ≤ 0 := by simpa [hx] using h x
  have heq : c * ν x = 0 := le_antisymm hle (by simp)
  rcases mul_eq_zero.1 heq with hc | hν
  · exact (hc0 hc).elim
  · exact hν

theorem xiSemimeasure_dominates_index {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (i : ι) :
    Dominates (xiSemimeasure ν w hw) (ν i) (w i) := by
  intro x
  simpa [xiSemimeasure] using xi_dominates_index ν w i x

theorem xiSemimeasure_le_one {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (x : BinString) :
    (xiSemimeasure ν w hw) x ≤ 1 := by
  have hmono : (xiSemimeasure ν w hw) x ≤ (xiSemimeasure ν w hw) [] := by
    simpa using (xiSemimeasure ν w hw).mono_append [] x
  exact hmono.trans (xiSemimeasure ν w hw).root_le_one'

theorem xiSemimeasure_ne_top {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (x : BinString) :
    (xiSemimeasure ν w hw) x ≠ (⊤ : ENNReal) := by
  have hle : (xiSemimeasure ν w hw) x ≤ 1 := xiSemimeasure_le_one ν w hw x
  have htop : (1 : ENNReal) < ⊤ := by simp
  have : (xiSemimeasure ν w hw) x < ⊤ := lt_of_le_of_lt hle htop
  exact (lt_top_iff_ne_top).1 this

theorem semimeasure_le_one (μ : Semimeasure) (x : BinString) : μ x ≤ 1 := by
  have hmono : μ x ≤ μ [] := by
    simpa using μ.mono_append [] x
  exact hmono.trans μ.root_le_one'

theorem semimeasure_ne_top (μ : Semimeasure) (x : BinString) : μ x ≠ (⊤ : ENNReal) := by
  have hle : μ x ≤ 1 := semimeasure_le_one μ x
  have htop : (1 : ENNReal) < ⊤ := by simp
  have : μ x < ⊤ := lt_of_le_of_lt hle htop
  exact (lt_top_iff_ne_top).1 this

/-! ## Posterior weights (Bayesian update for mixtures) -/

/-- Posterior weight after observing prefix `x`:

`w(i | x) := w(i) * νᵢ(x) / ξ(x)`, and `0` if `ξ(x)=0`. -/
noncomputable def posteriorWeight {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal)
    (x : BinString) (i : ι) : ENNReal :=
  if xiFun ν w x = 0 then 0 else (w i * ν i x) / xiFun ν w x

theorem tsum_posteriorWeight {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (x : BinString) :
    (∑' i : ι, posteriorWeight ν w x i) = if xiFun ν w x = 0 then 0 else 1 := by
  classical
  by_cases hx0 : xiFun ν w x = 0
  · simp [posteriorWeight, hx0]
  · have hxTop : xiFun ν w x ≠ (⊤ : ENNReal) := by
      have hle : (xiFun ν w x) ≤ 1 := by
        simpa [xiSemimeasure] using xiSemimeasure_le_one ν w hw x
      have htop : (1 : ENNReal) < ⊤ := by simp
      have : xiFun ν w x < ⊤ := lt_of_le_of_lt hle htop
      exact (lt_top_iff_ne_top).1 this
    have htsum :
        (∑' i : ι, posteriorWeight ν w x i) = (∑' i : ι, (w i * ν i x) / xiFun ν w x) := by
      refine tsum_congr ?_
      intro i
      simp [posteriorWeight, hx0]
    have hsum :
        (∑' i : ι, posteriorWeight ν w x i) = 1 := by
      calc
        (∑' i : ι, posteriorWeight ν w x i)
            = (∑' i : ι, (w i * ν i x) / xiFun ν w x) := htsum
        _ = (∑' i : ι, w i * ν i x) / xiFun ν w x := by
              simp [div_eq_mul_inv, ENNReal.tsum_mul_right]
        _ = xiFun ν w x / xiFun ν w x := by
              simp [xiFun]
        _ = 1 := by
              simp [div_eq_mul_inv, ENNReal.mul_inv_cancel hx0 hxTop]
    simp [hx0, hsum]

/-! ## Mixture conditionals -/

/-- ENNReal-valued conditional probability for a semimeasure:
`μ(y|x) := μ(xy) / μ(x)` (well-defined since `μ(xy) = 0` when `μ(x) = 0`). -/
noncomputable def conditionalENN (μ : Semimeasure) (y x : BinString) : ENNReal :=
  μ (x ++ y) / μ x

theorem conditionalENN_eq_zero_of_eq_zero (μ : Semimeasure) (x y : BinString) (hx : μ x = 0) :
    conditionalENN μ y x = 0 := by
  unfold conditionalENN
  have hxy : μ (x ++ y) = 0 := by
    have hle : μ (x ++ y) ≤ μ x := μ.mono_append x y
    have hle0 : μ (x ++ y) ≤ 0 := by simpa [hx] using hle
    exact le_antisymm hle0 (by simp)
  simp [hx, hxy]

theorem xiFun_eq_zero_of_eq_zero {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal)
    (x y : BinString) (hx : xiFun ν w x = 0) : xiFun ν w (x ++ y) = 0 := by
  unfold xiFun at hx ⊢
  have hterm0 : ∀ i : ι, w i * ν i x = 0 := (ENNReal.tsum_eq_zero).1 hx
  refine (ENNReal.tsum_eq_zero).2 ?_
  intro i
  have hmono : ν i (x ++ y) ≤ ν i x := (ν i).mono_append x y
  have hle : w i * ν i (x ++ y) ≤ w i * ν i x := mul_le_mul_right hmono (w i)
  have : w i * ν i (x ++ y) ≤ 0 := by simpa [hterm0 i] using hle
  exact le_antisymm this (by simp)

theorem xi_conditionalENN_eq_tsum_posterior_mul {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal)
    (x y : BinString) :
    xiFun ν w (x ++ y) / xiFun ν w x =
      ∑' i : ι, posteriorWeight ν w x i * conditionalENN (ν i) y x := by
  classical
  by_cases hx0 : xiFun ν w x = 0
  · have hxy0 : xiFun ν w (x ++ y) = 0 := xiFun_eq_zero_of_eq_zero ν w x y hx0
    simp [posteriorWeight, conditionalENN, hx0, hxy0]
  · have htsum :
        (∑' i : ι, posteriorWeight ν w x i * conditionalENN (ν i) y x) =
          ∑' i : ι, (w i * ν i (x ++ y)) / xiFun ν w x := by
      refine tsum_congr ?_
      intro i
      have hcancel :
          ν i x * (ν i (x ++ y) / ν i x) = ν i (x ++ y) := by
        refine ENNReal.mul_div_cancel' ?_ ?_
        · intro hix0
          have hle : ν i (x ++ y) ≤ ν i x := (ν i).mono_append x y
          have hle0 : ν i (x ++ y) ≤ 0 := by simpa [hix0] using hle
          exact le_antisymm hle0 (by simp)
        · intro hixTop
          have hne : ν i x ≠ (⊤ : ENNReal) := semimeasure_ne_top (ν i) x
          exact (hne hixTop).elim
      calc
        posteriorWeight ν w x i * conditionalENN (ν i) y x
            = ((w i * ν i x) / xiFun ν w x) * (ν i (x ++ y) / ν i x) := by
                simp [posteriorWeight, conditionalENN, hx0]
        _ = (w i / xiFun ν w x) * (ν i x * (ν i (x ++ y) / ν i x)) := by
                simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        _ = (w i / xiFun ν w x) * ν i (x ++ y) := by
                simp [hcancel]
        _ = (w i * ν i (x ++ y)) / xiFun ν w x := by
                simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    calc
      xiFun ν w (x ++ y) / xiFun ν w x
          = (∑' i : ι, w i * ν i (x ++ y)) / xiFun ν w x := by simp [xiFun]
      _ = ∑' i : ι, (w i * ν i (x ++ y)) / xiFun ν w x := by
            simp [div_eq_mul_inv, ENNReal.tsum_mul_right]
      _ = ∑' i : ι, posteriorWeight ν w x i * conditionalENN (ν i) y x := by
            simpa using htsum.symm

/-- The canonical Chapter‑3 mixture `ξ` using `geometricWeight`, yielding a semimeasure
without any additional assumptions. -/
noncomputable def xiGeomSemimeasure (ν : ℕ → Semimeasure) : Semimeasure :=
  xiSemimeasure ν geometricWeight tsum_geometricWeight_le_one

theorem xiGeom_dominates_index (ν : ℕ → Semimeasure) (i : ℕ) (x : BinString) :
    geometricWeight i * ν i x ≤ (xiGeomSemimeasure ν) x := by
  simpa [xiGeomSemimeasure] using xi_dominates_index ν geometricWeight i x

/-! ## The `encodeWeight` mixture -/

/-- Universal mixture with `encodeWeight`, defined for any countable (Encodable) index type. -/
noncomputable def xiEncodeSemimeasure {ι : Type*} [Encodable ι] (ν : ι → Semimeasure) :
    Semimeasure :=
  xiSemimeasure ν (encodeWeight (ι := ι)) (tsum_encodeWeight_le_one (ι := ι))

theorem xiEncode_dominates_index {ι : Type*} [Encodable ι] (ν : ι → Semimeasure) (i : ι)
    (x : BinString) :
    encodeWeight i * ν i x ≤ (xiEncodeSemimeasure (ι := ι) ν) x := by
  simpa [xiEncodeSemimeasure] using xi_dominates_index ν (encodeWeight (ι := ι)) i x

/-! ## The `Kpf` mixture -/

/-- Universal mixture over a `BinString`-indexed family, using the `2^{-Kpf}` weights. -/
noncomputable def xiKpfSemimeasure (U : PrefixFreeMachine) [UniversalPFM U]
    (ν : BinString → Semimeasure) : Semimeasure :=
  xiSemimeasure ν (kpfWeight (U := U)) (tsum_kpfWeight_le_one (U := U))

theorem xiKpf_dominates_index (U : PrefixFreeMachine) [UniversalPFM U]
    (ν : BinString → Semimeasure) (i : BinString) (x : BinString) :
    kpfWeight (U := U) i * ν i x ≤ (xiKpfSemimeasure (U := U) ν) x := by
  simpa [xiKpfSemimeasure] using xi_dominates_index ν (kpfWeight (U := U)) i x

/-! ### Invariance (machine-independence) of `2^{-Kpf}` weights -/

theorem kpfWeight_mul_le_of_invariance (U V : PrefixFreeMachine) [UniversalPFM U] [UniversalPFM V] :
    ∃ c : ℕ, ∀ x : BinString,
      kpfWeight (U := V) x * (2 : ENNReal) ^ (-(c : ℤ)) ≤ kpfWeight (U := U) x := by
  classical
  obtain ⟨c, hc⟩ := KolmogorovComplexity.invariance_Kpf (U := U) (V := V)
  refine ⟨c, ?_⟩
  intro x
  have hK : KolmogorovComplexity.prefixComplexity U x ≤ KolmogorovComplexity.prefixComplexity V x + c := hc x
  have hKInt :
      (KolmogorovComplexity.prefixComplexity U x : ℤ) ≤
        (KolmogorovComplexity.prefixComplexity V x + c : ℤ) :=
    (Int.ofNat_le).2 hK
  have hExp :
      (-(KolmogorovComplexity.prefixComplexity V x + c : ℤ)) ≤
        -(KolmogorovComplexity.prefixComplexity U x : ℤ) :=
    Int.neg_le_neg hKInt
  have h2le : (1 : ENNReal) ≤ 2 := by simp
  have h2ne0 : (2 : ENNReal) ≠ 0 := by norm_num
  have h2neTop : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
  have hProd :
      kpfWeight (U := V) x * (2 : ENNReal) ^ (-(c : ℤ)) =
        (2 : ENNReal) ^ (-(KolmogorovComplexity.prefixComplexity V x + c : ℤ)) := by
    unfold kpfWeight
    have hExpEq :
        (-(KolmogorovComplexity.prefixComplexity V x : ℤ)) + (-(c : ℤ)) =
          -(KolmogorovComplexity.prefixComplexity V x + c : ℤ) := by
      simpa using
        (Int.neg_add (a := (KolmogorovComplexity.prefixComplexity V x : ℤ)) (b := (c : ℤ))).symm
    calc
      (2 : ENNReal) ^ (-(KolmogorovComplexity.prefixComplexity V x : ℤ)) *
            (2 : ENNReal) ^ (-(c : ℤ))
          = (2 : ENNReal) ^ (-(KolmogorovComplexity.prefixComplexity V x : ℤ) + -(c : ℤ)) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                (ENNReal.zpow_add (x := (2 : ENNReal)) h2ne0 h2neTop
                  (-(KolmogorovComplexity.prefixComplexity V x : ℤ)) (-(c : ℤ))).symm
      _ = (2 : ENNReal) ^ (-(KolmogorovComplexity.prefixComplexity V x + c : ℤ)) := by
              simp [hExpEq]
  calc
    kpfWeight (U := V) x * (2 : ENNReal) ^ (-(c : ℤ))
        = (2 : ENNReal) ^ (-(KolmogorovComplexity.prefixComplexity V x + c : ℤ)) := hProd
    _ ≤ (2 : ENNReal) ^ (-(KolmogorovComplexity.prefixComplexity U x : ℤ)) := by
        exact ENNReal.zpow_le_of_le h2le hExp
    _ = kpfWeight (U := U) x := by
        simp [kpfWeight]

theorem xiKpfSemimeasure_mul_le_of_invariance (U V : PrefixFreeMachine) [UniversalPFM U] [UniversalPFM V]
    (ν : BinString → Semimeasure) :
    ∃ c : ℕ, ∀ x : BinString,
      (2 : ENNReal) ^ (-(c : ℤ)) * (xiKpfSemimeasure (U := V) ν) x ≤
        (xiKpfSemimeasure (U := U) ν) x := by
  classical
  obtain ⟨c, hc⟩ := kpfWeight_mul_le_of_invariance (U := U) (V := V)
  refine ⟨c, ?_⟩
  intro x
  have hmul :
      (2 : ENNReal) ^ (-(c : ℤ)) * xiFun ν (kpfWeight (U := V)) x =
        ∑' i : BinString, (2 : ENNReal) ^ (-(c : ℤ)) * (kpfWeight (U := V) i * ν i x) := by
    simp [xiFun, ENNReal.tsum_mul_left]
  have hterm : ∀ i : BinString,
      (2 : ENNReal) ^ (-(c : ℤ)) * (kpfWeight (U := V) i * ν i x) ≤ kpfWeight (U := U) i * ν i x := by
    intro i
    have hw : kpfWeight (U := V) i * (2 : ENNReal) ^ (-(c : ℤ)) ≤ kpfWeight (U := U) i := hc i
    have hw' :
        (kpfWeight (U := V) i * (2 : ENNReal) ^ (-(c : ℤ))) * ν i x ≤ kpfWeight (U := U) i * ν i x :=
      mul_le_mul_left hw (ν i x)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hw'
  calc
    (2 : ENNReal) ^ (-(c : ℤ)) * (xiKpfSemimeasure (U := V) ν) x
        = (2 : ENNReal) ^ (-(c : ℤ)) * xiFun ν (kpfWeight (U := V)) x := by
            simp [xiKpfSemimeasure, xiSemimeasure]
    _ = ∑' i : BinString, (2 : ENNReal) ^ (-(c : ℤ)) * (kpfWeight (U := V) i * ν i x) := hmul
    _ ≤ ∑' i : BinString, kpfWeight (U := U) i * ν i x := by
          exact ENNReal.tsum_le_tsum hterm
    _ = (xiKpfSemimeasure (U := U) ν) x := by
          simp [xiKpfSemimeasure, xiSemimeasure, xiFun]

end Mettapedia.Logic.UniversalPrediction
