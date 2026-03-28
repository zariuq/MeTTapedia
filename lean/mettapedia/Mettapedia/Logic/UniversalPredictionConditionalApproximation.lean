import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mettapedia.Logic.UniversalPredictionConditionalWMBridge

/-!
# Quantitative Conditional Approximation for Universal Mixtures

This file upgrades the exact conditional-query API with an honest quantitative
approximation theorem.

Main idea:
- the geometric finite-prefix approximant misses at most a geometric tail mass,
- under an explicit floor on the approximant's context mass, the induced
  conditional probability changes by at most a controlled ratio error.

Positive example:
- if the observed context has substantial approximant mass, then adding more
  universal-mixture components only changes `P(y | x)` by a small geometric
  amount.

Negative example:
- if the approximant assigns extremely small mass to the conditioning context,
  the denominator can amplify tail error, and no uniform conditional bound is
  claimed.
-/

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical
open Mettapedia.Logic.PLNWorldModel

/-- The canonical geometric tail budget after keeping the first `n` mixture
components. -/
noncomputable def geomTailMass (n : ℕ) : ENNReal :=
  (2⁻¹ : ENNReal) ^ n

theorem geometricWeight_shift (i n : ℕ) :
    geometricWeight (i + n) = geomTailMass n * geometricWeight i := by
  unfold geometricWeight geomTailMass
  have h2ne0 : (2 : ENNReal) ≠ 0 := by norm_num
  have h2neTop : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
  rw [show (-1 - ↑(i + n) : ℤ) = (-(n : ℤ)) + (-1 - (i : ℤ)) by omega]
  rw [ENNReal.zpow_add h2ne0 h2neTop]
  rw [show (2 : ENNReal) ^ (-(n : ℤ)) = (2⁻¹ : ENNReal) ^ n by
    simp [ENNReal.zpow_neg, ENNReal.inv_pow]]

theorem geomTailMass_eq_tsum_shift (n : ℕ) :
    geomTailMass n = ∑' i : ℕ, geometricWeight (i + n) := by
  calc
    geomTailMass n = geomTailMass n * ∑' i : ℕ, geometricWeight i := by
      rw [tsum_geometricWeight, mul_one]
    _ = ∑' i : ℕ, geomTailMass n * geometricWeight i := by
      simpa using (ENNReal.tsum_mul_left (a := geomTailMass n) (f := geometricWeight)).symm
    _ = ∑' i : ℕ, geometricWeight (i + n) := by
      refine tsum_congr ?_
      intro i
      rw [geometricWeight_shift]

theorem xiGeomSemimeasure_le_approx_add_tail
    (ν : ℕ → Semimeasure) (n : ℕ) (x : BinString) :
    (xiGeomSemimeasure ν) x ≤ (xiGeomApproxSemimeasure ν n) x + geomTailMass n := by
  let f : ℕ → ENNReal := fun i => geometricWeight i * ν i x
  have htail :
      ∀ m : ℕ,
        ∑ i ∈ Finset.range m, f i ≤ (xiGeomApproxSemimeasure ν n) x + geomTailMass n := by
    intro m
    by_cases hm : m ≤ n
    · calc
        ∑ i ∈ Finset.range m, f i = (xiGeomApproxSemimeasure ν m) x := by
              rfl
        _ ≤ (xiGeomApproxSemimeasure ν n) x := xiGeomApproxSemimeasure_mono ν hm x
        _ ≤ (xiGeomApproxSemimeasure ν n) x + geomTailMass n := by
              exact le_add_of_nonneg_right bot_le
    · have hm' : n + (m - n) = m := by omega
      have hsplit :
          ∑ i ∈ Finset.range m, f i =
            ∑ i ∈ Finset.range n, f i +
              ∑ i ∈ Finset.range (m - n), f (n + i) := by
        simpa [hm'] using (Finset.sum_range_add f n (m - n))
      have htailFin :
          ∑ i ∈ Finset.range (m - n), f (n + i) ≤ geomTailMass n := by
        calc
          ∑ i ∈ Finset.range (m - n), f (n + i)
              ≤ ∑' i : ℕ, f (n + i) := by
                  exact ENNReal.sum_le_tsum (s := Finset.range (m - n)) (f := fun i => f (n + i))
          _ ≤ ∑' i : ℕ, geometricWeight (i + n) := by
                refine ENNReal.tsum_le_tsum ?_
                intro i
                dsimp [f]
                simpa [Nat.add_comm, mul_one] using
                  mul_le_mul_right (semimeasure_le_one (ν (i + n)) x) (geometricWeight (i + n))
          _ = geomTailMass n := by rw [← geomTailMass_eq_tsum_shift]
      calc
        ∑ i ∈ Finset.range m, f i
            = ∑ i ∈ Finset.range n, f i + ∑ i ∈ Finset.range (m - n), f (n + i) := hsplit
        _ ≤ (xiGeomApproxSemimeasure ν n) x + geomTailMass n := by
              simpa [add_comm, add_left_comm, add_assoc, f, xiGeomApproxSemimeasure,
                xiApproxSemimeasure, xiApproxFun] using
                add_le_add_left htailFin (∑ i ∈ Finset.range n, f i)
  calc
    (xiGeomSemimeasure ν) x
        = ⨆ m : ℕ, ∑ i ∈ Finset.range m, f i := by
            simpa [f, xiGeomSemimeasure, xiSemimeasure, xiFun] using
              (ENNReal.tsum_eq_iSup_nat (f := f))
    _ ≤ (xiGeomApproxSemimeasure ν n) x + geomTailMass n := by
          refine iSup_le ?_
          intro m
          exact htail m

theorem xiGeomSemimeasure_tail_le
    (ν : ℕ → Semimeasure) (n : ℕ) (x : BinString) :
    (xiGeomSemimeasure ν) x - (xiGeomApproxSemimeasure ν n) x ≤ geomTailMass n := by
  simpa [add_comm] using
    (tsub_le_iff_right).2 (xiGeomSemimeasure_le_approx_add_tail ν n x)

/-- Real ratio stability under one-sided tail control and an explicit lower
bound on the denominator. -/
lemma abs_div_sub_div_le_of_tail
    {a A b B ε δ : ℝ}
    (ha_nonneg : 0 ≤ a)
    (haA : a ≤ A) (hbB : b ≤ B) (hab : a ≤ b)
    (hA : A - a ≤ ε) (hB : B - b ≤ ε)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδb : δ ≤ b) :
    |a / b - A / B| ≤ 2 * ε / δ := by
  have hb_pos : 0 < b := lt_of_lt_of_le hδ hδb
  have hB_pos : 0 < B := lt_of_lt_of_le hδ (hδb.trans hbB)
  have hnum :
      |a * B - A * b| ≤ 2 * B * ε := by
    have hterm1 : a * (B - b) ≤ B * ε := by
      nlinarith [ha_nonneg, hab, hbB, hB]
    have hterm2 : b * (A - a) ≤ B * ε := by
      nlinarith [hb_pos.le, hbB, haA, hA]
    calc
      |a * B - A * b| = |a * (B - b) - b * (A - a)| := by ring_nf
      _ ≤ |a * (B - b)| + |b * (A - a)| := by
            simpa using (abs_sub (a * (B - b)) (b * (A - a)))
      _ = a * (B - b) + b * (A - a) := by
            rw [abs_of_nonneg (mul_nonneg ha_nonneg (sub_nonneg.mpr hbB))]
            rw [abs_of_nonneg (mul_nonneg hb_pos.le (sub_nonneg.mpr haA))]
      _ ≤ B * ε + B * ε := add_le_add hterm1 hterm2
      _ = 2 * B * ε := by ring
  have hfrac : a / b - A / B = (a * B - A * b) / (b * B) := by
    field_simp [hb_pos.ne', hB_pos.ne']
  rw [hfrac, abs_div, abs_of_pos (mul_pos hb_pos hB_pos)]
  calc
    |a * B - A * b| / (b * B) ≤ (2 * B * ε) / (b * B) := by
      gcongr
    _ = 2 * ε / b := by
      field_simp [hb_pos.ne', hB_pos.ne']
    _ ≤ 2 * ε / δ := by
      gcongr

theorem geomConditionalENN_toReal_abs_sub_le
    (ν : ℕ → Semimeasure) (n : ℕ) (x y : BinString)
    {δ : ENNReal}
    (hδ0 : δ ≠ 0) (hδTop : δ ≠ ⊤)
    (hfloor : δ ≤ (xiGeomApproxSemimeasure ν n) x) :
    |(conditionalENN (xiGeomApproxSemimeasure ν n) y x).toReal -
        (conditionalENN (xiGeomSemimeasure ν) y x).toReal|
      ≤ 2 * (geomTailMass n).toReal / δ.toReal := by
  let a : ENNReal := (xiGeomApproxSemimeasure ν n) (x ++ y)
  let A : ENNReal := (xiGeomSemimeasure ν) (x ++ y)
  let b : ENNReal := (xiGeomApproxSemimeasure ν n) x
  let B : ENNReal := (xiGeomSemimeasure ν) x
  have haA : a ≤ A := by
    exact xiGeomApproxSemimeasure_le_full ν n (x ++ y)
  have hbB : b ≤ B := by
    exact xiGeomApproxSemimeasure_le_full ν n x
  have hab : a ≤ b := by
    dsimp [a, b]
    exact (xiGeomApproxSemimeasure ν n).mono_append x y
  have hAB : A ≤ B := by
    dsimp [A, B]
    exact (xiGeomSemimeasure ν).mono_append x y
  have hA_tail : A - a ≤ geomTailMass n := by
    dsimp [a, A]
    exact xiGeomSemimeasure_tail_le ν n (x ++ y)
  have hB_tail : B - b ≤ geomTailMass n := by
    dsimp [b, B]
    exact xiGeomSemimeasure_tail_le ν n x
  have hδ_pos : 0 < δ.toReal := ENNReal.toReal_pos hδ0 hδTop
  have hb_top : b ≠ ⊤ := by
    dsimp [b]
    exact semimeasure_ne_top (xiGeomApproxSemimeasure ν n) x
  have hB_top : B ≠ ⊤ := by
    dsimp [B]
    exact semimeasure_ne_top (xiGeomSemimeasure ν) x
  have hA_top : A ≠ ⊤ := by
    dsimp [A]
    exact semimeasure_ne_top (xiGeomSemimeasure ν) (x ++ y)
  have ha_top : a ≠ ⊤ := by
    dsimp [a]
    exact semimeasure_ne_top (xiGeomApproxSemimeasure ν n) (x ++ y)
  have hfloor_real : δ.toReal ≤ b.toReal := by
    exact ENNReal.toReal_mono hb_top hfloor
  have hA_real : A.toReal - a.toReal ≤ (geomTailMass n).toReal := by
    have h' : (A - a).toReal ≤ (geomTailMass n).toReal :=
      ENNReal.toReal_mono (by simp [geomTailMass]) hA_tail
    rwa [ENNReal.toReal_sub_of_le haA hA_top] at h'
  have hB_real : B.toReal - b.toReal ≤ (geomTailMass n).toReal := by
    have h' : (B - b).toReal ≤ (geomTailMass n).toReal :=
      ENNReal.toReal_mono (by simp [geomTailMass]) hB_tail
    rwa [ENNReal.toReal_sub_of_le hbB hB_top] at h'
  have habs :
      |a.toReal / b.toReal - A.toReal / B.toReal|
        ≤ 2 * (geomTailMass n).toReal / δ.toReal := by
    apply abs_div_sub_div_le_of_tail
    · exact ENNReal.toReal_nonneg
    · exact ENNReal.toReal_mono hA_top haA
    · exact ENNReal.toReal_mono hB_top hbB
    · exact ENNReal.toReal_mono hb_top hab
    · exact hA_real
    · exact hB_real
    · exact ENNReal.toReal_nonneg
    · exact hδ_pos
    · exact hfloor_real
  simpa [conditionalENN, a, A, b, B, ENNReal.toReal_div, abs_sub_comm] using habs

theorem geomApproxConditionalQueryStrength_abs_sub_le
    (ν : ℕ → Semimeasure) (n : ℕ) (q : ConditionalPrefixQuery)
    {δ : ENNReal}
    (hδ0 : δ ≠ 0) (hδTop : δ ≠ ⊤)
    (hfloor : δ ≤ (xiGeomApproxSemimeasure ν n) q.context) :
    |(BinaryWorldModel.queryStrength (geomApproxConditionalProfile ν n) q).toReal -
        (BinaryWorldModel.queryStrength (geomConditionalProfile ν) q).toReal|
      ≤ 2 * (geomTailMass n).toReal / δ.toReal := by
  rw [geomApproxConditionalQueryStrength_eq_conditionalENN,
    geomConditionalQueryStrength_eq_conditionalENN]
  exact geomConditionalENN_toReal_abs_sub_le ν n q.context q.target hδ0 hδTop hfloor

/-- Two geometric conditional approximants are close whenever both budgets keep
the conditioning context above the same explicit denominator floor.  This is a
safe Cauchy-style replacement for any unsupported monotonicity claim about
conditional ratios themselves. -/
theorem geomApproxConditionalQueryStrength_abs_sub_le_between_budgets
    (ν : ℕ → Semimeasure) (n m : ℕ) (q : ConditionalPrefixQuery)
    {δ : ENNReal}
    (hδ0 : δ ≠ 0) (hδTop : δ ≠ ⊤)
    (hfloor_n : δ ≤ (xiGeomApproxSemimeasure ν n) q.context)
    (hfloor_m : δ ≤ (xiGeomApproxSemimeasure ν m) q.context) :
    |(BinaryWorldModel.queryStrength (geomApproxConditionalProfile ν n) q).toReal -
        (BinaryWorldModel.queryStrength (geomApproxConditionalProfile ν m) q).toReal|
      ≤ 2 * (geomTailMass n).toReal / δ.toReal +
          2 * (geomTailMass m).toReal / δ.toReal := by
  have hn :=
    geomApproxConditionalQueryStrength_abs_sub_le
      ν n q hδ0 hδTop hfloor_n
  have hm :=
    geomApproxConditionalQueryStrength_abs_sub_le
      ν m q hδ0 hδTop hfloor_m
  let a : ℝ :=
    (BinaryWorldModel.queryStrength (geomApproxConditionalProfile ν n) q).toReal
  let b : ℝ :=
    (BinaryWorldModel.queryStrength (geomConditionalProfile ν) q).toReal
  let c : ℝ :=
    (BinaryWorldModel.queryStrength (geomApproxConditionalProfile ν m) q).toReal
  have htri : |a - c| ≤ |a - b| + |b - c| := by
    calc
      |a - c| = |(a - b) + (b - c)| := by ring_nf
      _ ≤ |a - b| + |b - c| := abs_add_le _ _
  have hm' : |b - c| ≤ 2 * (geomTailMass m).toReal / δ.toReal := by
    simpa [a, b, c, abs_sub_comm] using hm
  have hbound :
      |a - c| ≤
        2 * (geomTailMass n).toReal / δ.toReal +
          2 * (geomTailMass m).toReal / δ.toReal := by
    linarith [htri, hm, hm']
  simpa [a, c] using hbound

/-- Cauchy-style conditional approximation bound when the lower-budget context
mass already provides the common denominator floor.  Monotonicity of the
approximant context mass supplies the floor for the larger budget. -/
theorem geomApproxConditionalQueryStrength_abs_sub_le_between_budgets_of_le
    (ν : ℕ → Semimeasure) {n m : ℕ} (hnm : n ≤ m) (q : ConditionalPrefixQuery)
    {δ : ENNReal}
    (hδ0 : δ ≠ 0) (hδTop : δ ≠ ⊤)
    (hfloor : δ ≤ (xiGeomApproxSemimeasure ν n) q.context) :
    |(BinaryWorldModel.queryStrength (geomApproxConditionalProfile ν n) q).toReal -
        (BinaryWorldModel.queryStrength (geomApproxConditionalProfile ν m) q).toReal|
      ≤ 2 * (geomTailMass n).toReal / δ.toReal +
          2 * (geomTailMass m).toReal / δ.toReal := by
  refine geomApproxConditionalQueryStrength_abs_sub_le_between_budgets
    ν n m q hδ0 hδTop hfloor ?_
  exact le_trans hfloor (xiGeomApproxSemimeasure_mono ν hnm q.context)

end Mettapedia.Logic.UniversalPrediction
