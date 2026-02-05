import Mathlib.Tactic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.NARSMettaTruthFunctions
import Mettapedia.Logic.NARSEvidenceBridge

/-!
# NARS as Second-Order Probability (Beta-style evidence semantics)

This file provides a **semantics layer** for NARS truth values:

* A NARS truth value `t : TV` is treated as a view of underlying **evidence counts**
  `(n⁺, n⁻) : Evidence`.
* Revision is **evidence aggregation** (`hplus`) under this semantics.

We intentionally keep `Mettapedia.Logic.NARSMettaTruthFunctions` as a faithful mirror of
`lib_nars.metta`; all semantic claims are proved here, with explicit hypotheses.

This is the bridge needed to rebase NARS ↔ PLN comparisons on solid second-order (Beta) grounding.
-/

namespace Mettapedia.Logic.NARSSecondOrderProbability

open scoped ENNReal

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.NARSMettaTruthFunctions

/-! ## Validity predicate -/

/-- A NARS truth value is "probabilistically valid" when it is a frequency in `[0,1]`
and a confidence in `[0,1)`.

We keep this as a predicate (not a structure) to avoid interfering with the MeTTa mirror. -/
def IsProbTV (t : TV) : Prop :=
  0 ≤ t.f ∧ t.f ≤ 1 ∧ 0 ≤ t.c ∧ t.c < 1

namespace IsProbTV

theorem f_nonneg {t : TV} (ht : IsProbTV t) : 0 ≤ t.f := ht.1
theorem f_le_one {t : TV} (ht : IsProbTV t) : t.f ≤ 1 := ht.2.1
theorem c_nonneg {t : TV} (ht : IsProbTV t) : 0 ≤ t.c := ht.2.2.1
theorem c_lt_one {t : TV} (ht : IsProbTV t) : t.c < 1 := ht.2.2.2

end IsProbTV

/-! ## View functions: TV ↔ Evidence -/

namespace TV

/-- Interpret a NARS truth value as PLN evidence counts, using confidence prior/scale `k`.

This is exactly the PLN `ofSTV` map:

* total evidence `n = k * c / (1-c)`
* `n⁺ = f * n`, `n⁻ = (1-f) * n`

When `k = 1`, this matches the usual NARS `c2w`/`w2c` convention. -/
noncomputable def toEvidenceWithK (k : ℝ≥0∞) (t : TV) (hc : t.c < 1) : Evidence :=
  Evidence.ofSTV (κ := k) t.f t.c hc

end TV

namespace Evidence

/-- Interpret evidence counts as a NARS truth value (frequency + confidence), using prior/scale `k`.

We follow the NARS convention that frequency is arbitrary when total evidence is zero; we pick `0.5`.
-/
noncomputable def toNARSTVWithK (k : ℝ≥0∞) (e : Evidence) : TV :=
  let total := e.total
  let f := if total = 0 then 0.5 else (e.pos / total).toReal
  let c := (total / (total + k)).toReal
  ⟨f, c⟩

end Evidence

/-! ## Core semantic theorems -/

/-! ## Compatibility with the existing bridge file (k = 1) -/

theorem toEvidenceWithK_one_eq_bridge_toEvidence (t : TV) (ht : IsProbTV t) :
    TV.toEvidenceWithK 1 t ht.c_lt_one = Mettapedia.Logic.NARSEvidenceBridge.TV.toEvidence t := by
  -- Unfold both sides; the only real work is rewriting
  -- `ofReal t.c / ofReal (1-t.c)` into `ofReal (c2w t.c)`.
  have hden : 0 < 1 - t.c := sub_pos.mpr ht.c_lt_one
  have hdiv : ENNReal.ofReal t.c / ENNReal.ofReal (1 - t.c) = ENNReal.ofReal (c2w t.c) := by
    -- `ofReal (c/(1-c)) = ofReal c / ofReal (1-c)` on the positive denominator branch.
    simpa [c2w] using (ENNReal.ofReal_div_of_pos hden (x := t.c) (y := 1 - t.c)).symm
  have h1mf : 0 ≤ 1 - t.f := by linarith [ht.f_le_one]
  ext <;>
    simp [TV.toEvidenceWithK, Mettapedia.Logic.NARSEvidenceBridge.TV.toEvidence, Evidence.ofSTV,
      hdiv, ENNReal.ofReal_mul ht.f_nonneg, ENNReal.ofReal_mul h1mf]

theorem toNARSTVWithK_one_eq_bridge_toNARSTV (e : Evidence) :
    Evidence.toNARSTVWithK 1 e = Mettapedia.Logic.NARSEvidenceBridge.Evidence.toNARSTV e := by
  rfl

/-! ## Core revision (no clamps) and evidence aggregation -/

/-- The unclamped core of NARS revision (same as the MeTTa formula, without `min`/`max` guards). -/
noncomputable def truthRevisionCore (t1 t2 : TV) : TV :=
  let w1 := c2w t1.c
  let w2 := c2w t2.c
  let w := w1 + w2
  let f := (w1 * t1.f + w2 * t2.f) / w
  let c := w2c w
  ⟨f, c⟩

theorem truthRevisionCore_toEvidence
    (t1 t2 : TV) (ht1 : IsProbTV t1) (ht2 : IsProbTV t2) :
    TV.toEvidenceWithK 1 (truthRevisionCore t1 t2) (by
        -- Confidence is `w2c w`, hence < 1.
        -- This is true for all `w`, but we only need a simple arithmetic proof.
        unfold truthRevisionCore w2c
        have hw1 : 0 ≤ c2w t1.c := by
          unfold c2w
          have : 0 < 1 - t1.c := sub_pos.mpr ht1.c_lt_one
          exact div_nonneg ht1.c_nonneg (le_of_lt this)
        have hw2 : 0 ≤ c2w t2.c := by
          unfold c2w
          have : 0 < 1 - t2.c := sub_pos.mpr ht2.c_lt_one
          exact div_nonneg ht2.c_nonneg (le_of_lt this)
        -- `w/(w+1) < 1` when `w+1 > 0`.
        have hw : (c2w t1.c + c2w t2.c) / ((c2w t1.c + c2w t2.c) + 1) < 1 := by
          have hx : 0 ≤ c2w t1.c + c2w t2.c := add_nonneg hw1 hw2
          have hden : 0 < (c2w t1.c + c2w t2.c) + 1 := by
            have hx1 : (1 : ℝ) ≤ (c2w t1.c + c2w t2.c) + 1 := by
              simpa [zero_add] using add_le_add_right hx 1
            exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx1
          have hlt : (c2w t1.c + c2w t2.c) < (c2w t1.c + c2w t2.c) + 1 :=
            lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 1)
          exact (div_lt_one hden).2 hlt
        exact hw)
    =
    TV.toEvidenceWithK 1 t1 ht1.c_lt_one + TV.toEvidenceWithK 1 t2 ht2.c_lt_one := by
  -- Set up the real weights implied by confidence.
  have hden1 : 0 < 1 - t1.c := sub_pos.mpr ht1.c_lt_one
  have hden2 : 0 < 1 - t2.c := sub_pos.mpr ht2.c_lt_one
  set w1 : ℝ := c2w t1.c
  set w2 : ℝ := c2w t2.c
  set w : ℝ := w1 + w2
  have hw1 : 0 ≤ w1 := by
    subst w1; unfold c2w; exact div_nonneg ht1.c_nonneg (le_of_lt hden1)
  have hw2 : 0 ≤ w2 := by
    subst w2; unfold c2w; exact div_nonneg ht2.c_nonneg (le_of_lt hden2)
  have hw : 0 ≤ w := add_nonneg hw1 hw2

  -- Rewrite `ofSTV` totals into `ofReal (c2w _)`.
  have htot (t : TV) (hc : t.c < 1) :
      ENNReal.ofReal t.c / ENNReal.ofReal (1 - t.c) = ENNReal.ofReal (c2w t.c) := by
    have hden : 0 < 1 - t.c := sub_pos.mpr hc
    simpa [c2w] using (ENNReal.ofReal_div_of_pos hden (x := t.c) (y := 1 - t.c)).symm

  -- The revision confidence implies total evidence `w` (via `c2w (w2c w) = w`).
  have hc_rev : (w2c w) < 1 := by
    unfold w2c
    have hpos : 0 < w + 1 := by
      have hx1 : (1 : ℝ) ≤ w + 1 := by
        simpa [zero_add] using add_le_add_right hw 1
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx1
    -- `w/(w+1) < 1` since `w < w+1`.
    have hwlt : w < w + 1 := lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 1)
    have : w / (w + 1) < 1 := (div_lt_one hpos).2 hwlt
    simpa [w2c] using this
  have htot_rev : ENNReal.ofReal (w2c w) / ENNReal.ofReal (1 - w2c w) = ENNReal.ofReal w := by
    have hden : 0 < 1 - w2c w := sub_pos.mpr hc_rev
    -- First rewrite to `ofReal (c2w (w2c w))`, then use the real identity.
    have : ENNReal.ofReal (w2c w) / ENNReal.ofReal (1 - w2c w) =
        ENNReal.ofReal (c2w (w2c w)) := by
      simpa [c2w] using (ENNReal.ofReal_div_of_pos hden (x := w2c w) (y := 1 - w2c w)).symm
    -- `c2w (w2c w) = w` when `w ≥ 0`.
    have hw_id : c2w (w2c w) = w := by
      simpa using (Mettapedia.Logic.NARSEvidenceBridge.c2w_w2c_id w hw)
    simpa [hw_id] using this

  -- Frequency bounds for the weighted average (needed so `ofReal_mul` applies to `1 - f` too).
  have hnum_nonneg : 0 ≤ w1 * t1.f + w2 * t2.f := by
    have : 0 ≤ w1 * t1.f := mul_nonneg hw1 ht1.f_nonneg
    have : 0 ≤ w2 * t2.f := mul_nonneg hw2 ht2.f_nonneg
    linarith
  have hf_rev_nonneg : 0 ≤ (w1 * t1.f + w2 * t2.f) / w := by
    by_cases hw0 : w = 0
    · simp [hw0]
    · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
      exact div_nonneg hnum_nonneg (le_of_lt hwpos)
  have hnum_le_w : w1 * t1.f + w2 * t2.f ≤ w := by
    have h1 : w1 * t1.f ≤ w1 * 1 := mul_le_mul_of_nonneg_left ht1.f_le_one hw1
    have h2 : w2 * t2.f ≤ w2 * 1 := mul_le_mul_of_nonneg_left ht2.f_le_one hw2
    have h12 : w1 * t1.f + w2 * t2.f ≤ w1 * 1 + w2 * 1 := add_le_add h1 h2
    simpa [w, mul_one] using h12
  have hf_rev_le_one : (w1 * t1.f + w2 * t2.f) / w ≤ 1 := by
    by_cases hw0 : w = 0
    · simp [hw0]
    · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
      exact (div_le_one hwpos).2 hnum_le_w
  have h1mf_rev_nonneg : 0 ≤ 1 - (w1 * t1.f + w2 * t2.f) / w := by
    linarith

  -- Helper: cancel the weighted-average division (with the `w = 0` corner handled explicitly).
  have hw_cancel :
      ((w1 * t1.f + w2 * t2.f) / w) * w = w1 * t1.f + w2 * t2.f := by
    by_cases hw0 : w = 0
    · -- With `w = w1 + w2 = 0` and `w1,w2 ≥ 0`, both weights are 0, hence numerator is 0.
      have hw1' : w1 = 0 := by
        have : w1 ≤ 0 := by
          have : w1 ≤ w1 + w2 := by linarith [hw2]
          simpa [w, hw0] using this
        exact le_antisymm this hw1
      have hw2' : w2 = 0 := by
        have : w2 ≤ 0 := by
          have : w2 ≤ w1 + w2 := by linarith [hw1]
          simpa [w, hw0, add_comm] using this
        exact le_antisymm this hw2
      simp [w, hw0, hw1', hw2']
    · -- If `w ≠ 0`, this is the usual field cancellation.
      field_simp [hw0]

  -- Now prove equality by ext on `(pos,neg)`.
  ext
  · -- pos
    -- Reduce both sides to an `ofReal` statement on reals.
    -- LHS: `ofReal f_rev * ofReal w = ofReal (f_rev*w)`.
    -- RHS: `ofReal (f1*w1) + ofReal (f2*w2) = ofReal (f1*w1 + f2*w2)`.
    have hterm1 : 0 ≤ t1.f * w1 := mul_nonneg ht1.f_nonneg hw1
    have hterm2 : 0 ≤ t2.f * w2 := mul_nonneg ht2.f_nonneg hw2
    have hpos_add : ENNReal.ofReal (t1.f * w1 + t2.f * w2) =
        ENNReal.ofReal (t1.f * w1) + ENNReal.ofReal (t2.f * w2) := by
      simpa [add_comm, add_left_comm, add_assoc] using (ENNReal.ofReal_add hterm1 hterm2)
    -- Reduce to a clean ENNReal equality.
    simp [TV.toEvidenceWithK, Evidence.ofSTV, truthRevisionCore, w1, w2, w,
      htot t1 ht1.c_lt_one, htot t2 ht2.c_lt_one, htot_rev, Evidence.hplus_def]
    -- Convert products/sums into a single `ofReal`, then use the real cancellation `hw_cancel`.
    rw [← ENNReal.ofReal_mul hf_rev_nonneg]
    rw [← ENNReal.ofReal_mul ht1.f_nonneg]
    rw [← ENNReal.ofReal_mul ht2.f_nonneg]
    rw [← ENNReal.ofReal_add hterm1 hterm2]
    have hreal :
        ((w1 * t1.f + w2 * t2.f) / w) * (c2w t1.c + c2w t2.c) = t1.f * w1 + t2.f * w2 := by
      -- The ENNReal "total evidence" on the RHS is exactly `w = w1 + w2`.
      have hw_tot : c2w t1.c + c2w t2.c = w := by simp [w, w1, w2]
      -- Cancel by `w` and normalize commutativity in the numerator.
      simpa [hw_tot, mul_comm, add_comm, add_left_comm, add_assoc] using hw_cancel
    simp [hreal]
  · -- neg
    have h1mf1 : 0 ≤ 1 - t1.f := sub_nonneg.mpr ht1.f_le_one
    have h1mf2 : 0 ≤ 1 - t2.f := sub_nonneg.mpr ht2.f_le_one
    have hterm1 : 0 ≤ (1 - t1.f) * w1 := mul_nonneg h1mf1 hw1
    have hterm2 : 0 ≤ (1 - t2.f) * w2 := mul_nonneg h1mf2 hw2
    have hneg_add : ENNReal.ofReal ((1 - t1.f) * w1 + (1 - t2.f) * w2) =
        ENNReal.ofReal ((1 - t1.f) * w1) + ENNReal.ofReal ((1 - t2.f) * w2) := by
      simpa [add_comm, add_left_comm, add_assoc] using (ENNReal.ofReal_add hterm1 hterm2)
    -- We rewrite `(1 - f_rev) * w` as `w - (f_rev*w)` and use `hw_cancel`.
    have hneg_rw :
        (1 - (w1 * t1.f + w2 * t2.f) / w) * w = (1 - t1.f) * w1 + (1 - t2.f) * w2 := by
      -- Handle the `w = 0` corner separately to avoid division-by-zero algebra.
      by_cases hw0 : w = 0
      · -- As in `hw_cancel`, `w1=w2=0` so both sides are 0.
        have hw1' : w1 = 0 := by
          have : w1 ≤ 0 := by
            have : w1 ≤ w1 + w2 := by linarith [hw2]
            simpa [w, hw0] using this
          exact le_antisymm this hw1
        have hw2' : w2 = 0 := by
          have : w2 ≤ 0 := by
            have : w2 ≤ w1 + w2 := by linarith [hw1]
            simpa [w, hw0, add_comm] using this
          exact le_antisymm this hw2
        simp [w, hw0, hw1', hw2']
      · have hw_cancel' : ((w1 * t1.f + w2 * t2.f) / w) * w = w1 * t1.f + w2 * t2.f := by
          -- Reuse the already-proved cancellation lemma.
          simpa using hw_cancel
        -- In the `w ≠ 0` branch we can use `ring` safely.
        -- `(1 - a/w) * w = w - (a/w) * w`.
        calc (1 - (w1 * t1.f + w2 * t2.f) / w) * w
            = w - ((w1 * t1.f + w2 * t2.f) / w) * w := by ring
        _ = w - (w1 * t1.f + w2 * t2.f) := by simp [hw_cancel']
        _ = (1 - t1.f) * w1 + (1 - t2.f) * w2 := by
              -- Expand `w = w1 + w2` and collect terms.
              simp [w]; ring

    simp [TV.toEvidenceWithK, Evidence.ofSTV, truthRevisionCore, w1, w2, w,
      htot t1 ht1.c_lt_one, htot t2 ht2.c_lt_one, htot_rev, Evidence.hplus_def]
    rw [← ENNReal.ofReal_mul h1mf_rev_nonneg]
    rw [← ENNReal.ofReal_mul h1mf1]
    rw [← ENNReal.ofReal_mul h1mf2]
    rw [← ENNReal.ofReal_add hterm1 hterm2]
    -- Now both sides are `ofReal` of the same real expression.
    have hreal :
        (1 - (w1 * t1.f + w2 * t2.f) / w) * (c2w t1.c + c2w t2.c) =
          (1 - t1.f) * w1 + (1 - t2.f) * w2 := by
      have hw_tot : c2w t1.c + c2w t2.c = w := by simp [w, w1, w2]
      simpa [hw_tot] using hneg_rw
    simp [hreal]

end Mettapedia.Logic.NARSSecondOrderProbability
