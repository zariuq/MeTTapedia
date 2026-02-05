import Mathlib.Tactic
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNMettaTruthFunctions

namespace Mettapedia.Logic.NuEvidenceQuantaleBridge

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNMettaTruthFunctions
open scoped ENNReal

/-!
# nuPLN: Evidence-Quantale <-> MeTTa Truth-Value Bridge

This file states and proves small "bridge" lemmas connecting:
- the *numerical* truth-value formulas (as mirrored from `lib_pln.metta`), and
- the Evidence semantics (`EvidenceQuantale.lean`) that interprets truth values as evidence counts.

The intended use is to make explicit (and checkable) the hypotheses under which the MeTTa-style
truth-value calculations coincide with Evidence addition (`hplus`) and its `toSTV` view.
-/

namespace Bridge

/-- Convert a MeTTa-style truth value to Evidence by interpreting confidence via the capped
weight transform `w = c/(1-c)` (with a fixed prior parameter `κ`). -/
noncomputable def TV.toEvidence (κ : ℝ≥0∞) (t : TV) : Evidence :=
  Evidence.ofSTV (κ := κ) t.s (capConf t.c) (capConf_lt_one t.c)

/-- View Evidence as a MeTTa-style truth value `(strength, confidence)` in `ℝ`. -/
noncomputable def Evidence.toTV (κ : ℝ≥0∞) (e : Evidence) : TV :=
  ⟨(Evidence.toStrength e).toReal, (Evidence.toConfidence (κ := κ) e).toReal⟩

end Bridge

/-! ## Weight/Confidence algebra (capped) -/

namespace PLNMettaTruthFunctions

/-- `w2c (c2w c)` reduces to the capped confidence `capConf c`. -/
theorem w2c_c2w_eq_capConf (c : ℝ) : w2c (c2w c) = capConf c := by
  -- Unfold and compute using the algebra `w/(w+1)` with `w = c/(1-c)`.
  unfold c2w w2c
  -- Name the capped confidence.
  set cc : ℝ := capConf c
  have hcc0 : 0 ≤ cc := by
    simp [cc, capConf]
  have hcc1 : cc < 1 := by
    simpa [cc] using capConf_lt_one c
  have hcc1pos : 0 < 1 - cc := by linarith
  have hw0 : 0 ≤ cc / (1 - cc) := div_nonneg hcc0 (le_of_lt hcc1pos)
  -- `max 0 w = w` since `w ≥ 0`.
  simp [cc, hw0]
  -- Finish the algebra.
  have hne : (1 - cc) ≠ 0 := by linarith
  have hden : cc / (1 - cc) + 1 = 1 / (1 - cc) := by
    field_simp [hne]
    ring
  rw [hden]
  -- Reduce to the cancellation `(1-cc) * (1 / (1-cc)) = 1`.
  rw [div_div]
  have hmul : (1 - cc) * (1 / (1 - cc)) = 1 := by
    simp [div_eq_mul_inv, hne]
  rw [hmul]
  simp

/-- `w2c` is monotone (it is `w ↦ max 0 w / (max 0 w + 1)`). -/
theorem w2c_monotone : Monotone w2c := by
  intro a b hab
  unfold w2c
  -- Reduce to the monotonicity of `max 0`.
  have hmax : max 0 a ≤ max 0 b := max_le_max_left 0 hab
  set aa : ℝ := max 0 a
  set bb : ℝ := max 0 b
  have haa : 0 ≤ aa := by simp [aa]
  have hbb : 0 ≤ bb := by simp [bb]
  -- Compare `aa/(aa+1)` and `bb/(bb+1)` by cross-multiplication (denominators are positive).
  have hdenA : 0 < aa + 1 := by linarith
  have hdenB : 0 < bb + 1 := by linarith
  -- Rewrite the goal in terms of `aa`, `bb`.
  -- Note: `simp` will unfold `aa`/`bb` back when needed.
  have : aa / (aa + 1) ≤ bb / (bb + 1) := by
    -- `a/(a+1) ≤ b/(b+1)` iff `a*(b+1) ≤ b*(a+1)` for positive denominators.
    rw [div_le_div_iff₀ hdenA hdenB]
    -- This simplifies to `aa ≤ bb`.
    nlinarith [hmax]
  simpa [aa, bb] using this

/-- Taking `min` in weight-space and mapping back via `w2c` is the same as taking `min` of the
corresponding capped confidences. -/
theorem w2c_min_c2w (c1 c2 : ℝ) :
    w2c (min (c2w c1) (c2w c2)) = min (capConf c1) (capConf c2) := by
  have hmono : Monotone w2c := w2c_monotone
  -- `w2c` is monotone, so it preserves `min`.
  simpa [w2c_c2w_eq_capConf] using (hmono.map_min (a := c2w c1) (b := c2w c2))

end PLNMettaTruthFunctions

/-
## Bridge: Revision = Evidence Aggregation

Here we connect the MeTTa-style revision rule (weighted average by confidence-weights) to the
Evidence semantics (`hplus` on evidence counts) under a *single* prior parameter `κ`.
-/

namespace Bridge

open scoped ENNReal

open Mettapedia.Logic.PLNMettaTruthFunctions

/-- The `Evidence.ofSTV` "total evidence" matches the intended `κ * c / (1-c)` when
`s ∈ [0,1]`. This makes confidence independent of strength, as in the PLN book formulas. -/
theorem toEvidence_total (κ : ℝ≥0∞) (t : TV) (hs0 : 0 ≤ t.s) (hs1 : t.s ≤ 1) :
    (TV.toEvidence κ t).total =
      κ * ENNReal.ofReal (capConf t.c) / ENNReal.ofReal (1 - capConf t.c) := by
  -- Unfold the definition and reduce to `ofReal s + ofReal (1-s) = 1`.
  simp [TV.toEvidence, Evidence.ofSTV, Evidence.total]
  rw [← add_mul]
  have hs1' : 0 ≤ 1 - t.s := by linarith
  have hsum : ENNReal.ofReal t.s + ENNReal.ofReal (1 - t.s) = (1 : ℝ≥0∞) := by
    calc
      ENNReal.ofReal t.s + ENNReal.ofReal (1 - t.s)
          = ENNReal.ofReal (t.s + (1 - t.s)) := by
              symm
              exact ENNReal.ofReal_add hs0 hs1'
      _ = ENNReal.ofReal 1 := by ring_nf
      _ = (1 : ℝ≥0∞) := by simp
  simp [hsum]

/-- `w2c` is just `w/(w+1)` when `w ≥ 0` (the `max 0` branch is inactive). -/
theorem w2c_eq_div_of_nonneg (w : ℝ) (hw : 0 ≤ w) : w2c w = w / (w + 1) := by
  unfold w2c
  simp [hw]

/-- The weight transform `c2w` is always nonnegative (because we cap to `[0, MAX_CONF]`). -/
theorem c2w_nonneg (c : ℝ) : 0 ≤ c2w c := by
  unfold c2w
  set cc : ℝ := capConf c
  have hcc0 : 0 ≤ cc := by simp [cc, capConf]
  have hcc1 : cc < 1 := by simpa [cc] using capConf_lt_one c
  have hcc1pos : 0 < 1 - cc := by linarith
  simpa [cc] using div_nonneg hcc0 (le_of_lt hcc1pos)

/-- Revision confidence agrees with `Evidence.toConfidence` after mapping STVs to evidence and
adding, assuming a single finite `κ`. -/
theorem truthRevision_conf_eq_toConfidence
    (κ : ℝ≥0∞) (hκ0 : κ ≠ 0) (hκT : κ ≠ ⊤)
    (t1 t2 : TV)
    (hs1 : 0 ≤ t1.s) (hs1' : t1.s ≤ 1)
    (hs2 : 0 ≤ t2.s) (hs2' : t2.s ≤ 1) :
    (truthRevision t1 t2).c =
      (Evidence.toConfidence (κ := κ) (TV.toEvidence κ t1 + TV.toEvidence κ t2)).toReal := by
  -- Expand the Evidence side.
  have ht1 : (TV.toEvidence κ t1).total =
      κ * ENNReal.ofReal (capConf t1.c) / ENNReal.ofReal (1 - capConf t1.c) :=
    toEvidence_total κ t1 hs1 hs1'
  have ht2 : (TV.toEvidence κ t2).total =
      κ * ENNReal.ofReal (capConf t2.c) / ENNReal.ofReal (1 - capConf t2.c) :=
    toEvidence_total κ t2 hs2 hs2'
  -- Total evidence adds under `hplus`.
  have htot_add :
      (TV.toEvidence κ t1 + TV.toEvidence κ t2).total =
        (TV.toEvidence κ t1).total + (TV.toEvidence κ t2).total := by
    simp [Evidence.total, Evidence.hplus_def, add_assoc, add_comm, add_left_comm]
  -- Compute the confidence in ENNReal, then convert to `ℝ` via `toReal`.
  -- Let `w1E`, `w2E` be the ENNReal weights.
  set w1E : ℝ≥0∞ := ENNReal.ofReal (capConf t1.c) / ENNReal.ofReal (1 - capConf t1.c)
  set w2E : ℝ≥0∞ := ENNReal.ofReal (capConf t2.c) / ENNReal.ofReal (1 - capConf t2.c)
  have htot1 : (TV.toEvidence κ t1).total = κ * w1E := by
    -- `κ * a / b` is `(κ * a) / b`, and `mul_div_assoc` rewrites it as `κ * (a / b)`.
    simpa [w1E, mul_div_assoc] using ht1
  have htot2 : (TV.toEvidence κ t2).total = κ * w2E := by
    simpa [w2E, mul_div_assoc] using ht2
  have htotSum : (TV.toEvidence κ t1 + TV.toEvidence κ t2).total = κ * (w1E + w2E) := by
    calc
      (TV.toEvidence κ t1 + TV.toEvidence κ t2).total
          = (TV.toEvidence κ t1).total + (TV.toEvidence κ t2).total := htot_add
      _ = κ * w1E + κ * w2E := by simp [htot1, htot2]
      _ = κ * (w1E + w2E) := by
        rw [← mul_add]
  -- Now unfold `toConfidence` and cancel `κ`.
  have hconf :
      Evidence.toConfidence (κ := κ) (TV.toEvidence κ t1 + TV.toEvidence κ t2)
        = (w1E + w2E) / (w1E + w2E + 1) := by
    unfold Evidence.toConfidence
    -- Rewrite total using `htotSum`.
    rw [htotSum]
    -- Factor `κ` out of the denominator.
    have hden : κ * (w1E + w2E) + κ = κ * (w1E + w2E + 1) := by
      calc
        κ * (w1E + w2E) + κ
            = κ * (w1E + w2E) + κ * 1 := by simp
        _ = κ * ((w1E + w2E) + 1) := by simp [mul_add]
        _ = κ * (w1E + w2E + 1) := by ac_rfl
    rw [hden]
    -- Cancel `κ` in `(κ * a) / (κ * b)`.
    simpa using
      (ENNReal.mul_div_mul_left (a := (w1E + w2E)) (b := (w1E + w2E + 1))
        (c := κ) hκ0 hκT)
  -- Convert the RHS to `ℝ` and match the MeTTa formula.
  have hw_nonneg : 0 ≤ c2w t1.c + c2w t2.c := by
    linarith [c2w_nonneg t1.c, c2w_nonneg t2.c]
  -- Rewrite the Evidence-side `toReal` explicitly.
  have hw1E_ne_top : w1E ≠ (⊤ : ℝ≥0∞) := by
    -- `a/b` is finite if `a` is finite and `b ≠ 0`.
    apply ENNReal.div_ne_top ENNReal.ofReal_ne_top
    have hpos : 0 < 1 - capConf t1.c := by
      have : capConf t1.c < 1 := capConf_lt_one t1.c
      linarith
    intro h0
    have : (1 - capConf t1.c) ≤ 0 := (ENNReal.ofReal_eq_zero).1 h0
    linarith
  have hw2E_ne_top : w2E ≠ (⊤ : ℝ≥0∞) := by
    apply ENNReal.div_ne_top ENNReal.ofReal_ne_top
    have hpos : 0 < 1 - capConf t2.c := by
      have : capConf t2.c < 1 := capConf_lt_one t2.c
      linarith
    intro h0
    have : (1 - capConf t2.c) ≤ 0 := (ENNReal.ofReal_eq_zero).1 h0
    linarith
  have hwsum_ne_top : w1E + w2E ≠ (⊤ : ℝ≥0∞) :=
    (ENNReal.add_ne_top).2 ⟨hw1E_ne_top, hw2E_ne_top⟩
  have hw1E_toReal : w1E.toReal = c2w t1.c := by
    -- Unfold and use `toReal_div`.
    have hden0 : 0 ≤ 1 - capConf t1.c := by
      have : capConf t1.c ≤ 1 := le_of_lt (capConf_lt_one t1.c)
      linarith
    simp [w1E, c2w, ENNReal.toReal_ofReal (capConf_nonneg t1.c),
      ENNReal.toReal_ofReal hden0]
  have hw2E_toReal : w2E.toReal = c2w t2.c := by
    have hden0 : 0 ≤ 1 - capConf t2.c := by
      have : capConf t2.c ≤ 1 := le_of_lt (capConf_lt_one t2.c)
      linarith
    simp [w2E, c2w, ENNReal.toReal_ofReal (capConf_nonneg t2.c),
      ENNReal.toReal_ofReal hden0]
  have hwsum_toReal : (w1E + w2E).toReal = c2w t1.c + c2w t2.c := by
    -- Use `toReal_add` for finite addends.
    simpa [hw1E_toReal, hw2E_toReal] using (ENNReal.toReal_add hw1E_ne_top hw2E_ne_top)
  have hwsum1_toReal : (w1E + w2E + 1).toReal = c2w t1.c + c2w t2.c + 1 := by
    have h1_ne_top : (1 : ℝ≥0∞) ≠ ⊤ := by simp
    -- `(w1E+w2E+1) = (w1E+w2E) + 1`
    have := ENNReal.toReal_add hwsum_ne_top h1_ne_top
    -- rewrite the LHS/RHS
    simpa [add_assoc, hwsum_toReal] using this
  -- Finish by rewriting both sides to the same real expression.
  have hmin :
      min 1 ((c2w t1.c + c2w t2.c) / (c2w t1.c + c2w t2.c + 1)) =
        (c2w t1.c + c2w t2.c) / (c2w t1.c + c2w t2.c + 1) := by
    have hden_pos : 0 < c2w t1.c + c2w t2.c + 1 := by linarith
    have hle : (c2w t1.c + c2w t2.c) / (c2w t1.c + c2w t2.c + 1) ≤ 1 := by
      rw [div_le_iff₀ hden_pos]
      linarith
    simpa [min_eq_left hle]
  -- Now expand both `truthRevision` and the Evidence side.
  -- `hconf` rewrites the Evidence confidence to `((w1E+w2E)/(w1E+w2E+1)).toReal`.
  -- Then `toReal_div` + the `toReal_add` computations above finish.
  simp [truthRevision, hconf, ENNReal.toReal_div, hwsum_toReal, hwsum1_toReal,
    w2c_eq_div_of_nonneg _ hw_nonneg, hmin]

/-- Revision strength agrees with `Evidence.toStrength` after mapping STVs to evidence and adding,
assuming a single finite `κ` and strengths in `[0,1]`. -/
theorem truthRevision_strength_eq_toStrength
    (κ : ℝ≥0∞) (hκ0 : κ ≠ 0) (hκT : κ ≠ ⊤)
    (t1 t2 : TV)
    (hs1 : 0 ≤ t1.s) (hs1' : t1.s ≤ 1)
    (hs2 : 0 ≤ t2.s) (hs2' : t2.s ≤ 1) :
    (truthRevision t1 t2).s =
      (Evidence.toStrength (TV.toEvidence κ t1 + TV.toEvidence κ t2)).toReal := by
  -- Real weights used by the MeTTa revision formula.
  set w1 : ℝ := c2w t1.c
  set w2 : ℝ := c2w t2.c
  set w : ℝ := w1 + w2
  have hw1 : 0 ≤ w1 := by simpa [w1] using c2w_nonneg t1.c
  have hw2 : 0 ≤ w2 := by simpa [w2] using c2w_nonneg t2.c
  have hw : 0 ≤ w := by linarith [hw1, hw2]

  -- The `min 1` clamp in `truthRevision` is redundant: the (safe) weighted average is ≤ 1.
  have hf_le : safeDiv (w1 * t1.s + w2 * t2.s) w ≤ 1 := by
    by_cases hwpos : 0 < w
    · -- `safeDiv` uses ordinary division.
      simp [safeDiv, hwpos]
      -- Bound each term by its weight.
      have h1 : w1 * t1.s ≤ w1 := by
        have := mul_le_mul_of_nonneg_left hs1' hw1
        simpa using this
      have h2 : w2 * t2.s ≤ w2 := by
        have := mul_le_mul_of_nonneg_left hs2' hw2
        simpa using this
      have hnum : w1 * t1.s + w2 * t2.s ≤ w1 + w2 := by linarith [h1, h2]
      -- Divide by a positive denominator.
      rw [div_le_iff₀ hwpos]
      dsimp [w]
      linarith [hnum]
    · have hw0 : w = 0 := le_antisymm (le_of_not_gt hwpos) hw
      simp [safeDiv, hw0]
  have hmin : min 1 (safeDiv (w1 * t1.s + w2 * t2.s) w) = safeDiv (w1 * t1.s + w2 * t2.s) w :=
    min_eq_right hf_le

  have lhs : (truthRevision t1 t2).s = safeDiv (w1 * t1.s + w2 * t2.s) w := by
    simp [truthRevision, w1, w2, w, hmin]

  -- ENNReal weights (the Evidence-side analogue of `w1`, `w2`).
  set w1E : ℝ≥0∞ := ENNReal.ofReal (capConf t1.c) / ENNReal.ofReal (1 - capConf t1.c)
  set w2E : ℝ≥0∞ := ENNReal.ofReal (capConf t2.c) / ENNReal.ofReal (1 - capConf t2.c)

  have hw1E_ne_top : w1E ≠ (⊤ : ℝ≥0∞) := by
    apply ENNReal.div_ne_top ENNReal.ofReal_ne_top
    have hpos : 0 < 1 - capConf t1.c := by
      have : capConf t1.c < 1 := capConf_lt_one t1.c
      linarith
    intro h0
    have : (1 - capConf t1.c) ≤ 0 := (ENNReal.ofReal_eq_zero).1 h0
    linarith
  have hw2E_ne_top : w2E ≠ (⊤ : ℝ≥0∞) := by
    apply ENNReal.div_ne_top ENNReal.ofReal_ne_top
    have hpos : 0 < 1 - capConf t2.c := by
      have : capConf t2.c < 1 := capConf_lt_one t2.c
      linarith
    intro h0
    have : (1 - capConf t2.c) ≤ 0 := (ENNReal.ofReal_eq_zero).1 h0
    linarith
  have hwsum_ne_top : w1E + w2E ≠ (⊤ : ℝ≥0∞) :=
    (ENNReal.add_ne_top).2 ⟨hw1E_ne_top, hw2E_ne_top⟩

  -- Convert ENNReal weights back to the real weights `w1`, `w2`.
  have hw1E_toReal : w1E.toReal = w1 := by
    have hden0 : 0 ≤ 1 - capConf t1.c := by
      have : capConf t1.c ≤ 1 := le_of_lt (capConf_lt_one t1.c)
      linarith
    simp [w1E, w1, c2w, ENNReal.toReal_ofReal (capConf_nonneg t1.c), ENNReal.toReal_ofReal hden0]
  have hw2E_toReal : w2E.toReal = w2 := by
    have hden0 : 0 ≤ 1 - capConf t2.c := by
      have : capConf t2.c ≤ 1 := le_of_lt (capConf_lt_one t2.c)
      linarith
    simp [w2E, w2, c2w, ENNReal.toReal_ofReal (capConf_nonneg t2.c), ENNReal.toReal_ofReal hden0]
  have hwsum_toReal : (w1E + w2E).toReal = w := by
    simpa [w, hw1E_toReal, hw2E_toReal] using (ENNReal.toReal_add hw1E_ne_top hw2E_ne_top)

  -- Totals only depend on confidence (because `s ∈ [0,1]`).
  have htot1 : (TV.toEvidence κ t1).total = κ * w1E := by
    have := toEvidence_total κ t1 hs1 hs1'
    simpa [w1E, mul_div_assoc] using this
  have htot2 : (TV.toEvidence κ t2).total = κ * w2E := by
    have := toEvidence_total κ t2 hs2 hs2'
    simpa [w2E, mul_div_assoc] using this
  have htot_add : (TV.toEvidence κ t1 + TV.toEvidence κ t2).total =
      (TV.toEvidence κ t1).total + (TV.toEvidence κ t2).total := by
    simp [Evidence.total, Evidence.hplus_def, add_assoc, add_comm, add_left_comm]
  have htotSum : (TV.toEvidence κ t1 + TV.toEvidence κ t2).total = κ * (w1E + w2E) := by
    calc
      (TV.toEvidence κ t1 + TV.toEvidence κ t2).total
          = (TV.toEvidence κ t1).total + (TV.toEvidence κ t2).total := htot_add
      _ = κ * w1E + κ * w2E := by simp [htot1, htot2]
      _ = κ * (w1E + w2E) := by rw [← mul_add]

  -- Positive evidence similarly factors as `κ * (...)`.
  have hpos1 : (TV.toEvidence κ t1).pos = κ * (ENNReal.ofReal t1.s * w1E) := by
    -- Unfold `ofSTV` and rewrite the internal `total` as `κ * w1E`.
    simp [TV.toEvidence, Evidence.ofSTV, w1E, mul_left_comm, mul_div_assoc]
  have hpos2 : (TV.toEvidence κ t2).pos = κ * (ENNReal.ofReal t2.s * w2E) := by
    simp [TV.toEvidence, Evidence.ofSTV, w2E, mul_left_comm, mul_div_assoc]
  have hposSum : (TV.toEvidence κ t1 + TV.toEvidence κ t2).pos =
      κ * (ENNReal.ofReal t1.s * w1E + ENNReal.ofReal t2.s * w2E) := by
    -- Coordinatewise addition on `Evidence`.
    simp [Evidence.hplus_def, hpos1, hpos2, mul_add]

  -- Now compare the two `if` branches: `safeDiv` uses `0 < w` while `toStrength` uses `total = 0`.
  by_cases htotal0 : (TV.toEvidence κ t1 + TV.toEvidence κ t2).total = 0
  · -- Zero total evidence: both return 0.
    have hwsum0 : w1E + w2E = 0 := by
      have : κ * (w1E + w2E) = 0 := by simpa [htotSum] using htotal0
      have : κ = 0 ∨ w1E + w2E = 0 := by simpa [mul_eq_zero] using this
      exact this.resolve_left hκ0
    have hw0 : w = 0 := by
      have : (w1E + w2E).toReal = 0 := by simp [hwsum0]
      simpa [hwsum_toReal] using this
    have hnwpos : ¬ 0 < w := by simp [hw0]
    have hsafe0 : safeDiv (w1 * t1.s + w2 * t2.s) w = 0 := by
      simp [safeDiv, hw0]
    calc
      (truthRevision t1 t2).s = safeDiv (w1 * t1.s + w2 * t2.s) w := lhs
      _ = 0 := hsafe0
      _ = (Evidence.toStrength (TV.toEvidence κ t1 + TV.toEvidence κ t2)).toReal := by
        simp [Evidence.toStrength, htotal0]
  · -- Nonzero total evidence: both use ordinary division.
    have hw_ne0 : w ≠ 0 := by
      intro hw0
      have : (w1E + w2E).toReal = 0 := by simpa [w, hw0] using hwsum_toReal
      have : w1E + w2E = 0 := by
        -- `toReal = 0` implies `= 0 ∨ = ⊤`; but we know it's not `⊤`.
        have hz := (ENNReal.toReal_eq_zero_iff (w1E + w2E)).1 this
        exact hz.resolve_right hwsum_ne_top
      exact htotal0 (by simp [htotSum, this, mul_zero])
    have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw_ne0)
    have hsafediv :
        safeDiv (w1 * t1.s + w2 * t2.s) w = (w1 * t1.s + w2 * t2.s) / w := by
      simp [safeDiv, hwpos]

    -- Evidence strength: cancel the common `κ`.
    have hratio : (TV.toEvidence κ t1 + TV.toEvidence κ t2).pos /
        (TV.toEvidence κ t1 + TV.toEvidence κ t2).total =
        (ENNReal.ofReal t1.s * w1E + ENNReal.ofReal t2.s * w2E) / (w1E + w2E) := by
      rw [hposSum, htotSum]
      simpa [mul_add, mul_assoc] using
        (ENNReal.mul_div_mul_left (a := (ENNReal.ofReal t1.s * w1E + ENNReal.ofReal t2.s * w2E))
          (b := (w1E + w2E)) (c := κ) hκ0 hκT)

    -- Convert the ENNReal division to reals.
    have hnum_toReal :
        (ENNReal.ofReal t1.s * w1E + ENNReal.ofReal t2.s * w2E).toReal =
          t1.s * w1 + t2.s * w2 := by
      have h1ne : ENNReal.ofReal t1.s * w1E ≠ (⊤ : ℝ≥0∞) :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw1E_ne_top
      have h2ne : ENNReal.ofReal t2.s * w2E ≠ (⊤ : ℝ≥0∞) :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw2E_ne_top
      have hadd := ENNReal.toReal_add h1ne h2ne
      have ht1s : (ENNReal.ofReal t1.s).toReal = t1.s := ENNReal.toReal_ofReal hs1
      have ht2s : (ENNReal.ofReal t2.s).toReal = t2.s := ENNReal.toReal_ofReal hs2
      have hmul1 : (ENNReal.ofReal t1.s * w1E).toReal = t1.s * w1 := by
        simp [ENNReal.toReal_mul, ht1s, hw1E_toReal]
      have hmul2 : (ENNReal.ofReal t2.s * w2E).toReal = t2.s * w2 := by
        simp [ENNReal.toReal_mul, ht2s, hw2E_toReal]
      simpa [hmul1, hmul2] using hadd

    have rhs : (Evidence.toStrength (TV.toEvidence κ t1 + TV.toEvidence κ t2)).toReal =
        (t1.s * w1 + t2.s * w2) / w := by
      -- `toStrength` becomes `pos/total` because total ≠ 0.
      simp [Evidence.toStrength, htotal0, hratio, ENNReal.toReal_div, hnum_toReal, hwsum_toReal]

    -- Combine everything.
    calc
      (truthRevision t1 t2).s = safeDiv (w1 * t1.s + w2 * t2.s) w := lhs
      _ = (w1 * t1.s + w2 * t2.s) / w := by simp [hsafediv]
      _ = (t1.s * w1 + t2.s * w2) / w := by ring
      _ = (Evidence.toStrength (TV.toEvidence κ t1 + TV.toEvidence κ t2)).toReal := by
        simpa using rhs.symm


/-- Full bridge: revision in MeTTa view equals evidence aggregation under a single `κ`. -/
theorem truthRevision_eq_toTV_hplus
    (κ : ℝ≥0∞) (hκ0 : κ ≠ 0) (hκT : κ ≠ ⊤)
    (t1 t2 : TV)
    (hs1 : 0 ≤ t1.s) (hs1' : t1.s ≤ 1)
    (hs2 : 0 ≤ t2.s) (hs2' : t2.s ≤ 1) :
    truthRevision t1 t2 = Evidence.toTV κ (TV.toEvidence κ t1 + TV.toEvidence κ t2) := by
  -- Reduce to equality of the two fields.
  have hs :
      (truthRevision t1 t2).s = (Evidence.toTV κ (TV.toEvidence κ t1 + TV.toEvidence κ t2)).s := by
    simpa [Evidence.toTV] using
      (truthRevision_strength_eq_toStrength (κ := κ) hκ0 hκT t1 t2 hs1 hs1' hs2 hs2')
  have hc :
      (truthRevision t1 t2).c = (Evidence.toTV κ (TV.toEvidence κ t1 + TV.toEvidence κ t2)).c := by
    -- `truthRevision_conf_eq_toConfidence` is stated directly against `toConfidence`, which is
    -- exactly the confidence coordinate of `Evidence.toTV`.
    simpa [Evidence.toTV] using
      (truthRevision_conf_eq_toConfidence (κ := κ) hκ0 hκT t1 t2 hs1 hs1' hs2 hs2')
  -- Rebuild the `TV` from its coordinates on both sides.
  calc
    truthRevision t1 t2 = TV.mk (truthRevision t1 t2).s (truthRevision t1 t2).c := by
      symm
      exact TV.eta (truthRevision t1 t2)
    _ = TV.mk (Evidence.toTV κ (TV.toEvidence κ t1 + TV.toEvidence κ t2)).s
          (Evidence.toTV κ (TV.toEvidence κ t1 + TV.toEvidence κ t2)).c := by
      simp [hs, hc]
    _ = Evidence.toTV κ (TV.toEvidence κ t1 + TV.toEvidence κ t2) := by
      exact TV.eta (Evidence.toTV κ (TV.toEvidence κ t1 + TV.toEvidence κ t2))

end Bridge

/-!
## Bridge: Induction/Abduction Confidence = Weight-Space Minimum

The induction and abduction rules use the confidence formula:
  `conf_out = w2c(min(c2w(c1), c2w(c2)))`

This section proves why this is semantically correct from the Evidence perspective.

### Key Insight

When combining two pieces of evidence via induction or abduction:
1. The confidence should be limited by the "weaker" evidence
2. "Weaker" means less total evidence, which corresponds to lower WEIGHT (not lower confidence)
3. Taking min in weight-space correctly identifies the limiting factor

### Weight as Evidence Measure

For Evidence `e` with prior `κ`:
- `total = e.pos + e.neg` is the total evidence count
- `confidence = total / (total + κ)` maps evidence to [0,1)
- `weight = confidence / (1 - confidence) = total / κ` is the evidence-to-prior ratio

The weight transform is monotone: more evidence → higher weight → higher confidence.

### Why Weight-Space Minimum?

When doing induction `B→A, B→C ⊢ A→C`:
- We have evidence `E_BA` for premise B→A with confidence `c1`
- We have evidence `E_BC` for premise B→C with confidence `c2`
- The conclusion's confidence should reflect the weaker premise

The weight-space minimum `w2c(min(c2w(c1), c2w(c2)))` ensures:
- If `E_BA` has less evidence (lower weight), the conclusion is limited by `E_BA`
- If `E_BC` has less evidence (lower weight), the conclusion is limited by `E_BC`
- The conclusion confidence never exceeds either premise confidence
-/

namespace InductionAbductionBridge

open Mettapedia.Logic.PLNMettaTruthFunctions
open Mettapedia.Logic.EvidenceQuantale
open Bridge

/-- The weight transform `w = c/(1-c)` is monotone on [0, MAX_CONF].
    More confidence → more weight. -/
theorem c2w_monotone_on_capped (c1 c2 : ℝ) (h : capConf c1 ≤ capConf c2) :
    c2w c1 ≤ c2w c2 := by
  unfold c2w
  set cc1 := capConf c1
  set cc2 := capConf c2
  have hcc1_nonneg : 0 ≤ cc1 := capConf_nonneg c1
  have hcc1_lt_one : cc1 < 1 := capConf_lt_one c1
  have hcc2_lt_one : cc2 < 1 := capConf_lt_one c2
  have h1cc1_pos : 0 < 1 - cc1 := by linarith
  have h1cc2_pos : 0 < 1 - cc2 := by linarith
  -- Goal: cc1 / (1 - cc1) ≤ cc2 / (1 - cc2)
  -- Cross-multiply: cc1 * (1 - cc2) ≤ cc2 * (1 - cc1)
  rw [div_le_div_iff₀ h1cc1_pos h1cc2_pos]
  -- cc1 - cc1*cc2 ≤ cc2 - cc1*cc2
  -- Simplifies to: cc1 ≤ cc2
  nlinarith [h, hcc1_nonneg]

/-- Capped confidence is idempotent for values already in range. -/
theorem capConf_of_capConf (c : ℝ) : capConf (capConf c) = capConf c := by
  unfold capConf
  have h1 : 0 ≤ max 0 (min c MAX_CONF) := le_max_left 0 _
  have hMAX_nonneg : (0 : ℝ) ≤ MAX_CONF := by unfold MAX_CONF; norm_num
  have h2 : max 0 (min c MAX_CONF) ≤ MAX_CONF := by
    apply max_le hMAX_nonneg
    exact min_le_right c MAX_CONF
  have h3 : min (max 0 (min c MAX_CONF)) MAX_CONF = max 0 (min c MAX_CONF) := min_eq_left h2
  simp only [h3, max_eq_right h1]

/-- The confidence output of induction/abduction equals the minimum of capped input confidences. -/
theorem inductionAbduction_conf_eq_min_capped (c1 c2 : ℝ) :
    w2c (min (c2w c1) (c2w c2)) = min (capConf c1) (capConf c2) :=
  PLNMettaTruthFunctions.w2c_min_c2w c1 c2

/-- Taking min in weight-space preserves the ordering: whichever has lower capped confidence
    also has lower weight. -/
theorem min_c2w_eq_c2w_min_capConf (c1 c2 : ℝ) :
    min (c2w c1) (c2w c2) = c2w (if capConf c1 ≤ capConf c2 then c1 else c2) := by
  by_cases h : capConf c1 ≤ capConf c2
  · simp only [h, ↓reduceIte]
    have hle : c2w c1 ≤ c2w c2 := c2w_monotone_on_capped c1 c2 h
    exact min_eq_left hle
  · push_neg at h
    simp only [not_le.mpr h, ↓reduceIte]
    have hle : c2w c2 ≤ c2w c1 := c2w_monotone_on_capped c2 c1 (le_of_lt h)
    exact min_eq_right hle

/-- The induction/abduction confidence is at most the minimum of input confidences
    when both inputs are non-negative. This is the "conservative" property: the
    conclusion is never more confident than the weakest premise. -/
theorem inductionAbduction_conf_le_min (c1 c2 : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    w2c (min (c2w c1) (c2w c2)) ≤ min c1 c2 := by
  rw [inductionAbduction_conf_eq_min_capped]
  -- min (capConf c1) (capConf c2) ≤ min c1 c2
  -- capConf clamps to [0, MAX_CONF], so capConf x ≤ x when 0 ≤ x
  have h1 : capConf c1 ≤ c1 := by
    unfold capConf
    calc max 0 (min c1 MAX_CONF) ≤ max 0 c1 := max_le_max_left 0 (min_le_left c1 MAX_CONF)
      _ = c1 := max_eq_right hc1
  have h2 : capConf c2 ≤ c2 := by
    unfold capConf
    calc max 0 (min c2 MAX_CONF) ≤ max 0 c2 := max_le_max_left 0 (min_le_left c2 MAX_CONF)
      _ = c2 := max_eq_right hc2
  exact min_le_min h1 h2

/-! ### Semantic Justification: Evidence Interpretation

The weight-space minimum has a clean semantic interpretation in terms of Evidence:

Given Evidence `e` with prior `κ`:
- `weight(e) = e.total / κ`
- `confidence(e) = e.total / (e.total + κ) = weight / (weight + 1)`

So `c2w` extracts the evidence-to-prior ratio, and `w2c` converts it back.

When combining evidence via induction/abduction:
- The output confidence is limited by the premise with less evidence
- This is captured by `min` in weight (evidence) space
-/

/-- For Evidence with prior `κ`, weight = total / κ when confidence < MAX_CONF.

    This theorem shows that the c2w transform on confidence recovers the
    evidence-to-prior ratio, provided the confidence is below the MAX_CONF cap.

    The hypothesis `hconf_lt_max` ensures the capping doesn't kick in:
    `confidence = total / (total + κ) < MAX_CONF`
    which is equivalent to `total < MAX_CONF * κ / (1 - MAX_CONF)`.
-/
theorem weight_eq_total_div_prior (κ : ℝ≥0∞) (e : Evidence) (hκ0 : κ ≠ 0) (hκT : κ ≠ ⊤)
    (_he0 : e.total ≠ 0) (heT : e.total ≠ ⊤)
    (hconf_lt_max : (e.total / (e.total + κ)).toReal < MAX_CONF) :
    ENNReal.toReal (e.total / κ) =
      c2w (Evidence.toConfidence (κ := κ) e).toReal := by
  unfold Evidence.toConfidence c2w capConf
  -- First show confidence is in valid range
  have hκ_pos : 0 < κ := pos_iff_ne_zero.mpr hκ0
  have htotκ_ne_zero : e.total + κ ≠ 0 := ne_of_gt (lt_of_lt_of_le hκ_pos le_add_self)
  have htotκ_ne_top : e.total + κ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨heT, hκT⟩
  -- The confidence as a real
  have hconf_toReal : (e.total / (e.total + κ)).toReal = e.total.toReal / (e.total + κ).toReal := by
    rw [ENNReal.toReal_div]
  -- Show confidence is in [0, MAX_CONF)
  have hconf_nonneg : 0 ≤ (e.total / (e.total + κ)).toReal := by
    rw [hconf_toReal]
    exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have htotκ_pos : 0 < e.total + κ := lt_of_lt_of_le hκ_pos le_add_self
  have hconf_lt_one : (e.total / (e.total + κ)).toReal < 1 := by
    rw [hconf_toReal]
    have hlt : e.total < e.total + κ := ENNReal.lt_add_right heT hκ0
    have hpos : 0 < (e.total + κ).toReal := ENNReal.toReal_pos htotκ_ne_zero htotκ_ne_top
    rw [div_lt_one hpos]
    exact ENNReal.toReal_strict_mono htotκ_ne_top hlt
  -- Now compute c2w using the fact that conf < MAX_CONF
  -- Since 0 ≤ conf < MAX_CONF, max 0 (min conf MAX_CONF) = conf
  have hmin_eq : min ((e.total / (e.total + κ)).toReal) MAX_CONF = (e.total / (e.total + κ)).toReal :=
    min_eq_left (le_of_lt hconf_lt_max)
  have hcap_eq : max 0 (min ((e.total / (e.total + κ)).toReal) MAX_CONF) =
      (e.total / (e.total + κ)).toReal := by
    rw [hmin_eq, max_eq_right hconf_nonneg]
  simp only [hcap_eq]
  -- Now we need: (e.total / κ).toReal = conf / (1 - conf)
  -- where conf = (e.total / (e.total + κ)).toReal
  -- conf = total.toReal / (total + κ).toReal
  -- 1 - conf = κ.toReal / (total + κ).toReal
  -- conf / (1 - conf) = total.toReal / κ.toReal
  have hsum : e.total.toReal + κ.toReal = (e.total + κ).toReal := (ENNReal.toReal_add heT hκT).symm
  have htotκ_toReal_pos : 0 < (e.total + κ).toReal := ENNReal.toReal_pos htotκ_ne_zero htotκ_ne_top
  have hκ_toReal_pos : 0 < κ.toReal := ENNReal.toReal_pos hκ0 hκT
  -- Prove 1 - conf = κ.toReal / (e.total + κ).toReal
  have h1_sub_conf : 1 - (e.total / (e.total + κ)).toReal = κ.toReal / (e.total + κ).toReal := by
    rw [hconf_toReal]
    have h1 : (e.total + κ).toReal / (e.total + κ).toReal = 1 := div_self htotκ_toReal_pos.ne'
    calc 1 - e.total.toReal / (e.total + κ).toReal
        = (e.total + κ).toReal / (e.total + κ).toReal - e.total.toReal / (e.total + κ).toReal := by
          rw [h1]
      _ = ((e.total + κ).toReal - e.total.toReal) / (e.total + κ).toReal := by
          rw [sub_div]
      _ = κ.toReal / (e.total + κ).toReal := by
          congr 1
          linarith [hsum]
  -- The key calculation: show (e.total / κ).toReal = conf / (1 - conf)
  rw [ENNReal.toReal_div, hconf_toReal]
  -- Now goal is: e.total.toReal / κ.toReal =
  --              e.total.toReal / (e.total + κ).toReal / (1 - e.total.toReal / (e.total + κ).toReal)
  -- Use h1_sub_conf after rewriting with hconf_toReal
  have h1_sub : 1 - e.total.toReal / (e.total + κ).toReal = κ.toReal / (e.total + κ).toReal := by
    rw [← hconf_toReal]; exact h1_sub_conf
  rw [h1_sub]
  -- Goal: e.total.toReal / κ.toReal = (e.total.toReal / (e.total + κ).toReal) / (κ.toReal / (e.total + κ).toReal)
  -- Algebra: (a/b) / (c/b) = a/c when b ≠ 0, c ≠ 0
  field_simp [htotκ_toReal_pos.ne', hκ_toReal_pos.ne']

/-- The weight-space minimum semantically corresponds to taking the premise with
    less total evidence as the limiting factor.

    If premise 1 has less evidence (lower weight), then:
    `w2c(min(c2w(c1), c2w(c2))) = c1` (capped)
-/
theorem weight_min_is_limiting_evidence (c1 c2 : ℝ) (h : capConf c1 ≤ capConf c2) :
    w2c (min (c2w c1) (c2w c2)) = capConf c1 := by
  rw [inductionAbduction_conf_eq_min_capped]
  exact min_eq_left h

end InductionAbductionBridge

/-!
## Summary: Induction/Abduction Confidence Bridge

The weight-space minimum formula `w2c(min(c2w(c1), c2w(c2)))` used in PLN induction
and abduction has been shown to:

1. **Equal the minimum of capped confidences** (`inductionAbduction_conf_eq_min_capped`)
2. **Preserve ordering** (`c2w_monotone_on_capped`)
3. **Be conservative** (`inductionAbduction_conf_le_min`) - never exceeds input confidences
4. **Select the limiting evidence** (`weight_min_is_limiting_evidence`)

This justifies the MeTTa implementation:
```metta
(= (Fixed_Conf $c1 $c2)
   (Truth_w2c (min (Truth_c2w $c1) (Truth_c2w $c2))))
```

The "double-damping" bug in the old code used `w2c(min(c1, c2))` which:
- Incorrectly treated confidences as weights
- Led to 10-50% underestimation of output confidence
- Has been fixed in `lib_pln.metta` as of 2025-01
-/

end Mettapedia.Logic.NuEvidenceQuantaleBridge
