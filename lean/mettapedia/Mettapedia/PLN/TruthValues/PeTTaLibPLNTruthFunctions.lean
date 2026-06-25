import Mathlib.Tactic
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInferenceRules

namespace Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions

open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInferenceRules

/-!
# PeTTa `lib_pln.metta` Truth Functions

This file is a transparent Lean transcription of the numerical truth-value rules in:

* `/home/zar/claude/hyperon/PeTTa/lib/lib_pln.metta`
* `https://github.com/trueagi-io/PeTTa/blob/main/lib/lib_pln.metta`

as mirrored from the local PeTTa checkout inspected during this update:

* `/home/zar/claude/hyperon/PeTTa` HEAD `6f734e33533cde865d50bfe5eb449b439235ae89`

This file is intentionally a mirror of that library surface. It is **not** the
place where canonicity or world-model justification is decided. For the
theorem-backed WM/evidence account, see
`Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions`.
-/

/-! ## Simple Truth Values -/

/-- A lightweight (strength, confidence) pair. -/
structure TV where
  s : ℝ
  c : ℝ

namespace TV

@[simp] theorem eta (t : TV) : TV.mk t.s t.c = t := by
  cases t
  rfl

end TV

/-! ## Utility: confidence ↔ weight -/

def MAX_CONF : ℝ := 0.9999

/-- Clamp an arbitrary real into the confidence range `[0, MAX_CONF]`. -/
def capConf (c : ℝ) : ℝ :=
  max 0 (min c MAX_CONF)

theorem capConf_nonneg (c : ℝ) : 0 ≤ capConf c := by
  simp [capConf]

theorem capConf_lt_one (c : ℝ) : capConf c < 1 := by
  have hmax : MAX_CONF < 1 := by
    unfold MAX_CONF
    norm_num
  have hmin : min c MAX_CONF ≤ MAX_CONF := min_le_right c MAX_CONF
  have hle : capConf c ≤ MAX_CONF := by
    have h : max 0 (min c MAX_CONF) ≤ max 0 MAX_CONF := max_le_max_left 0 hmin
    have hMAX0 : (0 : ℝ) ≤ MAX_CONF := by
      unfold MAX_CONF
      norm_num
    have hMAX : max 0 MAX_CONF = MAX_CONF := max_eq_right hMAX0
    simpa [capConf, hMAX] using h
  exact lt_of_le_of_lt hle hmax

noncomputable def c2w (c : ℝ) : ℝ :=
  let cc := capConf c
  cc / (1 - cc)

noncomputable def w2c (w : ℝ) : ℝ :=
  let ww := max 0 w
  ww / (ww + 1)

/-! ## PeTTa `lib_pln.metta` helpers -/

/-- A Lean helper mirroring MeTTa's `/safe`: returns `0` when the denominator is `≤ 0`. -/
noncomputable def safeDiv (a b : ℝ) : ℝ :=
  if 0 < b then a / b else 0

/-! ## PeTTa `lib_pln.metta` truth functions -/

/-- `Truth_Deduction` as mirrored from PeTTa `lib_pln.metta`. -/
noncomputable def truthDeduction (p q r pq qr : TV) : TV :=
by
  classical
  exact
    if conditionalProbabilityConsistency p.s q.s pq.s ∧
       conditionalProbabilityConsistency q.s r.s qr.s then
      let s :=
        if 0.9999 < q.s then
          r.s
        else
          pq.s * qr.s + (1 - pq.s) * (r.s - q.s * qr.s) / (1 - q.s)
      let c := min p.c (min q.c (min r.c (min pq.c qr.c)))
      ⟨s, c⟩
    else
      ⟨1, 0⟩

/-- `Truth_Induction` as mirrored from PeTTa `lib_pln.metta`. -/
noncomputable def truthInduction (a b c ba bc : TV) : TV :=
  let s := plnInductionStrength ba.s bc.s a.s b.s c.s
  let conf := w2c (min (c2w ba.c) (c2w bc.c))
  ⟨s, conf⟩

/-- `Truth_Abduction` as mirrored from PeTTa `lib_pln.metta`. -/
noncomputable def truthAbduction (a b c ab cb : TV) : TV :=
  let s := plnAbductionStrength ab.s cb.s a.s b.s c.s
  let conf := w2c (min (c2w ab.c) (c2w cb.c))
  ⟨s, conf⟩

/-- SourceRule (cospan completion): alias of `truthInduction`. -/
noncomputable abbrev truthSourceRule := truthInduction

/-- SinkRule (span completion): alias of `truthAbduction`. -/
noncomputable abbrev truthSinkRule := truthAbduction

/-- `Truth_ModusPonens` as mirrored from PeTTa `lib_pln.metta`. -/
noncomputable def truthModusPonens (p pq : TV) : TV :=
  ⟨modusPonens pq.s p.s 0.02, p.c * pq.c⟩

/-- `Truth_SymmetricModusPonens` as mirrored from PeTTa `lib_pln.metta`. -/
noncomputable def truthSymmetricModusPonens (a ab : TV) : TV :=
  let snotAB : ℝ := 0.2
  let cnotAB : ℝ := 1.0
  let s := a.s * ab.s + snotAB * (1 - a.s) * (1 + ab.s)
  let c := min (min ab.c cnotAB) a.c
  ⟨s, c⟩

/-- `Truth_Revision` as mirrored from PeTTa `lib_pln.metta`. -/
noncomputable def truthRevision (t1 t2 : TV) : TV :=
  let w1 := c2w t1.c
  let w2 := c2w t2.c
  let w := w1 + w2
  let f := safeDiv (w1 * t1.s + w2 * t2.s) w
  let c := w2c w
  ⟨min 1 f, min 1 c⟩

/-- `Truth_Negation` as mirrored from PeTTa `lib_pln.metta`. -/
noncomputable def truthNegation (t : TV) : TV :=
  ⟨1 - t.s, t.c⟩

/-! ## Additional OpenCog / PeTTa WIP heuristic rules -/

/-- `Truth_inversion` as mirrored from PeTTa `lib_pln.metta`. -/
noncomputable def truthInversion (b ab : TV) : TV :=
  ⟨ab.s, b.c * (ab.c * 0.6)⟩

/-- `Truth_equivalenceToImplication` as mirrored from PeTTa `lib_pln.metta`. -/
noncomputable def truthEquivalenceToImplication (a b ab : TV) : TV :=
  let conclS :=
    if 0.99 < ab.s * ab.c then
      ab.s
    else
      safeDiv ((1 + safeDiv b.s a.s) * ab.s) (1 + ab.s)
  ⟨conclS, ab.c⟩

/-- Strength-level helper corresponding to `TransitiveSimilarityStrength` in PeTTa `lib_pln.metta`. -/
noncomputable def transitiveSimilarityStrength (simAB simBC sA sB sC : ℝ) : ℝ :=
  transitiveSimilarity simAB simBC sA sB sC

/-- `Truth_transitiveSimilarity` as mirrored from PeTTa `lib_pln.metta`. -/
noncomputable def truthTransitiveSimilarity (a b c ab bc : TV) : TV :=
  let s := transitiveSimilarityStrength ab.s bc.s a.s b.s c.s
  let conf := min ab.c bc.c
  ⟨s, conf⟩

/-- Partial version of the deduction-strength helper used by PeTTa `lib_pln.metta`. -/
noncomputable def simpleDeductionStrength (sA sB sC sAB sBC : ℝ) : Option ℝ := by
  classical
  exact
    if conditionalProbabilityConsistency sA sB sAB ∧
       conditionalProbabilityConsistency sB sC sBC then
      if 0.99 < sB then some sC else
        some (sAB * sBC + safeDiv ((1 - sAB) * (sC - sB * sBC)) (1 - sB))
    else
      none

/-- `Truth_evaluationImplication` as mirrored from PeTTa `lib_pln.metta`. -/
noncomputable def truthEvaluationImplication (a b c ab ac : TV) : Option TV :=
  match simpleDeductionStrength b.s a.s c.s ab.s ac.s with
  | none => none
  | some s =>
      let conf :=
        (0.9 * 0.9) *
          min b.c (min a.c (min c.c (min ac.c (0.9 * ab.c))))
      some ⟨s, conf⟩

/-! ## Small transport lemmas -/

theorem truthInduction_s_eq (a b c ba bc : TV) :
    (truthInduction a b c ba bc).s = plnInductionStrength ba.s bc.s a.s b.s c.s := by
  simp [truthInduction]

theorem truthAbduction_s_eq (a b c ab cb : TV) :
    (truthAbduction a b c ab cb).s = plnAbductionStrength ab.s cb.s a.s b.s c.s := by
  simp [truthAbduction]

theorem truthInduction_c_eq_weight_min (a b c ba bc : TV) :
    (truthInduction a b c ba bc).c = w2c (min (c2w ba.c) (c2w bc.c)) := by
  simp [truthInduction]

theorem truthAbduction_c_eq_weight_min (a b c ab cb : TV) :
    (truthAbduction a b c ab cb).c = w2c (min (c2w ab.c) (c2w cb.c)) := by
  simp [truthAbduction]

/-- `w2c (c2w c)` reduces to the capped confidence `capConf c`. -/
theorem w2c_c2w_eq_capConf (c : ℝ) : w2c (c2w c) = capConf c := by
  unfold c2w w2c
  set cc : ℝ := capConf c
  have hcc0 : 0 ≤ cc := by
    simp [cc, capConf]
  have hcc1 : cc < 1 := by
    simpa [cc] using capConf_lt_one c
  have hcc1pos : 0 < 1 - cc := by
    linarith
  have hw0 : 0 ≤ cc / (1 - cc) := div_nonneg hcc0 (le_of_lt hcc1pos)
  simp [cc, hw0]
  have hne : (1 - cc) ≠ 0 := by
    linarith
  have hden : cc / (1 - cc) + 1 = 1 / (1 - cc) := by
    field_simp [hne]
    ring
  rw [hden]
  rw [div_div]
  have hmul : (1 - cc) * (1 / (1 - cc)) = 1 := by
    simp [div_eq_mul_inv, hne]
  rw [hmul]
  simp

/-- `w2c` is monotone. -/
theorem w2c_monotone : Monotone w2c := by
  intro a b hab
  unfold w2c
  have hmax : max 0 a ≤ max 0 b := max_le_max_left 0 hab
  set aa : ℝ := max 0 a
  set bb : ℝ := max 0 b
  have haa : 0 ≤ aa := by simp [aa]
  have hbb : 0 ≤ bb := by simp [bb]
  have hdenA : 0 < aa + 1 := by linarith
  have hdenB : 0 < bb + 1 := by linarith
  have : aa / (aa + 1) ≤ bb / (bb + 1) := by
    rw [div_le_div_iff₀ hdenA hdenB]
    nlinarith [hmax]
  simpa [aa, bb] using this

theorem w2c_min_c2w (c1 c2 : ℝ) :
    w2c (min (c2w c1) (c2w c2)) = min (capConf c1) (capConf c2) := by
  have hmono : Monotone w2c := w2c_monotone
  simpa [w2c_c2w_eq_capConf] using (hmono.map_min (a := c2w c1) (b := c2w c2))

end Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions
