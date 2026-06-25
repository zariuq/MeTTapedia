import Mathlib.Tactic
import Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions
import Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions
import Mettapedia.PLN.TruthValues.PLNBugAnalysis
import Mettapedia.PLN.Evidence.NuEvidenceQuantaleBridge
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInferenceRules

namespace Mettapedia.PLN.Comparisons.PeTTa.PeTTaLibPLNFormalAnalysis

open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions

abbrev TV := Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.TV
abbrev MAX_CONF := Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.MAX_CONF
abbrev capConf := Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf

/-!
# Formal Analysis of PeTTa `lib_pln.metta`

This file compares the transparent local PeTTa `lib_pln.metta` mirror
against the current WM-backed justified truth-function layer, and keeps
the historical raw-min confidence bug visible via `PLNBugAnalysis`.

Reading guide:

* exact equality theorems mean the upstream PeTTa library formula already
  matches the justified Lean rule;
* disagreement / counterexample theorems mark places where historical or
  canonical formulas disagree with the current WM-backed layer;
* bound theorems mean a library formula is conservative / admissible, but not
  yet promoted to a uniquely canonical WM rule;
* canonical-upstream theorems compare the upstream `hyperon/PLN/lib_pln.metta`
  confidence family against both the PeTTa mirror and the WM-justified layer;
* for mirror-only rules, we record the strongest formal analogue currently available
  and prove what we can about its relation to the mirrored library formula.

Public upstream-main reference:

* `https://github.com/trueagi-io/PeTTa/blob/main/lib/lib_pln.metta`

## Reading this file if you are not a Lean user

The *story* lives in (i) section headers, (ii) theorem and definition
names, and (iii) their plain-English docstrings (`/-- ... -/`). Proof
bodies — the blocks starting with `by` — are machine verification and
can be skipped on first read.

Lean syntax you will see:

* `TV.s`, `TV.c` are accessor dot-notation; for a truth value `t`,
  `t.s` is its strength and `t.c` its confidence.
* `Set.Icc a b` is the closed interval `[a, b]`; appears as in-range
  hypotheses on inputs.
* `theorem foo : … := by …` is a claim followed by its proof. The
  claim is everything before `:=`; the proof lives after `by` and can
  be skipped.
* `noncomputable def` introduces a real-valued function defined via
  classical reals; semantically identical to a PLN/MeTTa formula, just
  not kernel-executable.
* Anonymous-constructor `⟨a, b⟩` builds a pair / structure value; e.g.
  `⟨0.7, 0.9⟩` for a TV with strength 0.7 and confidence 0.9.

PLN-adjacent auxiliary symbols used throughout:

* `MAX_CONF = 0.9999` — the hard confidence cap (a confidence of 1 is
  disallowed so that more evidence can always raise it).
* `c2w c = c / (1 - c)` — confidence → evidence weight.
* `w2c w = w / (w + 1)` — evidence weight → confidence (inverse of
  `c2w`).
* `capConf c = max 0 (min c MAX_CONF)` — clip into `[0, MAX_CONF]`.

**The running story.** The current local PeTTa mirror computes
induction/abduction confidence as
`w2c (min (c2w cBA) (c2w cBC))`: the min is taken in weight space, then
converted back. A theorem in the WM file
(`truthInduction_conf_eq_min_capped`) proves that this round-trip equals
`min (capConf cBA) (capConf cBC)` — the intuitive "your chained
confidence is the weaker of your two inputs'".

The old raw-min formula `w2c (min cBA cBC)` is retained only as a
historical bug surface in `PLNBugAnalysis`: it takes the min of two
*confidences* and then passes that min *back through* `w2c` as if it
were a *weight*. That is the "double damping" bug: a confidence of 0.5
becomes `0.5 / 1.5 ≈ 0.333`.
-/

/-- **Workhorse lemma.** The weight-to-confidence map
`w2c(w) = w / (w+1)` never inflates: for nonneg `w`, `w2c(w) ≤ w`.
This is the single step that drives the canonical-below-PeTTa-below-WM
ordering proofs lower down in this file. Intuition: as evidence grows,
confidence approaches but never reaches 1, so the map always lands on
or below the diagonal. -/
theorem pettaw2c_le_self (w : ℝ) (hw : 0 ≤ w) :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c w ≤ w := by
  rw [Mettapedia.PLN.Evidence.NuEvidenceQuantaleBridge.Bridge.w2c_eq_div_of_nonneg w hw]
  have hden : 0 < w + 1 := by
    linarith
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg w]

/-- On any confidence already in the legal range `[0, MAX_CONF]`,
clipping does nothing: `capConf c = c`. Used to collapse "min of
capped confidences" to "min of confidences" in downstream theorems
without extra qualifiers. -/
theorem capConf_eq_self_of_mem_core (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ MAX_CONF) :
    capConf c = c := by
  have h1' : c ≤ Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.MAX_CONF := by
    simpa [MAX_CONF] using h1
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf, h0, h1']

namespace CanonicalUpstream

/-- Upstream canonical deduction confidence from `/home/zar/claude/hyperon/PLN/lib_pln.metta`. -/
noncomputable def truthDeductionConf (pq qr : TV) : ℝ :=
  pq.s * qr.s * pq.c * qr.c

/-- Upstream canonical induction confidence from `/home/zar/claude/hyperon/PLN/lib_pln.metta`. -/
noncomputable def truthInductionConf (ba bc : TV) : ℝ :=
  Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c (bc.s * bc.c * ba.c)

/-- Upstream canonical abduction confidence from `/home/zar/claude/hyperon/PLN/lib_pln.metta`. -/
noncomputable def truthAbductionConf (ab cb : TV) : ℝ :=
  Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c (ab.s * ab.c * cb.c)

/-- Upstream canonical modus-ponens confidence from `/home/zar/claude/hyperon/PLN/lib_pln.metta`. -/
noncomputable def truthModusPonensConf (p pq : TV) : ℝ :=
  p.s * pq.s * p.c * pq.c

/-- Upstream canonical disjunction helper from `/home/zar/claude/hyperon/PLN/lib_pln.metta`. -/
noncomputable def truthOr (a b : ℝ) : ℝ :=
  1 - (1 - a) * (1 - b)

/-- Upstream canonical symmetric-modus-ponens confidence from `/home/zar/claude/hyperon/PLN/lib_pln.metta`. -/
noncomputable def truthSymmetricModusPonensConf (a ab : TV) : ℝ :=
  a.c * ab.c * truthOr a.s ab.s

/-- Upstream canonical transitive-similarity confidence from `/home/zar/claude/hyperon/PLN/lib_pln.metta`. -/
noncomputable def truthTransitiveSimilarityConf (ab bc : TV) : ℝ :=
  ab.c * bc.c * truthOr ab.s bc.s

end CanonicalUpstream

theorem canonical_truthOr_mem_unit {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    CanonicalUpstream.truthOr a b ∈ Set.Icc (0 : ℝ) 1 := by
  unfold CanonicalUpstream.truthOr
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

/-! ## Canonical upstream as a third comparison lane -/

theorem canonicalInduction_conf_le_inputs
    (ba bc : TV)
    (hbcS : bc.s ∈ Set.Icc (0 : ℝ) 1)
    (hbaC : ba.c ∈ Set.Icc (0 : ℝ) MAX_CONF)
    (hbcC : bc.c ∈ Set.Icc (0 : ℝ) MAX_CONF) :
    CanonicalUpstream.truthInductionConf ba bc ≤ min ba.c bc.c := by
  unfold CanonicalUpstream.truthInductionConf
  let w : ℝ := bc.s * bc.c * ba.c
  have hMAX : MAX_CONF ≤ 1 := by
    norm_num [MAX_CONF, Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.MAX_CONF]
  have hbaC1 : ba.c ≤ 1 := by
    linarith [hbaC.2, hMAX]
  have hbcC1 : bc.c ≤ 1 := by
    linarith [hbcC.2, hMAX]
  have hw0 : 0 ≤ w := by
    unfold w
    exact mul_nonneg (mul_nonneg hbcS.1 hbcC.1) hbaC.1
  have hw_le_ba : w ≤ ba.c := by
    unfold w
    have hfac : bc.s * bc.c ≤ 1 := by
      nlinarith [hbcS.1, hbcS.2, hbcC.1, hbcC1]
    nlinarith [hfac, hbaC.1]
  have hw_le_bc : w ≤ bc.c := by
    unfold w
    have hfac : bc.s * ba.c ≤ 1 := by
      nlinarith [hbcS.1, hbcS.2, hbaC.1, hbaC1]
    nlinarith [hfac, hbcC.1]
  have hw_le_min : w ≤ min ba.c bc.c := by
    exact le_min hw_le_ba hw_le_bc
  exact le_trans (pettaw2c_le_self w hw0) hw_le_min

/-- **Ordering step 1 of 2 (induction).** The original canonical PLN
induction confidence — the strength-mixed form `w2c (sBC · cBC · cBA)`
— is always ≤ the current PeTTa / WM weight-min form on in-range inputs.

Why: `sBC · cBC · cBA` is pointwise ≤ `min cBA cBC` (a product of things
in `[0,1]` lies below any factor), while the current PeTTa formula
collapses to exactly that min on already-clipped inputs. So the canonical
form is strictly more cautious than the current weight-min family. -/
theorem canonicalInduction_conf_le_petta_wm
    (a b c ba bc : TV)
    (hbcS : bc.s ∈ Set.Icc (0 : ℝ) 1)
    (hbaC : ba.c ∈ Set.Icc (0 : ℝ) MAX_CONF)
    (hbcC : bc.c ∈ Set.Icc (0 : ℝ) MAX_CONF) :
    CanonicalUpstream.truthInductionConf ba bc ≤
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c := by
  have hcanon := canonicalInduction_conf_le_inputs ba bc hbcS hbaC hbcC
  have hpetta :
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c =
        min ba.c bc.c := by
    rw [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction_c_eq_weight_min,
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c_min_c2w]
    change min (capConf ba.c) (capConf bc.c) = min ba.c bc.c
    rw [capConf_eq_self_of_mem_core ba.c hbaC.1 hbaC.2,
      capConf_eq_self_of_mem_core bc.c hbcC.1 hbcC.2]
  rw [hpetta]
  exact hcanon

/-- **Ordering step 2 of 2 (induction): the full three-lane chain.**
For in-range inputs, `canonical ≤ PeTTa-main = WM-justified`:

* canonical is the strength-mixed `w2c (sBC · cBC · cBA)`,
* PeTTa-main is the corrected weight-min form,
* WM-justified is the same corrected weight-min form.

So the current local PeTTa mirror is no longer an intermediate buggy
lane; it agrees with the WM form on the induction confidence component. -/
theorem canonicalInduction_conf_le_wm_best
    (a b c ba bc : TV)
    (hbcS : bc.s ∈ Set.Icc (0 : ℝ) 1)
    (hbaC : ba.c ∈ Set.Icc (0 : ℝ) MAX_CONF)
    (hbcC : bc.c ∈ Set.Icc (0 : ℝ) MAX_CONF) :
    CanonicalUpstream.truthInductionConf ba bc ≤
      (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInduction a b c ba bc).c := by
  have hcanon := canonicalInduction_conf_le_inputs ba bc hbcS hbaC hbcC
  have hwm_eq :
      (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInduction a b c ba bc).c =
        min ba.c bc.c := by
    rw [Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInduction_conf_eq_min_capped]
    change min (capConf ba.c) (capConf bc.c) = min ba.c bc.c
    rw [capConf_eq_self_of_mem_core ba.c hbaC.1 hbaC.2,
      capConf_eq_self_of_mem_core bc.c hbcC.1 hbcC.2]
  rw [hwm_eq]
  exact hcanon

theorem canonicalAbduction_conf_le_inputs
    (ab cb : TV)
    (habS : ab.s ∈ Set.Icc (0 : ℝ) 1)
    (habC : ab.c ∈ Set.Icc (0 : ℝ) MAX_CONF)
    (hcbC : cb.c ∈ Set.Icc (0 : ℝ) MAX_CONF) :
    CanonicalUpstream.truthAbductionConf ab cb ≤ min ab.c cb.c := by
  unfold CanonicalUpstream.truthAbductionConf
  let w : ℝ := ab.s * ab.c * cb.c
  have hMAX : MAX_CONF ≤ 1 := by
    norm_num [MAX_CONF, Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.MAX_CONF]
  have habC1 : ab.c ≤ 1 := by
    linarith [habC.2, hMAX]
  have hcbC1 : cb.c ≤ 1 := by
    linarith [hcbC.2, hMAX]
  have hw0 : 0 ≤ w := by
    unfold w
    exact mul_nonneg (mul_nonneg habS.1 habC.1) hcbC.1
  have hw_le_ab : w ≤ ab.c := by
    unfold w
    have hfac : ab.s * cb.c ≤ 1 := by
      nlinarith [habS.1, habS.2, hcbC.1, hcbC1]
    nlinarith [hfac, habC.1]
  have hw_le_cb : w ≤ cb.c := by
    unfold w
    have hfac : ab.s * ab.c ≤ 1 := by
      nlinarith [habS.1, habS.2, habC.1, habC1]
    nlinarith [hfac, hcbC.1]
  have hw_le_min : w ≤ min ab.c cb.c := by
    exact le_min hw_le_ab hw_le_cb
  exact le_trans (pettaw2c_le_self w hw0) hw_le_min

theorem canonicalAbduction_conf_le_petta_wm
    (a b c ab cb : TV)
    (habS : ab.s ∈ Set.Icc (0 : ℝ) 1)
    (habC : ab.c ∈ Set.Icc (0 : ℝ) MAX_CONF)
    (hcbC : cb.c ∈ Set.Icc (0 : ℝ) MAX_CONF) :
    CanonicalUpstream.truthAbductionConf ab cb ≤
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c := by
  have hcanon := canonicalAbduction_conf_le_inputs ab cb habS habC hcbC
  have hpetta :
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c =
        min ab.c cb.c := by
    rw [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction_c_eq_weight_min,
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c_min_c2w]
    change min (capConf ab.c) (capConf cb.c) = min ab.c cb.c
    rw [capConf_eq_self_of_mem_core ab.c habC.1 habC.2,
      capConf_eq_self_of_mem_core cb.c hcbC.1 hcbC.2]
  rw [hpetta]
  exact hcanon

theorem canonicalAbduction_conf_le_wm_best
    (a b c ab cb : TV)
    (habS : ab.s ∈ Set.Icc (0 : ℝ) 1)
    (habC : ab.c ∈ Set.Icc (0 : ℝ) MAX_CONF)
    (hcbC : cb.c ∈ Set.Icc (0 : ℝ) MAX_CONF) :
    CanonicalUpstream.truthAbductionConf ab cb ≤
      (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthAbduction a b c ab cb).c := by
  have hcanon := canonicalAbduction_conf_le_inputs ab cb habS habC hcbC
  have hwm_eq :
      (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthAbduction a b c ab cb).c =
        min ab.c cb.c := by
    rw [Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthAbduction_conf_eq_min_capped]
    change min (capConf ab.c) (capConf cb.c) = min ab.c cb.c
    rw [capConf_eq_self_of_mem_core ab.c habC.1 habC.2,
      capConf_eq_self_of_mem_core cb.c hcbC.1 hcbC.2]
  rw [hwm_eq]
  exact hcanon

theorem canonicalDeduction_conf_le_edge_inputs
    (pq qr : TV)
    (hpqS : pq.s ∈ Set.Icc (0 : ℝ) 1)
    (hqrS : qr.s ∈ Set.Icc (0 : ℝ) 1)
    (hpqC : pq.c ∈ Set.Icc (0 : ℝ) 1)
    (hqrC : qr.c ∈ Set.Icc (0 : ℝ) 1) :
    CanonicalUpstream.truthDeductionConf pq qr ≤ pq.c ∧
    CanonicalUpstream.truthDeductionConf pq qr ≤ qr.c := by
  constructor
  · unfold CanonicalUpstream.truthDeductionConf
    have hprod : pq.s * qr.s ≤ 1 := by
      nlinarith [hpqS.1, hpqS.2, hqrS.1, hqrS.2]
    have hfac : pq.s * qr.s * qr.c ≤ 1 := by
      have hmul : pq.s * qr.s * qr.c ≤ 1 * qr.c := by
        exact mul_le_mul_of_nonneg_right hprod hqrC.1
      nlinarith [hmul, hqrC.2]
    nlinarith [hfac, hpqC.1]
  · unfold CanonicalUpstream.truthDeductionConf
    have hprod : pq.s * qr.s ≤ 1 := by
      nlinarith [hpqS.1, hpqS.2, hqrS.1, hqrS.2]
    have hfac : pq.s * qr.s * pq.c ≤ 1 := by
      have hmul : pq.s * qr.s * pq.c ≤ 1 * pq.c := by
        exact mul_le_mul_of_nonneg_right hprod hpqC.1
      nlinarith [hmul, hpqC.2]
    nlinarith [hfac, hqrC.1]

/-- **Negative result — deduction is different.**

For induction and abduction, canonical PLN's confidence is always
below PeTTa's form (proved above). **For deduction, that ordering fails.**

Witness: set `p = q = r = (strength = 1, confidence = 0.1)` and
`pq = qr = (strength = 1, confidence = 1)`. Then canonical deduction's
confidence is `1 · 1 · 1 · 1 = 1`, while PeTTa's min-of-five is
`min(0.1, 0.1, 0.1, 1, 1) = 0.1`. Canonical overshoots.

So no clean "canonical is always more conservative" rule holds for
deduction; the shapes genuinely disagree, not just in magnitude. This
is why the four-family table needs to keep deduction as a separate
story from induction/abduction. -/
theorem canonicalDeduction_not_le_petta_wm_globally :
    ∃ p q r pq qr : TV,
      CanonicalUpstream.truthDeductionConf pq qr >
        min p.c (min q.c (min r.c (min pq.c qr.c))) := by
  refine ⟨⟨1, 0.1⟩, ⟨1, 0.1⟩, ⟨1, 0.1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ?_⟩
  norm_num [CanonicalUpstream.truthDeductionConf]

theorem canonicalModusPonens_conf_le_petta_wm
    (p pq : TV)
    (hpS : p.s ∈ Set.Icc (0 : ℝ) 1)
    (hpqS : pq.s ∈ Set.Icc (0 : ℝ) 1)
    (hpC : p.c ∈ Set.Icc (0 : ℝ) 1)
    (hpqC : pq.c ∈ Set.Icc (0 : ℝ) 1) :
    CanonicalUpstream.truthModusPonensConf p pq ≤
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthModusPonens p pq).c := by
  unfold CanonicalUpstream.truthModusPonensConf
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthModusPonens]
  have hmulS : p.s * pq.s ≤ 1 := by
    nlinarith [hpS.1, hpS.2, hpqS.1, hpqS.2]
  have hconf_nonneg : 0 ≤ p.c * pq.c := by
    exact mul_nonneg hpC.1 hpqC.1
  nlinarith [hmulS, hconf_nonneg]

theorem canonicalModusPonens_conf_le_wm_best
    (p pq : TV)
    (hpS : p.s ∈ Set.Icc (0 : ℝ) 1)
    (hpqS : pq.s ∈ Set.Icc (0 : ℝ) 1)
    (hpC : p.c ∈ Set.Icc (0 : ℝ) 1)
    (hpqC : pq.c ∈ Set.Icc (0 : ℝ) 1) :
    CanonicalUpstream.truthModusPonensConf p pq ≤
      (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthModusPonensConservative p pq).c := by
  simpa [Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthModusPonensConservative] using
    canonicalModusPonens_conf_le_petta_wm p pq hpS hpqS hpC hpqC

theorem canonicalSymmetricModusPonens_conf_le_petta_wm
    (a ab : TV)
    (haS : a.s ∈ Set.Icc (0 : ℝ) 1)
    (habS : ab.s ∈ Set.Icc (0 : ℝ) 1)
    (haC : a.c ∈ Set.Icc (0 : ℝ) 1)
    (habC : ab.c ∈ Set.Icc (0 : ℝ) 1) :
    CanonicalUpstream.truthSymmetricModusPonensConf a ab ≤
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens a ab).c := by
  have hor : CanonicalUpstream.truthOr a.s ab.s ≤ 1 := (canonical_truthOr_mem_unit haS habS).2
  have habcnonneg : 0 ≤ a.c * ab.c := by
    exact mul_nonneg haC.1 habC.1
  have hprod_le_min : a.c * ab.c ≤ min a.c ab.c := by
    apply le_min <;> nlinarith [haC.1, haC.2, habC.1, habC.2]
  have hscaled : CanonicalUpstream.truthSymmetricModusPonensConf a ab ≤ a.c * ab.c := by
    unfold CanonicalUpstream.truthSymmetricModusPonensConf
    have : a.c * ab.c * CanonicalUpstream.truthOr a.s ab.s ≤ a.c * ab.c * 1 := by
      exact mul_le_mul_of_nonneg_left hor habcnonneg
    simpa using this
  have hmirror :
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens a ab).c =
        min ab.c a.c := by
    have hone : (1.0 : ℝ) = 1 := by norm_num
    simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens,
      hone, habC.2, min_comm]
  rw [hmirror]
  exact le_trans hscaled (by simpa [min_comm] using hprod_le_min)

theorem canonicalSymmetricModusPonens_conf_le_wm_conservative
    (a ab : TV)
    (haS : a.s ∈ Set.Icc (0 : ℝ) 1)
    (habS : ab.s ∈ Set.Icc (0 : ℝ) 1)
    (haC : a.c ∈ Set.Icc (0 : ℝ) 1)
    (habC : ab.c ∈ Set.Icc (0 : ℝ) 1) :
    CanonicalUpstream.truthSymmetricModusPonensConf a ab ≤
      (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthSymmetricModusPonensConservative a ab).c := by
  simpa [Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthSymmetricModusPonensConservative] using
    canonicalSymmetricModusPonens_conf_le_petta_wm a ab haS habS haC habC

theorem canonicalTransitiveSimilarity_conf_le_mirror
    (a b c ab bc : TV)
    (habS : ab.s ∈ Set.Icc (0 : ℝ) 1)
    (hbcS : bc.s ∈ Set.Icc (0 : ℝ) 1)
    (habC : ab.c ∈ Set.Icc (0 : ℝ) 1)
    (hbcC : bc.c ∈ Set.Icc (0 : ℝ) 1) :
    CanonicalUpstream.truthTransitiveSimilarityConf ab bc ≤
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity a b c ab bc).c := by
  have hor : CanonicalUpstream.truthOr ab.s bc.s ≤ 1 := (canonical_truthOr_mem_unit habS hbcS).2
  have habcnonneg : 0 ≤ ab.c * bc.c := by
    exact mul_nonneg habC.1 hbcC.1
  have hprod_le_min : ab.c * bc.c ≤ min ab.c bc.c := by
    apply le_min <;> nlinarith [habC.1, habC.2, hbcC.1, hbcC.2]
  have hscaled : CanonicalUpstream.truthTransitiveSimilarityConf ab bc ≤ ab.c * bc.c := by
    unfold CanonicalUpstream.truthTransitiveSimilarityConf
    have : ab.c * bc.c * CanonicalUpstream.truthOr ab.s bc.s ≤ ab.c * bc.c * 1 := by
      exact mul_le_mul_of_nonneg_left hor habcnonneg
    simpa using this
  have hmirror :
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity a b c ab bc).c =
        min ab.c bc.c := by
    simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity]
  rw [hmirror]
  exact le_trans hscaled hprod_le_min

/-! ## Direct comparison with the justified layer -/

theorem revision_strength_matches_justified (t1 t2 : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthRevision t1 t2).s =
      (truthRevision t1 t2).s := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthRevision,
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthRevision]

/-- **Revision matches the WM-backed rule exactly.**

The current PeTTa mirror and `WMPLNJustifiedTruthFunctions.truthRevision`
use the same confidence formula: add the two evidence weights and convert
back with `w2c`, then apply the same final `min 1` guard. -/
theorem revision_conf_matches_justified (t1 t2 : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthRevision t1 t2).c =
      (truthRevision t1 t2).c := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthRevision,
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthRevision]

theorem revision_matches_justified (t1 t2 : TV) :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthRevision t1 t2 =
      truthRevision t1 t2 := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthRevision,
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthRevision]

theorem induction_strength_matches_justified (a b c ba bc : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).s =
      (truthInduction a b c ba bc).s := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction,
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInduction]

theorem abduction_strength_matches_justified (a b c ab cb : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).s =
      (truthAbduction a b c ab cb).s := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction,
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthAbduction]

theorem induction_conf_matches_justified (a b c ba bc : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c =
      (truthInduction a b c ba bc).c := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction,
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInduction]

theorem abduction_conf_matches_justified (a b c ab cb : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c =
      (truthAbduction a b c ab cb).c := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction,
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthAbduction]

theorem induction_matches_justified (a b c ba bc : TV) :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc =
      truthInduction a b c ba bc := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction,
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInduction]

theorem abduction_matches_justified (a b c ab cb : TV) :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb =
      truthAbduction a b c ab cb := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction,
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthAbduction]

theorem deduction_matches_conservative (p q r pq qr : TV) :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthDeduction p q r pq qr =
      truthDeductionConservative p q r pq qr := rfl

theorem modusPonens_matches_conservative (p pq : TV) :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthModusPonens p pq =
      truthModusPonensConservative p pq := rfl

theorem symmetricModusPonens_matches_conservative (a ab : TV) :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens a ab =
      truthSymmetricModusPonensConservative a ab := rfl

theorem negation_matches_justified (t : TV) :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthNegation t =
      truthNegation t := rfl

/-! ## Core consequences -/

/-- The current PeTTa induction confidence takes the minimum in evidence-weight
space, not in raw confidence space. -/
theorem induction_conf_eq_weight_min (a b c ba bc : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c =
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c
        (min (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w ba.c)
             (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w bc.c)) :=
  Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction_c_eq_weight_min a b c ba bc

/-- Same corrected weight-space confidence shape for abduction. -/
theorem abduction_conf_eq_weight_min (a b c ab cb : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c =
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c
        (min (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w ab.c)
             (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w cb.c)) :=
  Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction_c_eq_weight_min a b c ab cb

theorem induction_conf_eq_min_capped (a b c ba bc : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c =
      min (capConf ba.c) (capConf bc.c) := by
  rw [induction_conf_eq_weight_min,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c_min_c2w]

theorem abduction_conf_eq_min_capped (a b c ab cb : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c =
      min (capConf ab.c) (capConf cb.c) := by
  rw [abduction_conf_eq_weight_min,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c_min_c2w]

theorem induction_conf_le_inputs
    (a b c ba bc : TV) (hba : 0 ≤ ba.c) (hbc : 0 ≤ bc.c) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c ≤
      min ba.c bc.c := by
  simpa [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction,
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInduction] using
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInduction_conf_le_inputs
      a b c ba bc hba hbc

theorem abduction_conf_le_inputs
    (a b c ab cb : TV) (hab : 0 ≤ ab.c) (hcb : 0 ≤ cb.c) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c ≤
      min ab.c cb.c := by
  simpa [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction,
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthAbduction] using
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthAbduction_conf_le_inputs
      a b c ab cb hab hcb

theorem deduction_conf_le_inputs
    (p q r pq qr : TV)
    (hp : 0 ≤ p.c) (hq : 0 ≤ q.c) (hr : 0 ≤ r.c) (hpq : 0 ≤ pq.c) (hqr : 0 ≤ qr.c) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthDeduction p q r pq qr).c ≤ p.c ∧
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthDeduction p q r pq qr).c ≤ q.c ∧
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthDeduction p q r pq qr).c ≤ r.c ∧
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthDeduction p q r pq qr).c ≤ pq.c ∧
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthDeduction p q r pq qr).c ≤ qr.c :=
  truthDeduction_conf_le_inputs p q r pq qr hp hq hr hpq hqr

theorem modusPonens_conf_le_inputs
    (p pq : TV) (hp : p.c ∈ Set.Icc (0 : ℝ) 1) (hpq : pq.c ∈ Set.Icc (0 : ℝ) 1) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthModusPonens p pq).c ≤ p.c ∧
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthModusPonens p pq).c ≤ pq.c :=
  truthModusPonens_conf_le_inputs p pq hp hpq

theorem symmetricModusPonens_conf_le_inputs (a ab : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens a ab).c ≤ a.c ∧
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens a ab).c ≤ ab.c :=
  truthSymmetricModusPonens_conf_le_inputs a ab

/-! ## Concrete anti-bug witnesses -/

theorem capConf_eq_self_of_mem (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ MAX_CONF) :
    capConf c = c := by
  have h1' : c ≤ Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.MAX_CONF := by
    simpa [MAX_CONF] using h1
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf, h0, h1']

/-- **The "obvious right answer" made formal.** The WM-justified
induction confidence, restricted to the standard input range
`[0, MAX_CONF]`, reduces to `min ba.c bc.c` — just the smaller of the
two input confidences.

Both the `capConf` clip and the weight-space round-trip (`c2w` → `min`
→ `w2c`) are invisible when inputs are already well-formed. What
remains is exactly "your chained confidence is the weaker of your two
inputs'." -/
theorem wm_induction_conf_eq_min_of_bounded_inputs
    (a b c ba bc : TV)
    (hba0 : 0 ≤ ba.c) (hba1 : ba.c ≤ MAX_CONF)
    (hbc0 : 0 ≤ bc.c) (hbc1 : bc.c ≤ MAX_CONF) :
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInduction a b c ba bc).c =
      min ba.c bc.c := by
  rw [Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInduction_conf_eq_min_capped]
  change min (capConf ba.c) (capConf bc.c) = min ba.c bc.c
  rw [capConf_eq_self_of_mem ba.c hba0 hba1, capConf_eq_self_of_mem bc.c hbc0 hbc1]

/-- Current PeTTa induction has the same bounded-input confidence as the
WM-backed rule. -/
theorem induction_conf_eq_min_of_bounded_inputs
    (a b c ba bc : TV)
    (hba0 : 0 ≤ ba.c) (hba1 : ba.c ≤ MAX_CONF)
    (hbc0 : 0 ≤ bc.c) (hbc1 : bc.c ≤ MAX_CONF) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c =
      min ba.c bc.c := by
  rw [induction_conf_eq_min_capped]
  rw [capConf_eq_self_of_mem ba.c hba0 hba1, capConf_eq_self_of_mem bc.c hbc0 hbc1]

/-- **Historical bug quantified.** For any strictly-positive in-range input
confidences, the old raw-min formula `w2c (min cBA cBC)` is strictly below
the current PeTTa / WM weight-min value. -/
theorem historical_induction_raw_min_conf_strictly_below_current_on_positive_inputs
    (a b c ba bc : TV)
    (hba0 : 0 < ba.c) (hba1 : ba.c ≤ MAX_CONF)
    (hbc0 : 0 < bc.c) (hbc1 : bc.c ≤ MAX_CONF) :
    Mettapedia.PLN.TruthValues.PLNBugAnalysis.inductionConfBuggy ba.c bc.c <
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c := by
  rw [induction_conf_eq_min_of_bounded_inputs a b c ba bc
    (le_of_lt hba0) hba1 (le_of_lt hbc0) hbc1]
  unfold Mettapedia.PLN.TruthValues.PLNBugAnalysis.inductionConfBuggy
    Mettapedia.PLN.TruthValues.PLNBugAnalysis.w2c'
  let m : ℝ := min ba.c bc.c
  change m / (m + 1) < m
  have hm0 : 0 < m := by
    unfold m
    exact lt_min hba0 hbc0
  have hm_le : m ≤ MAX_CONF := by
    unfold m
    exact min_le_iff.mpr (Or.inl hba1)
  have hm1 : m < 1 := by
    have hMAX : MAX_CONF < 1 := by
      norm_num [MAX_CONF, Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.MAX_CONF]
    exact lt_of_le_of_lt hm_le hMAX
  have hden : 0 < m + 1 := by linarith
  rw [div_lt_iff₀ hden]
  nlinarith [sq_nonneg m]

theorem wm_abduction_conf_eq_min_of_bounded_inputs
    (a b c ab cb : TV)
    (hab0 : 0 ≤ ab.c) (hab1 : ab.c ≤ MAX_CONF)
    (hcb0 : 0 ≤ cb.c) (hcb1 : cb.c ≤ MAX_CONF) :
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthAbduction a b c ab cb).c =
      min ab.c cb.c := by
  rw [Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthAbduction_conf_eq_min_capped]
  change min (capConf ab.c) (capConf cb.c) = min ab.c cb.c
  rw [capConf_eq_self_of_mem ab.c hab0 hab1, capConf_eq_self_of_mem cb.c hcb0 hcb1]

/-- Current PeTTa abduction has the same bounded-input confidence as the
WM-backed rule. -/
theorem abduction_conf_eq_min_of_bounded_inputs
    (a b c ab cb : TV)
    (hab0 : 0 ≤ ab.c) (hab1 : ab.c ≤ MAX_CONF)
    (hcb0 : 0 ≤ cb.c) (hcb1 : cb.c ≤ MAX_CONF) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c =
      min ab.c cb.c := by
  rw [abduction_conf_eq_min_capped]
  rw [capConf_eq_self_of_mem ab.c hab0 hab1, capConf_eq_self_of_mem cb.c hcb0 hcb1]

/-- Historical abduction counterpart: the old raw-min formula is strictly
below the current PeTTa / WM weight-min value on positive in-range inputs. -/
theorem historical_abduction_raw_min_conf_strictly_below_current_on_positive_inputs
    (a b c ab cb : TV)
    (hab0 : 0 < ab.c) (hab1 : ab.c ≤ MAX_CONF)
    (hcb0 : 0 < cb.c) (hcb1 : cb.c ≤ MAX_CONF) :
    Mettapedia.PLN.TruthValues.PLNBugAnalysis.inductionConfBuggy ab.c cb.c <
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c := by
  rw [abduction_conf_eq_min_of_bounded_inputs a b c ab cb
    (le_of_lt hab0) hab1 (le_of_lt hcb0) hcb1]
  unfold Mettapedia.PLN.TruthValues.PLNBugAnalysis.inductionConfBuggy
    Mettapedia.PLN.TruthValues.PLNBugAnalysis.w2c'
  let m : ℝ := min ab.c cb.c
  change m / (m + 1) < m
  have hm0 : 0 < m := by
    unfold m
    exact lt_min hab0 hcb0
  have hm_le : m ≤ MAX_CONF := by
    unfold m
    exact min_le_iff.mpr (Or.inl hab1)
  have hm1 : m < 1 := by
    have hMAX : MAX_CONF < 1 := by
      norm_num [MAX_CONF, Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.MAX_CONF]
    exact lt_of_le_of_lt hm_le hMAX
  have hden : 0 < m + 1 := by linarith
  rw [div_lt_iff₀ hden]
  nlinarith [sq_nonneg m]

/-! ### Concrete anti-bug numerics

Worked side-by-side on identical inputs. With both input confidences
at `0.9`:

* the historical raw-min bug returns `0.9 / 1.9 ≈ 0.473`,
* the current PeTTa / WM-corrected form returns `0.9`.

These are human-checkable numeric witnesses of the strict-below theorem
just above; together they make the bug concrete without needing to
follow any definitions. -/

example :
    let zero : TV := ⟨0, 0⟩
    let ba : TV := ⟨0.7, 0.9⟩
    let bc : TV := ⟨0.8, 0.9⟩
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction zero zero zero ba bc).c = 0.9 := by
  dsimp
  norm_num [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.MAX_CONF]

example :
    let zero : TV := ⟨0, 0⟩
    let ba : TV := ⟨0.7, 0.9⟩
    let bc : TV := ⟨0.8, 0.9⟩
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInduction zero zero zero ba bc).c = 0.9 := by
  dsimp
  have h :=
    wm_induction_conf_eq_min_of_bounded_inputs
      (a := (⟨0, 0⟩ : TV)) (b := (⟨0, 0⟩ : TV)) (c := (⟨0, 0⟩ : TV))
      (ba := (⟨0.7, 0.9⟩ : TV)) (bc := (⟨0.8, 0.9⟩ : TV))
      (by norm_num)
      (by
        simpa [MAX_CONF, Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.MAX_CONF] using
          (show (0.9 : ℝ) ≤ (0.9999 : ℝ) by norm_num))
      (by norm_num)
      (by
        simpa [MAX_CONF, Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.MAX_CONF] using
          (show (0.9 : ℝ) ≤ (0.9999 : ℝ) by norm_num))
  simpa using h

example :
    Mettapedia.PLN.TruthValues.PLNBugAnalysis.inductionConfBuggy 0.9 0.9 = 0.9 / 1.9 := by
  unfold Mettapedia.PLN.TruthValues.PLNBugAnalysis.inductionConfBuggy
    Mettapedia.PLN.TruthValues.PLNBugAnalysis.w2c'
  simp [min_self]
  norm_num

example :
    (0.9 : ℝ) / 1.9 < 0.9 := by
  norm_num

/-! ## Canonical upstream vs PeTTa vs WM-justified

For the core confidence rules, the local picture is now explicit:

* induction / abduction: canonical upstream is more cautious than upstream
  PeTTa / WM weight-min on positive in-range inputs; the historical raw-min
  formula remains documented only as a bug witness;
* deduction: canonical upstream is conservative relative to the edge
  confidences, but is not globally below the PeTTa / WM min-of-five family;
* modus ponens: canonical upstream is more cautious than both PeTTa and
  the WM-justified layer.
-/

/-! ## Strongest Formal Analogues for Mirror-Only Rules

The following rules remain outside the justified layer today, but we can still
say meaningful formal things about them.

### Inversion

There are two distinct formal inversion-strength stories nearby:

* the compiled-rule-catalog / standalone inversion rule keeps `s_BA = s_AB`;
* Bayes inversion computes `s_BA * s_B / s_A` and is used internally by
  induction/abduction derivations.

The mirrored PeTTa/OpenCog rule only carries `b` and `ab`, so it matches the
standalone catalog strength exactly and is under-parameterized for the full
Bayes inversion semantics.
-/

@[simp] theorem truthInversion_strength_matches_catalog (b ab : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInversion b ab).s =
      Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInversionStrength ab := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInversion,
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInversionStrength]

theorem truthInversion_conf_formula (b ab : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInversion b ab).c =
      0.6 * b.c * ab.c := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInversion]
  ring

/-- **Two inversion-strength meanings disagree.** There are two
incompatible readings of inversion-strength floating in the PLN
literature:

* the compiled-rule-catalog form, `s_BA = s_AB` (strength is preserved);
* Bayes inversion, `s_BA = s_AB · s_A / s_B`.

This theorem exhibits a concrete triple where they differ, so any
future unification of the two readings has to pick one. (The mirrored
PeTTa rule implements the catalog form and cannot recover the Bayes
form, which also needs `s_A` and `s_B` as inputs.) -/
theorem truthInversion_catalog_ne_bayes_example :
    ∃ a b ab : TV,
      Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInversionStrength ab ≠
        Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInversionBayesStrength a b ab := by
  refine ⟨⟨0.8, 0.2⟩, ⟨0.4, 0.9⟩, ⟨0.6, 0.8⟩, ?_⟩
  norm_num [Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInversionStrength,
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInversionBayesStrength,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation.bayesInversion]

theorem truthInversion_parametric_conf_le_inputs
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (b ab : TV)
    (hb : b.c ∈ Set.Icc (0 : ℝ) 1)
    (hab : ab.c ∈ Set.Icc (0 : ℝ) 1) :
    α * b.c * ab.c ≤ b.c ∧ α * b.c * ab.c ≤ ab.c := by
  constructor
  · have hmul : α * ab.c ≤ 1 := by
      nlinarith [hα.1, hα.2, hab.1, hab.2]
    have := mul_le_mul_of_nonneg_right hmul hb.1
    nlinarith
  · have hmul : α * b.c ≤ 1 := by
      nlinarith [hα.1, hα.2, hb.1, hb.2]
    have := mul_le_mul_of_nonneg_right hmul hab.1
    nlinarith

example :
    let b : TV := ⟨0.4, 0.9⟩
    let ab : TV := ⟨0.6, 0.8⟩
    let a1 : TV := ⟨0.8, 0.2⟩
    let a2 : TV := ⟨0.6, 0.2⟩
    Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInversionBayesStrength a1 b ab ≠
      Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInversionBayesStrength a2 b ab := by
  dsimp [Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInversionBayesStrength,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation.bayesInversion]
  norm_num

/-!
### Equivalence-to-Implication

We do not yet have a theorem-backed WM semantics identifying the mirrored
thresholded rule with a canonical implication/equivalence operator. What we can
say formally today is that the mirrored rule passes confidence through
unchanged, and its strength has an explicit heuristic threshold branch.
-/

@[simp] theorem truthEquivalenceToImplication_conf_eq (a b ab : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthEquivalenceToImplication a b ab).c = ab.c := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthEquivalenceToImplication]

theorem truthEquivalenceToImplication_threshold_branch
    (a b ab : TV) (h : 0.99 < ab.s * ab.c) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthEquivalenceToImplication a b ab).s = ab.s := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthEquivalenceToImplication, h]

theorem truthEquivalenceToImplication_nonthreshold_strength_eq_formal_analogue
    (a b ab : TV)
    (hthresh : ¬ 0.99 < ab.s * ab.c)
    (ha : 0 < a.s)
    (hab : 0 ≤ ab.s) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthEquivalenceToImplication a b ab).s =
      Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInferenceRules.sim2inh ab.s a.s b.s := by
  have hab_plus : 0 < 1 + ab.s := by
    linarith
  have hsim : ¬(a.s = 0 ∨ ab.s = -1) := by
    intro hbad
    cases hbad with
    | inl h0 => linarith
    | inr hm1 => linarith
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthEquivalenceToImplication,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInferenceRules.sim2inh, hthresh, hsim, ha, hab_plus,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.safeDiv]

/-!
### Transitive Similarity

Here the situation is better. The mirrored strength formula already agrees with
the formal similarity-composition rule from `PLNInferenceRules`, while the
confidence remains only a conservative minimum-style aggregator.
-/

theorem truthTransitiveSimilarity_strength_matches_formal_analogue (a b c ab bc : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity a b c ab bc).s =
      Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInferenceRules.transitiveSimilarity ab.s bc.s a.s b.s c.s := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.transitiveSimilarityStrength,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInferenceRules.transitiveSimilarity]

theorem truthTransitiveSimilarity_conf_le_inputs (a b c ab bc : TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity a b c ab bc).c ≤ ab.c ∧
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity a b c ab bc).c ≤ bc.c := by
  constructor <;>
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity]

/-!
### Evaluation Implication

The mirrored rule is partly deduction-derived on strength, but its confidence is
still a hand-tuned attenuation heuristic. The best nearby formal theory in the
repository is the predictive-implication / temporal lane, not this exact
`0.9 * 0.9 * ...` library formula.
-/

theorem truthEvaluationImplication_some_strength_formula
    (a b c ab ac : TV) (s : ℝ)
    (h :
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.simpleDeductionStrength
        b.s a.s c.s ab.s ac.s = some s) :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthEvaluationImplication a b c ab ac =
      some ⟨s,
        (0.9 * 0.9) *
          min b.c (min a.c (min c.c (min ac.c (0.9 * ab.c))))⟩ := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthEvaluationImplication, h]

theorem truthEvaluationImplication_some_strength_eq_formal_analogue
    (a b c ab ac : TV) (s : ℝ)
    (h :
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.simpleDeductionStrength
        b.s a.s c.s ab.s ac.s = some s) :
    s = Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.simpleDeductionStrengthFormula b.s a.s c.s ab.s ac.s := by
  unfold Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.simpleDeductionStrength at h
  by_cases hcons :
      ¬(Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.conditionalProbabilityConsistency b.s a.s ab.s ∧
        Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.conditionalProbabilityConsistency a.s c.s ac.s)
  · simp [hcons] at h
  · have hcons' :
        Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.conditionalProbabilityConsistency b.s a.s ab.s ∧
        Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.conditionalProbabilityConsistency a.s c.s ac.s := by
      exact not_not.mp hcons
    by_cases ha : 0.99 < a.s
    · simp [hcons', ha, Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.simpleDeductionStrengthFormula] at h ⊢
      simpa using h.symm
    · have hden : 0 < 1 - a.s := by
        linarith
      simp [hcons', ha, hden, Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.simpleDeductionStrengthFormula,
        Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.safeDiv] at h ⊢
      simpa using h.symm

theorem truthEvaluationImplication_some_conf_le_inputs
    (a b c ab ac out : TV)
    (h :
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthEvaluationImplication a b c ab ac = some out)
    (ha : 0 ≤ a.c) (hb : 0 ≤ b.c) (hc : 0 ≤ c.c) (hab : 0 ≤ ab.c) (hac : 0 ≤ ac.c) :
    out.c ≤ b.c ∧ out.c ≤ a.c ∧ out.c ≤ c.c ∧ out.c ≤ ac.c ∧ out.c ≤ ab.c := by
  unfold Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthEvaluationImplication at h
  split at h
  · cases h
  · cases h
    let m : ℝ := min b.c (min a.c (min c.c (min ac.c (0.9 * ab.c))))
    have hm_nonneg : 0 ≤ m := by
      unfold m
      apply le_min hb
      apply le_min ha
      apply le_min hc
      apply le_min hac
      nlinarith
    have hscale : (0.9 * 0.9 : ℝ) ≤ 1 := by norm_num
    have hscaled_le_m : (0.9 * 0.9) * m ≤ m := by
      have : (0.9 * 0.9 : ℝ) * m ≤ 1 * m := by
        exact mul_le_mul_of_nonneg_right hscale hm_nonneg
      simpa using this
    have hm_le_b : m ≤ b.c := by
      unfold m
      exact min_le_left _ _
    have hm_le_a : m ≤ a.c := by
      unfold m
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hm_le_c : m ≤ c.c := by
      unfold m
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hm_le_ac : m ≤ ac.c := by
      unfold m
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hm_le_ab_scaled : m ≤ 0.9 * ab.c := by
      unfold m
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans hscaled_le_m hm_le_b
    · exact le_trans hscaled_le_m hm_le_a
    · exact le_trans hscaled_le_m hm_le_c
    · exact le_trans hscaled_le_m hm_le_ac
    · calc
        (0.9 * 0.9) * m ≤ (0.9 * 0.9) * (0.9 * ab.c) := by
              exact mul_le_mul_of_nonneg_left hm_le_ab_scaled (by norm_num)
        _ ≤ ab.c := by
              nlinarith

/-! ## Constructive WM-backed additions absent from current upstream PeTTa main

These are not mirror comparisons, because the current upstream `main` line
omits them. They are included here so the analysis layer also shows the
concrete WM-backed rules we can already offer today.
-/

theorem predictiveImplication_conf_le_inputs
    (p pq : TV) (hp : p.c ∈ Set.Icc (0 : ℝ) 1) (hpq : pq.c ∈ Set.Icc (0 : ℝ) 1) :
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthPredictiveImplicationConservative p pq).c ≤ p.c ∧
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthPredictiveImplicationConservative p pq).c ≤ pq.c :=
  Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthPredictiveImplication_conf_le_inputs p pq hp hpq

theorem conjunctionConditional_strength_lifts_to_wm
    (a ab : TV) (ha : 0 ≤ a.s) :
    ENNReal.ofReal
        (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionConditionalConservative a ab).s =
      Mettapedia.PLN.RuleFamilies.FirstOrder.PLNConjunction.conjunctionConditional
        (ENNReal.ofReal a.s) (ENNReal.ofReal ab.s) :=
  Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionConditional_strength_lifts_to_wm
    a ab ha

theorem conjunctionConditional_conf_le_inputs
    (a ab : TV) (ha : a.c ∈ Set.Icc (0 : ℝ) 1) (hab : ab.c ∈ Set.Icc (0 : ℝ) 1) :
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionConditionalConservative a ab).c ≤ a.c ∧
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionConditionalConservative a ab).c ≤ ab.c :=
  Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionConditional_conf_le_inputs
    a ab ha hab

theorem conjunctionIndependent_strength_eq_product
    (a b : TV) :
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionIndependentEvidenceStyle a b).s =
      a.s * b.s :=
  Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionIndependent_strength_eq a b

theorem conjunctionIndependent_conf_eq_weight_product
    (a b : TV) :
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionIndependentEvidenceStyle a b).c =
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c
        (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w a.c *
         Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w b.c) :=
  Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionIndependent_conf_eq a b

theorem conjunctionIndependent_strength_le_inputs
    (a b : TV) (ha : a.s ∈ Set.Icc (0 : ℝ) 1) (hb : b.s ∈ Set.Icc (0 : ℝ) 1) :
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionIndependentEvidenceStyle a b).s ≤ a.s ∧
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionIndependentEvidenceStyle a b).s ≤ b.s :=
  Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionIndependent_strength_le_inputs a b ha hb

theorem conjunctionHypergeometric_strength_nonneg
    (n a b : ℕ) :
    0 ≤ (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric n a b).s :=
  Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric_strength_nonneg n a b

theorem conjunctionHypergeometric_strength_le_min_fraction
    (n a b : ℕ) (hn : 0 < n) (ha : a ≤ n) (hb : b ≤ n) :
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric n a b).s ≤
      (min a b : ℝ) / n :=
  Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric_strength_le_min_fraction
    n a b hn ha hb

theorem conjunctionHypergeometric_strength_le_one
    (n a b : ℕ) (hn : 0 < n) (ha : a ≤ n) (hb : b ≤ n) :
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric n a b).s ≤ 1 :=
  Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric_strength_le_one
    n a b hn ha hb

theorem conjunctionHypergeometric_conf_nonneg
    (n a b : ℕ) :
    0 ≤ (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric n a b).c :=
  Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric_conf_nonneg n a b

end Mettapedia.PLN.Comparisons.PeTTa.PeTTaLibPLNFormalAnalysis
