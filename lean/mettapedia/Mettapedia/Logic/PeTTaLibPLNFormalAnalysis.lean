import Mathlib.Tactic
import Mettapedia.Logic.PeTTaLibPLNTruthFunctions
import Mettapedia.Logic.WMPLNJustifiedTruthFunctions
import Mettapedia.Logic.PLNBugAnalysis
import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.PLNInferenceRules

namespace Mettapedia.Logic.PeTTaLibPLNFormalAnalysis

open Mettapedia.Logic.PLN
open Mettapedia.Logic.WMPLNJustifiedTruthFunctions

abbrev TV := Mettapedia.Logic.PeTTaLibPLNTruthFunctions.TV
abbrev MAX_CONF := Mettapedia.Logic.PeTTaLibPLNTruthFunctions.MAX_CONF
abbrev capConf := Mettapedia.Logic.PeTTaLibPLNTruthFunctions.capConf

/-!
# Formal Analysis of PeTTa `lib_pln.metta`

This file compares the transparent PeTTa library mirror against the current
WM-backed justified truth-function layer.

Reading guide:

* exact equality theorems mean the PeTTa library formula already matches the
  justified Lean rule;
* bound theorems mean the PeTTa library formula is conservative / admissible,
  but not yet promoted to a uniquely canonical WM rule;
* canonical-upstream theorems compare the upstream `hyperon/PLN/lib_pln.metta`
  confidence family against both the PeTTa mirror and the WM-justified layer;
* for mirror-only rules, we record the strongest formal analogue currently available
  and prove what we can about its relation to the mirrored library formula.
-/

theorem pettaw2c_le_self (w : ℝ) (hw : 0 ≤ w) :
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c w ≤ w := by
  rw [Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.w2c_eq_div_of_nonneg w hw]
  have hden : 0 < w + 1 := by
    linarith
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg w]

theorem capConf_eq_self_of_mem_core (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ MAX_CONF) :
    capConf c = c := by
  have h1' : c ≤ Mettapedia.Logic.PeTTaLibPLNTruthFunctions.MAX_CONF := by
    simpa [MAX_CONF] using h1
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.capConf, h0, h1']

namespace CanonicalUpstream

/-- Upstream canonical deduction confidence from `/home/zar/claude/hyperon/PLN/lib_pln.metta`. -/
noncomputable def truthDeductionConf (pq qr : TV) : ℝ :=
  pq.s * qr.s * pq.c * qr.c

/-- Upstream canonical induction confidence from `/home/zar/claude/hyperon/PLN/lib_pln.metta`. -/
noncomputable def truthInductionConf (ba bc : TV) : ℝ :=
  Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c (bc.s * bc.c * ba.c)

/-- Upstream canonical abduction confidence from `/home/zar/claude/hyperon/PLN/lib_pln.metta`. -/
noncomputable def truthAbductionConf (ab cb : TV) : ℝ :=
  Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c (ab.s * ab.c * cb.c)

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
    norm_num [MAX_CONF, Mettapedia.Logic.PeTTaLibPLNTruthFunctions.MAX_CONF]
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

theorem canonicalInduction_conf_le_petta_wm
    (a b c ba bc : TV)
    (hbcS : bc.s ∈ Set.Icc (0 : ℝ) 1)
    (hbaC : ba.c ∈ Set.Icc (0 : ℝ) MAX_CONF)
    (hbcC : bc.c ∈ Set.Icc (0 : ℝ) MAX_CONF) :
    CanonicalUpstream.truthInductionConf ba bc ≤
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c := by
  have hcurr :
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c =
        min ba.c bc.c := by
    calc
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c
          = min (capConf ba.c) (capConf bc.c) := by
              simpa [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInduction] using
                (Mettapedia.Logic.NuEvidenceQuantaleBridge.InductionAbductionBridge.inductionAbduction_conf_eq_min_capped
                  ba.c bc.c)
      _ = min ba.c bc.c := by
              rw [capConf_eq_self_of_mem_core ba.c hbaC.1 hbaC.2,
                capConf_eq_self_of_mem_core bc.c hbcC.1 hbcC.2]
  rw [hcurr]
  exact canonicalInduction_conf_le_inputs ba bc hbcS hbaC hbcC

theorem canonicalInduction_conf_le_wm_best
    (a b c ba bc : TV)
    (hbcS : bc.s ∈ Set.Icc (0 : ℝ) 1)
    (hbaC : ba.c ∈ Set.Icc (0 : ℝ) MAX_CONF)
    (hbcC : bc.c ∈ Set.Icc (0 : ℝ) MAX_CONF) :
    CanonicalUpstream.truthInductionConf ba bc ≤
      (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthInduction a b c ba bc).c := by
  simpa [Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthInduction] using
    canonicalInduction_conf_le_petta_wm a b c ba bc hbcS hbaC hbcC

theorem canonicalAbduction_conf_le_inputs
    (ab cb : TV)
    (habS : ab.s ∈ Set.Icc (0 : ℝ) 1)
    (habC : ab.c ∈ Set.Icc (0 : ℝ) MAX_CONF)
    (hcbC : cb.c ∈ Set.Icc (0 : ℝ) MAX_CONF) :
    CanonicalUpstream.truthAbductionConf ab cb ≤ min ab.c cb.c := by
  unfold CanonicalUpstream.truthAbductionConf
  let w : ℝ := ab.s * ab.c * cb.c
  have hMAX : MAX_CONF ≤ 1 := by
    norm_num [MAX_CONF, Mettapedia.Logic.PeTTaLibPLNTruthFunctions.MAX_CONF]
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
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c := by
  have hcurr :
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c =
        min ab.c cb.c := by
    calc
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c
          = min (capConf ab.c) (capConf cb.c) := by
              simpa [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthAbduction] using
                (Mettapedia.Logic.NuEvidenceQuantaleBridge.InductionAbductionBridge.inductionAbduction_conf_eq_min_capped
                  ab.c cb.c)
      _ = min ab.c cb.c := by
              rw [capConf_eq_self_of_mem_core ab.c habC.1 habC.2,
                capConf_eq_self_of_mem_core cb.c hcbC.1 hcbC.2]
  rw [hcurr]
  exact canonicalAbduction_conf_le_inputs ab cb habS habC hcbC

theorem canonicalAbduction_conf_le_wm_best
    (a b c ab cb : TV)
    (habS : ab.s ∈ Set.Icc (0 : ℝ) 1)
    (habC : ab.c ∈ Set.Icc (0 : ℝ) MAX_CONF)
    (hcbC : cb.c ∈ Set.Icc (0 : ℝ) MAX_CONF) :
    CanonicalUpstream.truthAbductionConf ab cb ≤
      (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthAbduction a b c ab cb).c := by
  simpa [Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthAbduction] using
    canonicalAbduction_conf_le_petta_wm a b c ab cb habS habC hcbC

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
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthModusPonens p pq).c := by
  unfold CanonicalUpstream.truthModusPonensConf
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthModusPonens]
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
      (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthModusPonensConservative p pq).c := by
  simpa [Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthModusPonensConservative] using
    canonicalModusPonens_conf_le_petta_wm p pq hpS hpqS hpC hpqC

theorem canonicalSymmetricModusPonens_conf_le_petta_wm
    (a ab : TV)
    (haS : a.s ∈ Set.Icc (0 : ℝ) 1)
    (habS : ab.s ∈ Set.Icc (0 : ℝ) 1)
    (haC : a.c ∈ Set.Icc (0 : ℝ) 1)
    (habC : ab.c ∈ Set.Icc (0 : ℝ) 1) :
    CanonicalUpstream.truthSymmetricModusPonensConf a ab ≤
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens a ab).c := by
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
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens a ab).c =
        min ab.c a.c := by
    have hone : (1.0 : ℝ) = 1 := by norm_num
    simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens,
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
      (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthSymmetricModusPonensConservative a ab).c := by
  simpa [Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthSymmetricModusPonensConservative] using
    canonicalSymmetricModusPonens_conf_le_petta_wm a ab haS habS haC habC

theorem canonicalTransitiveSimilarity_conf_le_mirror
    (a b c ab bc : TV)
    (habS : ab.s ∈ Set.Icc (0 : ℝ) 1)
    (hbcS : bc.s ∈ Set.Icc (0 : ℝ) 1)
    (habC : ab.c ∈ Set.Icc (0 : ℝ) 1)
    (hbcC : bc.c ∈ Set.Icc (0 : ℝ) 1) :
    CanonicalUpstream.truthTransitiveSimilarityConf ab bc ≤
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity a b c ab bc).c := by
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
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity a b c ab bc).c =
        min ab.c bc.c := by
    simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity]
  rw [hmirror]
  exact le_trans hscaled hprod_le_min

/-! ## Exact agreement with the justified layer -/

theorem revision_matches_justified (t1 t2 : TV) :
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthRevision t1 t2 =
      truthRevision t1 t2 := rfl

theorem induction_matches_justified (a b c ba bc : TV) :
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc =
      truthInduction a b c ba bc := rfl

theorem abduction_matches_justified (a b c ab cb : TV) :
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb =
      truthAbduction a b c ab cb := rfl

theorem deduction_matches_conservative (p q r pq qr : TV) :
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthDeduction p q r pq qr =
      truthDeductionConservative p q r pq qr := rfl

theorem modusPonens_matches_conservative (p pq : TV) :
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthModusPonens p pq =
      truthModusPonensConservative p pq := rfl

theorem symmetricModusPonens_matches_conservative (a ab : TV) :
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens a ab =
      truthSymmetricModusPonensConservative a ab := rfl

theorem negation_matches_justified (t : TV) :
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthNegation t =
      truthNegation t := rfl

/-! ## Core consequences -/

theorem induction_conf_eq_min_capped (a b c ba bc : TV) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c =
      min (capConf ba.c) (capConf bc.c) :=
  truthInduction_conf_eq_min_capped a b c ba bc

theorem abduction_conf_eq_min_capped (a b c ab cb : TV) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c =
      min (capConf ab.c) (capConf cb.c) :=
  truthAbduction_conf_eq_min_capped a b c ab cb

theorem induction_conf_le_inputs
    (a b c ba bc : TV) (hba : 0 ≤ ba.c) (hbc : 0 ≤ bc.c) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c ≤
      min ba.c bc.c :=
  truthInduction_conf_le_inputs a b c ba bc hba hbc

theorem abduction_conf_le_inputs
    (a b c ab cb : TV) (hab : 0 ≤ ab.c) (hcb : 0 ≤ cb.c) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c ≤
      min ab.c cb.c :=
  truthAbduction_conf_le_inputs a b c ab cb hab hcb

theorem deduction_conf_le_inputs
    (p q r pq qr : TV)
    (hp : 0 ≤ p.c) (hq : 0 ≤ q.c) (hr : 0 ≤ r.c) (hpq : 0 ≤ pq.c) (hqr : 0 ≤ qr.c) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthDeduction p q r pq qr).c ≤ p.c ∧
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthDeduction p q r pq qr).c ≤ q.c ∧
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthDeduction p q r pq qr).c ≤ r.c ∧
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthDeduction p q r pq qr).c ≤ pq.c ∧
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthDeduction p q r pq qr).c ≤ qr.c :=
  truthDeduction_conf_le_inputs p q r pq qr hp hq hr hpq hqr

theorem modusPonens_conf_le_inputs
    (p pq : TV) (hp : p.c ∈ Set.Icc (0 : ℝ) 1) (hpq : pq.c ∈ Set.Icc (0 : ℝ) 1) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthModusPonens p pq).c ≤ p.c ∧
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthModusPonens p pq).c ≤ pq.c :=
  truthModusPonens_conf_le_inputs p pq hp hpq

theorem symmetricModusPonens_conf_le_inputs (a ab : TV) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens a ab).c ≤ a.c ∧
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens a ab).c ≤ ab.c :=
  truthSymmetricModusPonens_conf_le_inputs a ab

/-! ## Concrete anti-bug witnesses -/

theorem capConf_eq_self_of_mem (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ MAX_CONF) :
    capConf c = c := by
  have h1' : c ≤ Mettapedia.Logic.PeTTaLibPLNTruthFunctions.MAX_CONF := by
    simpa [MAX_CONF] using h1
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.capConf, h0, h1']

theorem induction_conf_eq_min_of_bounded_inputs
    (a b c ba bc : TV)
    (hba0 : 0 ≤ ba.c) (hba1 : ba.c ≤ MAX_CONF)
    (hbc0 : 0 ≤ bc.c) (hbc1 : bc.c ≤ MAX_CONF) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c =
      min ba.c bc.c := by
  rw [induction_conf_eq_min_capped]
  rw [capConf_eq_self_of_mem ba.c hba0 hba1, capConf_eq_self_of_mem bc.c hbc0 hbc1]

example :
    let zero : TV := ⟨0, 0⟩
    let ba : TV := ⟨0.7, 0.9⟩
    let bc : TV := ⟨0.8, 0.9⟩
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInduction zero zero zero ba bc).c = 0.9 := by
  dsimp
  have h :=
    induction_conf_eq_min_of_bounded_inputs
      (a := (⟨0, 0⟩ : TV)) (b := (⟨0, 0⟩ : TV)) (c := (⟨0, 0⟩ : TV))
      (ba := (⟨0.7, 0.9⟩ : TV)) (bc := (⟨0.8, 0.9⟩ : TV))
      (by norm_num)
      (by
        simpa [MAX_CONF, Mettapedia.Logic.PeTTaLibPLNTruthFunctions.MAX_CONF] using
          (show (0.9 : ℝ) ≤ (0.9999 : ℝ) by norm_num))
      (by norm_num)
      (by
        simpa [MAX_CONF, Mettapedia.Logic.PeTTaLibPLNTruthFunctions.MAX_CONF] using
          (show (0.9 : ℝ) ≤ (0.9999 : ℝ) by norm_num))
  simpa using h

example :
    Mettapedia.Logic.PLNBugAnalysis.inductionConfBuggy 0.9 0.9 = 0.9 / 1.9 := by
  unfold Mettapedia.Logic.PLNBugAnalysis.inductionConfBuggy
    Mettapedia.Logic.PLNBugAnalysis.w2c'
  simp [min_self]
  norm_num

example :
    (0.9 : ℝ) / 1.9 < 0.9 := by
  norm_num

/-! ## Canonical upstream vs PeTTa vs WM-justified

For the core confidence rules, the local picture is now explicit:

* induction / abduction: canonical upstream is more cautious than both PeTTa
  and the WM-justified layer;
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
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInversion b ab).s =
      Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthInversionStrength ab := by
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInversion,
    Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthInversionStrength]

theorem truthInversion_conf_formula (b ab : TV) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInversion b ab).c =
      0.6 * b.c * ab.c := by
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInversion]
  ring

theorem truthInversion_catalog_ne_bayes_example :
    ∃ a b ab : TV,
      Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthInversionStrength ab ≠
        Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthInversionBayesStrength a b ab := by
  refine ⟨⟨0.8, 0.2⟩, ⟨0.4, 0.9⟩, ⟨0.6, 0.8⟩, ?_⟩
  norm_num [Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthInversionStrength,
    Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthInversionBayesStrength,
    Mettapedia.Logic.PLN.bayesInversion]

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
    Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthInversionBayesStrength a1 b ab ≠
      Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthInversionBayesStrength a2 b ab := by
  dsimp [Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthInversionBayesStrength,
    Mettapedia.Logic.PLN.bayesInversion]
  norm_num

/-!
### Equivalence-to-Implication

We do not yet have a theorem-backed WM semantics identifying the mirrored
thresholded rule with a canonical implication/equivalence operator. What we can
say formally today is that the mirrored rule passes confidence through
unchanged, and its strength has an explicit heuristic threshold branch.
-/

@[simp] theorem truthEquivalenceToImplication_conf_eq (a b ab : TV) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthEquivalenceToImplication a b ab).c = ab.c := by
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthEquivalenceToImplication]

theorem truthEquivalenceToImplication_threshold_branch
    (a b ab : TV) (h : 0.99 < ab.s * ab.c) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthEquivalenceToImplication a b ab).s = ab.s := by
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthEquivalenceToImplication, h]

theorem truthEquivalenceToImplication_nonthreshold_strength_eq_formal_analogue
    (a b ab : TV)
    (hthresh : ¬ 0.99 < ab.s * ab.c)
    (ha : 0 < a.s)
    (hab : 0 ≤ ab.s) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthEquivalenceToImplication a b ab).s =
      Mettapedia.Logic.PLNInferenceRules.sim2inh ab.s a.s b.s := by
  have hab_plus : 0 < 1 + ab.s := by
    linarith
  have hsim : ¬(a.s = 0 ∨ ab.s = -1) := by
    intro hbad
    cases hbad with
    | inl h0 => linarith
    | inr hm1 => linarith
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthEquivalenceToImplication,
    Mettapedia.Logic.PLNInferenceRules.sim2inh, hthresh, hsim, ha, hab_plus,
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.safeDiv]

/-!
### Transitive Similarity

Here the situation is better. The mirrored strength formula already agrees with
the formal similarity-composition rule from `PLNInferenceRules`, while the
confidence remains only a conservative minimum-style aggregator.
-/

theorem truthTransitiveSimilarity_strength_matches_formal_analogue (a b c ab bc : TV) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity a b c ab bc).s =
      Mettapedia.Logic.PLNInferenceRules.transitiveSimilarity ab.s bc.s a.s b.s c.s := by
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity,
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.transitiveSimilarityStrength,
    Mettapedia.Logic.PLNInferenceRules.transitiveSimilarity]

theorem truthTransitiveSimilarity_conf_le_inputs (a b c ab bc : TV) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity a b c ab bc).c ≤ ab.c ∧
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity a b c ab bc).c ≤ bc.c := by
  constructor <;>
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity]

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
      Mettapedia.Logic.PeTTaLibPLNTruthFunctions.simpleDeductionStrength
        b.s a.s c.s ab.s ac.s = some s) :
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthEvaluationImplication a b c ab ac =
      some ⟨s,
        (0.9 * 0.9) *
          min b.c (min a.c (min c.c (min ac.c (0.9 * ab.c))))⟩ := by
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthEvaluationImplication, h]

theorem truthEvaluationImplication_some_strength_eq_formal_analogue
    (a b c ab ac : TV) (s : ℝ)
    (h :
      Mettapedia.Logic.PeTTaLibPLNTruthFunctions.simpleDeductionStrength
        b.s a.s c.s ab.s ac.s = some s) :
    s = Mettapedia.Logic.PLNDeduction.simpleDeductionStrengthFormula b.s a.s c.s ab.s ac.s := by
  unfold Mettapedia.Logic.PeTTaLibPLNTruthFunctions.simpleDeductionStrength at h
  by_cases hcons :
      ¬(Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency b.s a.s ab.s ∧
        Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency a.s c.s ac.s)
  · simp [hcons] at h
  · have hcons' :
        Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency b.s a.s ab.s ∧
        Mettapedia.Logic.PLNDeduction.conditionalProbabilityConsistency a.s c.s ac.s := by
      exact not_not.mp hcons
    by_cases ha : 0.99 < a.s
    · simp [hcons', ha, Mettapedia.Logic.PLNDeduction.simpleDeductionStrengthFormula] at h ⊢
      simpa using h.symm
    · have hden : 0 < 1 - a.s := by
        linarith
      simp [hcons', ha, hden, Mettapedia.Logic.PLNDeduction.simpleDeductionStrengthFormula,
        Mettapedia.Logic.PeTTaLibPLNTruthFunctions.safeDiv] at h ⊢
      simpa using h.symm

theorem truthEvaluationImplication_some_conf_le_inputs
    (a b c ab ac out : TV)
    (h :
      Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthEvaluationImplication a b c ab ac = some out)
    (ha : 0 ≤ a.c) (hb : 0 ≤ b.c) (hc : 0 ≤ c.c) (hab : 0 ≤ ab.c) (hac : 0 ≤ ac.c) :
    out.c ≤ b.c ∧ out.c ≤ a.c ∧ out.c ≤ c.c ∧ out.c ≤ ac.c ∧ out.c ≤ ab.c := by
  unfold Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthEvaluationImplication at h
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

/-! ## Constructive WM-backed additions absent from current PeTTa `lib_pln.metta`

These are not mirror comparisons, because the current PeTTa library does not
ship them. They are included here so the analysis layer also shows the concrete
WM-backed rules we can already offer today.
-/

theorem predictiveImplication_conf_le_inputs
    (p pq : TV) (hp : p.c ∈ Set.Icc (0 : ℝ) 1) (hpq : pq.c ∈ Set.Icc (0 : ℝ) 1) :
    (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthPredictiveImplicationConservative p pq).c ≤ p.c ∧
    (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthPredictiveImplicationConservative p pq).c ≤ pq.c :=
  Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthPredictiveImplication_conf_le_inputs p pq hp hpq

theorem conjunctionConditional_strength_lifts_to_wm
    (a ab : TV) (ha : 0 ≤ a.s) :
    ENNReal.ofReal
        (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionConditionalConservative a ab).s =
      Mettapedia.Logic.PLNConjunction.conjunctionConditional
        (ENNReal.ofReal a.s) (ENNReal.ofReal ab.s) :=
  Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionConditional_strength_lifts_to_wm
    a ab ha

theorem conjunctionConditional_conf_le_inputs
    (a ab : TV) (ha : a.c ∈ Set.Icc (0 : ℝ) 1) (hab : ab.c ∈ Set.Icc (0 : ℝ) 1) :
    (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionConditionalConservative a ab).c ≤ a.c ∧
    (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionConditionalConservative a ab).c ≤ ab.c :=
  Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionConditional_conf_le_inputs
    a ab ha hab

theorem conjunctionIndependent_strength_eq_product
    (a b : TV) :
    (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionIndependentEvidenceStyle a b).s =
      a.s * b.s :=
  Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionIndependent_strength_eq a b

theorem conjunctionIndependent_conf_eq_weight_product
    (a b : TV) :
    (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionIndependentEvidenceStyle a b).c =
      Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c
        (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w a.c *
         Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w b.c) :=
  Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionIndependent_conf_eq a b

theorem conjunctionIndependent_strength_le_inputs
    (a b : TV) (ha : a.s ∈ Set.Icc (0 : ℝ) 1) (hb : b.s ∈ Set.Icc (0 : ℝ) 1) :
    (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionIndependentEvidenceStyle a b).s ≤ a.s ∧
    (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionIndependentEvidenceStyle a b).s ≤ b.s :=
  Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionIndependent_strength_le_inputs a b ha hb

theorem conjunctionHypergeometric_strength_nonneg
    (n a b : ℕ) :
    0 ≤ (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric n a b).s :=
  Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric_strength_nonneg n a b

theorem conjunctionHypergeometric_strength_le_min_fraction
    (n a b : ℕ) (hn : 0 < n) (ha : a ≤ n) (hb : b ≤ n) :
    (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric n a b).s ≤
      (min a b : ℝ) / n :=
  Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric_strength_le_min_fraction
    n a b hn ha hb

theorem conjunctionHypergeometric_strength_le_one
    (n a b : ℕ) (hn : 0 < n) (ha : a ≤ n) (hb : b ≤ n) :
    (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric n a b).s ≤ 1 :=
  Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric_strength_le_one
    n a b hn ha hb

theorem conjunctionHypergeometric_conf_nonneg
    (n a b : ℕ) :
    0 ≤ (Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric n a b).c :=
  Mettapedia.Logic.WMPLNJustifiedTruthFunctions.truthConjunctionHypergeometric_conf_nonneg n a b

end Mettapedia.Logic.PeTTaLibPLNFormalAnalysis
