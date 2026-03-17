import Mettapedia.Logic.PLNMettaTruthFunctions
import Mettapedia.Logic.NARSMettaTruthFunctions
import Mettapedia.Logic.NARSEvidenceBridge
import Mettapedia.Logic.NARSPLNGaloisConnection

/-!
# PLN↔NARS Rule Correspondence

This module consolidates the mathematically central bridge layer between PLN and
NARS into one theorem-oriented package:

- confidence/weight transform laws
- rule-shape correspondences (deduction/induction/abduction/source/sink)
- revision/evidence aggregation coherence
- informativeness adjunction (`L ⊣ U`) for finite evidence

The goal is a stable import surface for rule-by-rule comparison work.
-/

namespace Mettapedia.Logic.PLNNARSRuleCorrespondence

open scoped ENNReal

abbrev PLNTV := Mettapedia.Logic.PLNMettaTruthFunctions.TV
abbrev NARSTV := Mettapedia.Logic.NARSMettaTruthFunctions.TV

/-! ## TV Views -/

/-- View a NARS truth value as a PLN-style `(strength, confidence)` pair. -/
def narsToPLNTV (t : NARSTV) : PLNTV := ⟨t.f, t.c⟩

/-- View a PLN truth value as a NARS-style `(frequency, confidence)` pair. -/
def plnToNARSTV (t : PLNTV) : NARSTV := ⟨t.s, t.c⟩

@[simp] theorem narsToPLNTV_roundTrip (t : NARSTV) :
    plnToNARSTV (narsToPLNTV t) = t := by
  cases t
  rfl

@[simp] theorem plnToNARSTV_roundTrip (t : PLNTV) :
    narsToPLNTV (plnToNARSTV t) = t := by
  cases t
  rfl

/-! ## Bundle 1: Weight Transform Laws -/

structure WeightTransformBundle : Prop where
  nars_c2w_eq :
    ∀ c : ℝ, c < 1 →
      Mettapedia.Logic.NARSMettaTruthFunctions.c2w c = c / (1 - c)
  nars_w2c_eq :
    ∀ w : ℝ,
      Mettapedia.Logic.NARSMettaTruthFunctions.w2c w = w / (w + 1)
  w2c_c2w_id :
    ∀ c : ℝ, 0 ≤ c → c < 1 →
      Mettapedia.Logic.NARSMettaTruthFunctions.w2c
        (Mettapedia.Logic.NARSMettaTruthFunctions.c2w c) = c
  c2w_w2c_id :
    ∀ w : ℝ, 0 ≤ w →
      Mettapedia.Logic.NARSMettaTruthFunctions.c2w
        (Mettapedia.Logic.NARSMettaTruthFunctions.w2c w) = w

theorem weightTransformBundle : WeightTransformBundle := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    simpa using Mettapedia.Logic.NARSEvidenceBridge.nars_c2w_eq c hc
  · intro w
    simpa using Mettapedia.Logic.NARSEvidenceBridge.nars_w2c_eq w
  · intro c hc0 hc1
    simpa using Mettapedia.Logic.NARSEvidenceBridge.w2c_c2w_id c hc0 hc1
  · intro w hw
    simpa using Mettapedia.Logic.NARSEvidenceBridge.c2w_w2c_id w hw

/-! ## Bundle 2: Rule Correspondence Laws -/

structure RuleCorrespondenceBundle : Prop where
  pln_sourceRule_alias :
    Mettapedia.Logic.PLNMettaTruthFunctions.truthSourceRule =
      Mettapedia.Logic.PLNMettaTruthFunctions.truthInduction
  pln_sinkRule_alias :
    Mettapedia.Logic.PLNMettaTruthFunctions.truthSinkRule =
      Mettapedia.Logic.PLNMettaTruthFunctions.truthAbduction
  nars_sourceRule_alias :
    Mettapedia.Logic.NARSMettaTruthFunctions.truthSourceRule =
      Mettapedia.Logic.NARSMettaTruthFunctions.truthInduction
  nars_sinkRule_alias :
    Mettapedia.Logic.NARSMettaTruthFunctions.truthSinkRule =
      Mettapedia.Logic.NARSMettaTruthFunctions.truthAbduction
  nars_induction_is_abduction_swapped :
    ∀ t1 t2 : NARSTV,
      Mettapedia.Logic.NARSMettaTruthFunctions.truthInduction t1 t2 =
        Mettapedia.Logic.NARSMettaTruthFunctions.truthAbduction t2 t1
  nars_abduction_freq_is_second :
    ∀ t1 t2 : NARSTV,
      (Mettapedia.Logic.NARSMettaTruthFunctions.truthAbduction t1 t2).f = t2.f
  nars_induction_freq_is_first :
    ∀ t1 t2 : NARSTV,
      (Mettapedia.Logic.NARSMettaTruthFunctions.truthInduction t1 t2).f = t1.f
  pln_induction_strength_formula :
    ∀ a b c ba bc : PLNTV,
      (Mettapedia.Logic.PLNMettaTruthFunctions.truthInduction a b c ba bc).s =
        Mettapedia.Logic.PLN.plnInductionStrength ba.s bc.s a.s b.s c.s
  pln_abduction_strength_formula :
    ∀ a b c ab cb : PLNTV,
      (Mettapedia.Logic.PLNMettaTruthFunctions.truthAbduction a b c ab cb).s =
        Mettapedia.Logic.PLN.plnAbductionStrength ab.s cb.s a.s b.s c.s

theorem ruleCorrespondenceBundle : RuleCorrespondenceBundle := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro t1 t2
    simpa using
      Mettapedia.Logic.NARSEvidenceBridge.induction_is_abduction_swapped t1 t2
  · intro t1 t2
    simpa using Mettapedia.Logic.NARSEvidenceBridge.abduction_freq_is_f2 t1 t2
  · intro t1 t2
    simpa using Mettapedia.Logic.NARSEvidenceBridge.induction_freq_is_f1 t1 t2
  · intro a b c ba bc
    simpa using
      Mettapedia.Logic.PLNMettaTruthFunctions.truthInduction_s_eq a b c ba bc
  · intro a b c ab cb
    simpa using
      Mettapedia.Logic.PLNMettaTruthFunctions.truthAbduction_s_eq a b c ab cb

/-! ## Bundle 3: Revision/BinaryEvidence Coherence -/

structure RevisionCoherenceBundle : Prop where
  nars_revision_conf_formula :
    ∀ t1 t2 : NARSTV,
      Mettapedia.Logic.NARSMettaTruthFunctions.w2c
          (Mettapedia.Logic.NARSMettaTruthFunctions.c2w t1.c +
            Mettapedia.Logic.NARSMettaTruthFunctions.c2w t2.c) =
        (Mettapedia.Logic.NARSMettaTruthFunctions.c2w t1.c +
          Mettapedia.Logic.NARSMettaTruthFunctions.c2w t2.c) /
          (Mettapedia.Logic.NARSMettaTruthFunctions.c2w t1.c +
            Mettapedia.Logic.NARSMettaTruthFunctions.c2w t2.c + 1)
  nars_revision_freq_formula :
    ∀ t1 t2 : NARSTV,
      0 < Mettapedia.Logic.NARSMettaTruthFunctions.c2w t1.c +
            Mettapedia.Logic.NARSMettaTruthFunctions.c2w t2.c →
        (Mettapedia.Logic.NARSMettaTruthFunctions.c2w t1.c * t1.f +
          Mettapedia.Logic.NARSMettaTruthFunctions.c2w t2.c * t2.f) /
            (Mettapedia.Logic.NARSMettaTruthFunctions.c2w t1.c +
              Mettapedia.Logic.NARSMettaTruthFunctions.c2w t2.c) =
        t1.f * (Mettapedia.Logic.NARSMettaTruthFunctions.c2w t1.c /
          (Mettapedia.Logic.NARSMettaTruthFunctions.c2w t1.c +
            Mettapedia.Logic.NARSMettaTruthFunctions.c2w t2.c)) +
        t2.f * (Mettapedia.Logic.NARSMettaTruthFunctions.c2w t2.c /
          (Mettapedia.Logic.NARSMettaTruthFunctions.c2w t1.c +
            Mettapedia.Logic.NARSMettaTruthFunctions.c2w t2.c))
  nars_revision_is_evidence_aggregation :
    ∀ t1 t2 : NARSTV,
      let w1 := Mettapedia.Logic.NARSMettaTruthFunctions.c2w t1.c
      let w2 := Mettapedia.Logic.NARSMettaTruthFunctions.c2w t2.c
      (w1 * t1.f + w2 * t2.f) / (w1 + w2) =
        (t1.f * w1 + t2.f * w2) / (w1 + w2) ∧
      Mettapedia.Logic.NARSMettaTruthFunctions.w2c (w1 + w2) =
        (w1 + w2) / (w1 + w2 + 1)

theorem revisionCoherenceBundle : RevisionCoherenceBundle := by
  refine ⟨?_, ?_, ?_⟩
  · intro t1 t2
    simpa using Mettapedia.Logic.NARSEvidenceBridge.nars_revision_conf_formula t1 t2
  · intro t1 t2 hw
    simpa using Mettapedia.Logic.NARSEvidenceBridge.nars_revision_freq_formula t1 t2 hw
  · intro t1 t2
    simpa using Mettapedia.Logic.NARSEvidenceBridge.nars_revision_is_evidence_aggregation t1 t2

/-! ## Bundle 4: Informativeness Adjunction -/

structure InformativenessAdjunctionBundle : Prop where
  U_L_conf_round_trip :
    ∀ n : Mettapedia.Logic.NARSPLNGaloisConnection.NARSTruthValue,
      (Mettapedia.Logic.NARSPLNGaloisConnection.U
        (Mettapedia.Logic.NARSPLNGaloisConnection.L n)).c = n.c
  U_L_freq_round_trip :
    ∀ n : Mettapedia.Logic.NARSPLNGaloisConnection.NARSTruthValue, n.c > 0 →
      (Mettapedia.Logic.NARSPLNGaloisConnection.U
        (Mettapedia.Logic.NARSPLNGaloisConnection.L n)).f = n.f
  galoisConnection_L_U_finite :
    ∀ (b : Mettapedia.Logic.NARSPLNGaloisConnection.PLNBelief)
      (_hb : b.evidence.total ≠ ⊤)
      (n : Mettapedia.Logic.NARSPLNGaloisConnection.NARSTruthValue),
      (Mettapedia.Logic.NARSPLNGaloisConnection.L n).totalEvidence ≤ b.totalEvidence ↔
        n.weight ≤ (Mettapedia.Logic.NARSPLNGaloisConnection.U b).weight
  L_le_iff_le_U :
    ∀ (b : Mettapedia.Logic.NARSPLNGaloisConnection.PLNBelief)
      (_hb : b.evidence.total ≠ ⊤)
      (n : Mettapedia.Logic.NARSPLNGaloisConnection.NARSTruthValue),
      Mettapedia.Logic.NARSPLNGaloisConnection.L n ≤ b ↔
        n ≤ Mettapedia.Logic.NARSPLNGaloisConnection.U b

theorem informativenessAdjunctionBundle : InformativenessAdjunctionBundle := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    simpa using Mettapedia.Logic.NARSPLNGaloisConnection.U_L_conf_round_trip n
  · intro n hc
    simpa using Mettapedia.Logic.NARSPLNGaloisConnection.U_L_freq_round_trip n hc
  · intro b hb n
    simpa using Mettapedia.Logic.NARSPLNGaloisConnection.galoisConnection_L_U_finite b hb n
  · intro b hb n
    simpa using Mettapedia.Logic.NARSPLNGaloisConnection.L_le_iff_le_U b hb n

/-! ## Master Package -/

structure PLNNARSRuleBridgeBundle : Prop where
  weight : WeightTransformBundle
  rules : RuleCorrespondenceBundle
  revision : RevisionCoherenceBundle
  adjunction : InformativenessAdjunctionBundle

theorem plnNarsRuleBridgeBundle : PLNNARSRuleBridgeBundle := by
  refine ⟨weightTransformBundle, ruleCorrespondenceBundle,
    revisionCoherenceBundle, informativenessAdjunctionBundle⟩

end Mettapedia.Logic.PLNNARSRuleCorrespondence
