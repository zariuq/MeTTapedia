import Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions
import Mettapedia.NARS.TruthFunctions
import Mettapedia.NARS.Bridges.PLN.EvidenceTranslation
import Mettapedia.NARS.Bridges.PLN.InformationAdjunction

/-!
# PLN↔NARS Rule Correspondence

This module consolidates the mathematically central bridge layer between PLN and
NARS into one theorem-oriented package:

- confidence/weight transform laws
- rule-shape correspondences (deduction/induction/abduction/source/sink)
- revision/evidence aggregation coherence
- informativeness adjunction (`L ⊣ U`) for finite evidence

The goal is a stable import interface for rule-by-rule comparison work.
-/

namespace Mettapedia.NARS.Bridges.PLN.RuleCorrespondence

open scoped ENNReal

abbrev PLNTV := Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.TV
abbrev NARSTV := Mettapedia.NARS.TruthFunctions.TV

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
      Mettapedia.NARS.TruthFunctions.c2w c = c / (1 - c)
  nars_w2c_eq :
    ∀ w : ℝ,
      Mettapedia.NARS.TruthFunctions.w2c w = w / (w + 1)
  w2c_c2w_id :
    ∀ c : ℝ, 0 ≤ c → c < 1 →
      Mettapedia.NARS.TruthFunctions.w2c
        (Mettapedia.NARS.TruthFunctions.c2w c) = c
  c2w_w2c_id :
    ∀ w : ℝ, 0 ≤ w →
      Mettapedia.NARS.TruthFunctions.c2w
        (Mettapedia.NARS.TruthFunctions.w2c w) = w

theorem weightTransformBundle : WeightTransformBundle := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    simpa using Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.nars_c2w_eq c hc
  · intro w
    simpa using Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.nars_w2c_eq w
  · intro c hc0 hc1
    simpa using Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.w2c_c2w_id c hc0 hc1
  · intro w hw
    simpa using Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.c2w_w2c_id w hw

/-! ## Bundle 2: Rule Correspondence Laws -/

structure RuleCorrespondenceBundle : Prop where
  pln_sourceRule_alias :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthSourceRule =
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction
  pln_sinkRule_alias :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthSinkRule =
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction
  nars_sourceRule_alias :
    Mettapedia.NARS.TruthFunctions.truthSourceRule =
      Mettapedia.NARS.TruthFunctions.truthInduction
  nars_sinkRule_alias :
    Mettapedia.NARS.TruthFunctions.truthSinkRule =
      Mettapedia.NARS.TruthFunctions.truthAbduction
  nars_induction_is_abduction_swapped :
    ∀ t1 t2 : NARSTV,
      Mettapedia.NARS.TruthFunctions.truthInduction t1 t2 =
        Mettapedia.NARS.TruthFunctions.truthAbduction t2 t1
  nars_abduction_freq_is_second :
    ∀ t1 t2 : NARSTV,
      (Mettapedia.NARS.TruthFunctions.truthAbduction t1 t2).f = t2.f
  nars_induction_freq_is_first :
    ∀ t1 t2 : NARSTV,
      (Mettapedia.NARS.TruthFunctions.truthInduction t1 t2).f = t1.f
  pln_induction_strength_formula :
    ∀ a b c ba bc : PLNTV,
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).s =
        Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation.plnInductionStrength ba.s bc.s a.s b.s c.s
  pln_abduction_strength_formula :
    ∀ a b c ab cb : PLNTV,
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).s =
        Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation.plnAbductionStrength ab.s cb.s a.s b.s c.s

theorem ruleCorrespondenceBundle : RuleCorrespondenceBundle := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro t1 t2
    simpa using
      Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.induction_is_abduction_swapped t1 t2
  · intro t1 t2
    simpa using Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.abduction_freq_is_f2 t1 t2
  · intro t1 t2
    simpa using Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.induction_freq_is_f1 t1 t2
  · intro a b c ba bc
    simpa using
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction_s_eq a b c ba bc
  · intro a b c ab cb
    simpa using
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction_s_eq a b c ab cb

/-! ## Bundle 3: Revision/BinaryEvidence Coherence -/

structure RevisionCoherenceBundle : Prop where
  nars_revision_conf_formula :
    ∀ t1 t2 : NARSTV,
      Mettapedia.NARS.TruthFunctions.w2c
          (Mettapedia.NARS.TruthFunctions.c2w t1.c +
            Mettapedia.NARS.TruthFunctions.c2w t2.c) =
        (Mettapedia.NARS.TruthFunctions.c2w t1.c +
          Mettapedia.NARS.TruthFunctions.c2w t2.c) /
          (Mettapedia.NARS.TruthFunctions.c2w t1.c +
            Mettapedia.NARS.TruthFunctions.c2w t2.c + 1)
  nars_revision_freq_formula :
    ∀ t1 t2 : NARSTV,
      0 < Mettapedia.NARS.TruthFunctions.c2w t1.c +
            Mettapedia.NARS.TruthFunctions.c2w t2.c →
        (Mettapedia.NARS.TruthFunctions.c2w t1.c * t1.f +
          Mettapedia.NARS.TruthFunctions.c2w t2.c * t2.f) /
            (Mettapedia.NARS.TruthFunctions.c2w t1.c +
              Mettapedia.NARS.TruthFunctions.c2w t2.c) =
        t1.f * (Mettapedia.NARS.TruthFunctions.c2w t1.c /
          (Mettapedia.NARS.TruthFunctions.c2w t1.c +
            Mettapedia.NARS.TruthFunctions.c2w t2.c)) +
        t2.f * (Mettapedia.NARS.TruthFunctions.c2w t2.c /
          (Mettapedia.NARS.TruthFunctions.c2w t1.c +
            Mettapedia.NARS.TruthFunctions.c2w t2.c))
  nars_revision_is_evidence_aggregation :
    ∀ t1 t2 : NARSTV,
      let w1 := Mettapedia.NARS.TruthFunctions.c2w t1.c
      let w2 := Mettapedia.NARS.TruthFunctions.c2w t2.c
      (w1 * t1.f + w2 * t2.f) / (w1 + w2) =
        (t1.f * w1 + t2.f * w2) / (w1 + w2) ∧
      Mettapedia.NARS.TruthFunctions.w2c (w1 + w2) =
        (w1 + w2) / (w1 + w2 + 1)

theorem revisionCoherenceBundle : RevisionCoherenceBundle := by
  refine ⟨?_, ?_, ?_⟩
  · intro t1 t2
    simpa using Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.nars_revision_conf_formula t1 t2
  · intro t1 t2 hw
    simpa using Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.nars_revision_freq_formula t1 t2 hw
  · intro t1 t2
    simpa using Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.nars_revision_is_evidence_aggregation t1 t2

/-! ## Bundle 4: Informativeness Adjunction -/

structure InformativenessAdjunctionBundle : Prop where
  U_L_conf_round_trip :
    ∀ n : Mettapedia.NARS.Bridges.PLN.InformationAdjunction.NARSTruthValue,
      (Mettapedia.NARS.Bridges.PLN.InformationAdjunction.U
        (Mettapedia.NARS.Bridges.PLN.InformationAdjunction.L n)).c = n.c
  U_L_freq_round_trip :
    ∀ n : Mettapedia.NARS.Bridges.PLN.InformationAdjunction.NARSTruthValue, n.c > 0 →
      (Mettapedia.NARS.Bridges.PLN.InformationAdjunction.U
        (Mettapedia.NARS.Bridges.PLN.InformationAdjunction.L n)).f = n.f
  galoisConnection_L_U_finite :
    ∀ (b : Mettapedia.NARS.Bridges.PLN.InformationAdjunction.PLNBelief)
      (_hb : b.evidence.total ≠ ⊤)
      (n : Mettapedia.NARS.Bridges.PLN.InformationAdjunction.NARSTruthValue),
      (Mettapedia.NARS.Bridges.PLN.InformationAdjunction.L n).totalEvidence ≤ b.totalEvidence ↔
        n.weight ≤ (Mettapedia.NARS.Bridges.PLN.InformationAdjunction.U b).weight
  L_le_iff_le_U :
    ∀ (b : Mettapedia.NARS.Bridges.PLN.InformationAdjunction.PLNBelief)
      (_hb : b.evidence.total ≠ ⊤)
      (n : Mettapedia.NARS.Bridges.PLN.InformationAdjunction.NARSTruthValue),
      Mettapedia.NARS.Bridges.PLN.InformationAdjunction.L n ≤ b ↔
        n ≤ Mettapedia.NARS.Bridges.PLN.InformationAdjunction.U b

theorem informativenessAdjunctionBundle : InformativenessAdjunctionBundle := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    simpa using Mettapedia.NARS.Bridges.PLN.InformationAdjunction.U_L_conf_round_trip n
  · intro n hc
    simpa using Mettapedia.NARS.Bridges.PLN.InformationAdjunction.U_L_freq_round_trip n hc
  · intro b hb n
    simpa using Mettapedia.NARS.Bridges.PLN.InformationAdjunction.galoisConnection_L_U_finite b hb n
  · intro b hb n
    simpa using Mettapedia.NARS.Bridges.PLN.InformationAdjunction.L_le_iff_le_U b hb n

/-! ## Master Package -/

structure PLNNARSRuleBridgeBundle : Prop where
  weight : WeightTransformBundle
  rules : RuleCorrespondenceBundle
  revision : RevisionCoherenceBundle
  adjunction : InformativenessAdjunctionBundle

theorem plnNarsRuleBridgeBundle : PLNNARSRuleBridgeBundle := by
  refine ⟨weightTransformBundle, ruleCorrespondenceBundle,
    revisionCoherenceBundle, informativenessAdjunctionBundle⟩

end Mettapedia.NARS.Bridges.PLN.RuleCorrespondence
