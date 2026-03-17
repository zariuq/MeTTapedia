import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWMOSLFBridge
import Mettapedia.Logic.PLNBugAnalysis

/-!
# Error-Magnification Grounding (WM ↔ OSLF ↔ BinaryEvidence)

Semantic grounding for the Chapter-8 error-magnification theme, without chapter
labels in module names.

This module connects three layers:

1. BinaryEvidence-level confidence view (`BinaryEvidence.toConfidence`) on WM queries.
2. WM rewrite/query-equivalence transport for confidence thresholds.
3. OSLF atom semantics for confidence-threshold judgments.

It also internalizes the double-damping bug gap as a threshold-separation theorem.
-/

namespace Mettapedia.Logic.PLNErrorMagnificationGrounding

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNBugAnalysis
open Mettapedia.Logic.PLNWMOSLFBridge
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped ENNReal

section Untyped

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- Confidence view for a WM query, derived from evidence totals. -/
noncomputable def queryConfidence (κ : ℝ≥0∞) (W : State) (q : Query) : ℝ :=
  (BinaryWorldModel.queryConfidence (State := State) (Query := Query) κ W q).toReal

/-- Query equivalence transports the confidence view. -/
theorem WMQueryEq.to_queryConfidence
    {q₁ q₂ : Query}
    (hEq : WMQueryEq (State := State) (Query := Query) q₁ q₂)
    (κ : ℝ≥0∞) (W : State) :
    queryConfidence (State := State) (Query := Query) κ W q₁ =
      queryConfidence (State := State) (Query := Query) κ W q₂ := by
  simpa [queryConfidence] using
    congrArg ENNReal.toReal
      (PLNWorldModel.WMQueryEq.to_queryConfidence
        (State := State) (Query := Query) hEq κ W)

/-- Query equivalence transports confidence-threshold judgments. -/
theorem WMQueryEq.to_queryConfidence_threshold
    {q₁ q₂ : Query}
    (hEq : WMQueryEq (State := State) (Query := Query) q₁ q₂)
    (κ : ℝ≥0∞) (W : State) (tau : ℝ)
    (hTau : tau ≤ queryConfidence (State := State) (Query := Query) κ W q₁) :
    tau ≤ queryConfidence (State := State) (Query := Query) κ W q₂ := by
  simpa [WMQueryEq.to_queryConfidence (State := State) (Query := Query) hEq κ W] using hTau

/-- Atom semantics: an atom holds when its encoded WM-query confidence exceeds `tau`. -/
noncomputable def thresholdAtomSemOfWMQConfidence
    (κ : ℝ≥0∞) (W : State) (tau : ℝ)
    (queryOfAtom : String → Pattern → Query) : AtomSem :=
  fun a p => tau ≤ queryConfidence (State := State) (Query := Query) κ W (queryOfAtom a p)

/-- Rewrite soundness transferred to confidence-view equality at the atom level. -/
theorem wmRewriteRule_confidence_atom_eq_derive
    (r : WMRewriteRule State Query)
    (hSide : r.side) (κ : ℝ≥0∞) (W : State)
    (queryOfAtom : String → Pattern → Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion) :
    queryConfidence (State := State) (Query := Query) κ W (queryOfAtom a p) =
      (BinaryEvidence.toConfidence κ (r.derive W)).toReal := by
  rw [hEnc]
  have hEq :
      BinaryWorldModel.queryConfidence (State := State) (Query := Query) κ W r.conclusion =
        BinaryEvidence.toConfidence κ (r.derive W) := by
    simp [BinaryWorldModel.queryConfidence, r.sound hSide W]
  exact congrArg ENNReal.toReal hEq

/-- Confidence-threshold consequence for an atom from a WM rewrite rule. -/
theorem wmRewriteRule_threshold_atom_confidence
    (R : Pattern → Pattern → Prop)
    (r : WMRewriteRule State Query)
    (hSide : r.side) (κ : ℝ≥0∞) (W : State)
    (tau : ℝ)
    (queryOfAtom : String → Pattern → Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ (BinaryEvidence.toConfidence κ (r.derive W)).toReal) :
    sem R (thresholdAtomSemOfWMQConfidence (State := State) (Query := Query)
      κ W tau queryOfAtom) (.atom a) p := by
  show tau ≤ queryConfidence (State := State) (Query := Query) κ W (queryOfAtom a p)
  simpa [wmRewriteRule_confidence_atom_eq_derive (State := State) (Query := Query)
    r hSide κ W queryOfAtom a p hEnc] using hTau

/-- Buggy induction-confidence estimator from two WM queries. -/
noncomputable def inductionConfBuggyOfQueries
    (κ : ℝ≥0∞) (W : State) (q₁ q₂ : Query) : ℝ :=
  inductionConfBuggy
    (queryConfidence (State := State) (Query := Query) κ W q₁)
    (queryConfidence (State := State) (Query := Query) κ W q₂)

/-- Correct induction-confidence estimator from two WM queries. -/
noncomputable def inductionConfCorrectOfQueries
    (κ : ℝ≥0∞) (W : State) (q₁ q₂ : Query) : ℝ :=
  inductionConfCorrect
    (queryConfidence (State := State) (Query := Query) κ W q₁)
    (queryConfidence (State := State) (Query := Query) κ W q₂)

/-- Double-damping underestimation lifted to WM-query confidence channels. -/
theorem double_damping_underestimates_of_queries
    (κ : ℝ≥0∞) (W : State) (q₁ q₂ : Query)
    (hc1 : 0 < queryConfidence (State := State) (Query := Query) κ W q₁)
    (hc2 : 0 < queryConfidence (State := State) (Query := Query) κ W q₂)
    (hc1_lt1 : queryConfidence (State := State) (Query := Query) κ W q₁ < 1)
    (hc2_lt1 : queryConfidence (State := State) (Query := Query) κ W q₂ < 1)
    (h12 : queryConfidence (State := State) (Query := Query) κ W q₂
      ≤ queryConfidence (State := State) (Query := Query) κ W q₁) :
    inductionConfBuggyOfQueries (State := State) (Query := Query) κ W q₁ q₂
      <
    inductionConfCorrectOfQueries (State := State) (Query := Query) κ W q₁ q₂ := by
  unfold inductionConfBuggyOfQueries inductionConfCorrectOfQueries
  exact double_damping_underestimates
    (c1 := queryConfidence (State := State) (Query := Query) κ W q₁)
    (c2 := queryConfidence (State := State) (Query := Query) κ W q₂)
    hc1 hc2 hc1_lt1 hc2_lt1 h12

/-- Threshold-separation corollary: there is a confidence threshold region where
buggy inference fails while corrected inference succeeds. -/
theorem threshold_gap_of_double_damping_of_queries
    (κ : ℝ≥0∞) (W : State) (q₁ q₂ : Query) (tau : ℝ)
    (hbug : inductionConfBuggyOfQueries (State := State) (Query := Query) κ W q₁ q₂ < tau)
    (hcorrect : tau ≤ inductionConfCorrectOfQueries (State := State) (Query := Query) κ W q₁ q₂) :
    ¬ tau ≤ inductionConfBuggyOfQueries (State := State) (Query := Query) κ W q₁ q₂
      ∧
    tau ≤ inductionConfCorrectOfQueries (State := State) (Query := Query) κ W q₁ q₂ := by
  exact ⟨not_le.mpr hbug, hcorrect⟩

end Untyped

section Typed

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-- Confidence view for a typed WM query. -/
noncomputable def queryConfidenceSigma
    (κ : ℝ≥0∞) (W : State) (q : Sigma Query) : ℝ :=
  (WorldModelSigma.queryConfidence (State := State) (Srt := Srt) (Query := Query) κ W q).toReal

/-- Typed query equivalence transports confidence view. -/
theorem WMQueryEqSigma.to_queryConfidence
    {q₁ q₂ : Sigma Query}
    (hEq : WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (κ : ℝ≥0∞) (W : State) :
    queryConfidenceSigma (State := State) (Srt := Srt) (Query := Query) κ W q₁ =
      queryConfidenceSigma (State := State) (Srt := Srt) (Query := Query) κ W q₂ := by
  simpa [queryConfidenceSigma] using
    congrArg ENNReal.toReal
      (PLNWorldModel.WorldModelSigma.WMQueryEqSigma.to_queryConfidence
        (State := State) (Srt := Srt) (Query := Query) hEq κ W)

/-- Typed query equivalence transports confidence-threshold judgments. -/
theorem WMQueryEqSigma.to_queryConfidence_threshold
    {q₁ q₂ : Sigma Query}
    (hEq : WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (κ : ℝ≥0∞) (W : State) (tau : ℝ)
    (hTau : tau ≤ queryConfidenceSigma (State := State) (Srt := Srt) (Query := Query) κ W q₁) :
    tau ≤ queryConfidenceSigma (State := State) (Srt := Srt) (Query := Query) κ W q₂ := by
  simpa [WMQueryEqSigma.to_queryConfidence (State := State) (Srt := Srt) (Query := Query) hEq κ W] using hTau

/-- Typed atom semantics: confidence threshold over encoded typed queries. -/
noncomputable def thresholdAtomSemOfWMQSigmaConfidence
    (κ : ℝ≥0∞) (W : State) (tau : ℝ)
    (queryOfAtom : String → Pattern → Sigma Query) : AtomSem :=
  fun a p => tau ≤ queryConfidenceSigma (State := State) (Srt := Srt) (Query := Query)
    κ W (queryOfAtom a p)

/-- Typed rewrite soundness transferred to confidence-view atom equality. -/
theorem wmRewriteRuleSigma_confidence_atom_eq_derive
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (κ : ℝ≥0∞) (W : State)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion) :
    queryConfidenceSigma (State := State) (Srt := Srt) (Query := Query) κ W (queryOfAtom a p) =
      (BinaryEvidence.toConfidence κ (r.derive W)).toReal := by
  rw [hEnc]
  have hEq :
      WorldModelSigma.queryConfidence (State := State) (Srt := Srt) (Query := Query) κ W
          r.conclusion =
        BinaryEvidence.toConfidence κ (r.derive W) := by
    simp [WorldModelSigma.queryConfidence, r.sound hSide W]
  exact congrArg ENNReal.toReal hEq

/-- Typed confidence-threshold consequence for an atom from a WM rewrite rule. -/
theorem wmRewriteRuleSigma_threshold_atom_confidence
    (R : Pattern → Pattern → Prop)
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (κ : ℝ≥0∞) (W : State)
    (tau : ℝ)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ (BinaryEvidence.toConfidence κ (r.derive W)).toReal) :
    sem R (thresholdAtomSemOfWMQSigmaConfidence (State := State) (Srt := Srt) (Query := Query)
      κ W tau queryOfAtom) (.atom a) p := by
  show tau ≤ queryConfidenceSigma (State := State) (Srt := Srt) (Query := Query) κ W (queryOfAtom a p)
  simpa [wmRewriteRuleSigma_confidence_atom_eq_derive
    (State := State) (Srt := Srt) (Query := Query) r hSide κ W queryOfAtom a p hEnc] using hTau

/-- One-call typed endpoint: rewrite soundness + query-equivalence transport
for confidence-threshold atom semantics. -/
theorem rewrite_then_queryEq_threshold_atom_confidence_sigma
    (R : Pattern → Pattern → Prop)
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (κ : ℝ≥0∞) (W : State)
    (tau : ℝ)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc₁ : queryOfAtom₁ a p = r.conclusion)
    (hEq : WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Srt) (Query := Query)
      (queryOfAtom₁ a p) (queryOfAtom₂ a p))
    (hTau : tau ≤ (BinaryEvidence.toConfidence κ (r.derive W)).toReal) :
    sem R (thresholdAtomSemOfWMQSigmaConfidence
      (State := State) (Srt := Srt) (Query := Query)
      κ W tau queryOfAtom₂) (.atom a) p := by
  have hq1 : tau ≤ queryConfidenceSigma
      (State := State) (Srt := Srt) (Query := Query)
      κ W (queryOfAtom₁ a p) := by
    simpa [wmRewriteRuleSigma_confidence_atom_eq_derive
      (State := State) (Srt := Srt) (Query := Query)
      r hSide κ W queryOfAtom₁ a p hEnc₁] using hTau
  have hq2 := WMQueryEqSigma.to_queryConfidence_threshold
      (State := State) (Srt := Srt) (Query := Query) hEq κ W tau hq1
  exact hq2

end Typed

end Mettapedia.Logic.PLNErrorMagnificationGrounding
