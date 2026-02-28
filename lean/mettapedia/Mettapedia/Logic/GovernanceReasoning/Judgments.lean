import Mettapedia.Logic.GovernanceReasoning.Bridge

/-!
# Governance Reasoning: Three-Level Judgment System

Formalizes the 3-level inference architecture from the governance-reasoning-engine:
- Level 1 (Eventuality): conjunction/disjunction over modalities, negation
- Level 2 (Statement): Hobbs Rexist bridge, DTS derivations
- Level 3 (Governance): contradiction, compliance, violation, conflict, necessary violation

## References

- governance-reasoning-engine/reason/eventuality_level.metta
- governance-reasoning-engine/reason/statement_level.metta
- governance-reasoning-engine/reason/judgement_level.metta
-/

namespace Mettapedia.Logic.GovernanceReasoning.Judgments

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.GovernanceReasoning.Core
open Mettapedia.Logic.GovernanceReasoning.Bridge

/-! ## §1 Level 1 — Eventuality Judgments

An eventuality judgment records evidence for an eventuality under a specific modality.
Level 1 inference operations: conjunction, disjunction, negation.

Matches `eventuality_level.metta`. -/

/-- An eventuality judgment: evidence that eventuality `e` has modality `m`.

    For example: `⟨soaMoor, .obligatory, Evidence.mk 5 1⟩` means
    "there is evidence (5 positive, 1 negative) that mooring is obligatory". -/
structure EventualityJudgment (Entity Pred : Type*) where
  /-- The eventuality being judged. -/
  eventuality : Eventuality Entity Pred
  /-- The deontic modality. -/
  modality : DeonticModality
  /-- The evidence for this judgment. -/
  evidence : Evidence

namespace EventualityJudgment

variable {Entity Pred : Type*}

/-- Conjunction of two judgments on the same modality.
    Evidence is the infimum (lattice meet): the weakest common evidence.

    Matches `eventuality_level.metta:58-66`:
    `∀ea,e1,e2[and(ea,e1,e2) ⇒ (ropom(ea) ⇔ (ropom(e1) ∧ ropom(e2)))]` -/
noncomputable def conjoin (j₁ j₂ : EventualityJudgment Entity Pred)
    (conj_e : Eventuality Entity Pred)
    (_hmod : j₁.modality = j₂.modality) :
    EventualityJudgment Entity Pred :=
  { eventuality := conj_e
    modality := j₁.modality
    evidence := j₁.evidence ⊓ j₂.evidence }

/-- Conjunction evidence is ≤ each component. -/
theorem conjoin_evidence_le_left (j₁ j₂ : EventualityJudgment Entity Pred)
    (conj_e : Eventuality Entity Pred) (hmod : j₁.modality = j₂.modality) :
    (conjoin j₁ j₂ conj_e hmod).evidence ≤ j₁.evidence :=
  inf_le_left

theorem conjoin_evidence_le_right (j₁ j₂ : EventualityJudgment Entity Pred)
    (conj_e : Eventuality Entity Pred) (hmod : j₁.modality = j₂.modality) :
    (conjoin j₁ j₂ conj_e hmod).evidence ≤ j₂.evidence :=
  inf_le_right

/-- Disjunction of two judgments on the same modality.
    Evidence is the supremum (lattice join): the strongest available evidence.

    Matches `eventuality_level.metta:85-98` and `statement_level.metta:155-188`. -/
noncomputable def disjoin (j₁ j₂ : EventualityJudgment Entity Pred)
    (disj_e : Eventuality Entity Pred)
    (_hmod : j₁.modality = j₂.modality) :
    EventualityJudgment Entity Pred :=
  { eventuality := disj_e
    modality := j₁.modality
    evidence := j₁.evidence ⊔ j₂.evidence }

/-- Disjunction evidence is ≥ each component. -/
theorem disjoin_evidence_ge_left (j₁ j₂ : EventualityJudgment Entity Pred)
    (disj_e : Eventuality Entity Pred) (hmod : j₁.modality = j₂.modality) :
    j₁.evidence ≤ (disjoin j₁ j₂ disj_e hmod).evidence :=
  le_sup_left

theorem disjoin_evidence_ge_right (j₁ j₂ : EventualityJudgment Entity Pred)
    (disj_e : Eventuality Entity Pred) (hmod : j₁.modality = j₂.modality) :
    j₂.evidence ≤ (disjoin j₁ j₂ disj_e hmod).evidence :=
  le_sup_right

/-- Negation: flip the eventuality polarity, swap positive/negative evidence.

    Matches `eventuality_level.metta:16-50`: when two eventualities disagree
    on a thematic role, one is the negation of the other. -/
def negate (j : EventualityJudgment Entity Pred) :
    EventualityJudgment Entity Pred :=
  { eventuality := j.eventuality.negate
    modality := j.modality
    evidence := Evidence.mk j.evidence.neg j.evidence.pos }

/-- Double negation returns to the original eventuality. -/
theorem negate_negate_eventuality (j : EventualityJudgment Entity Pred) :
    (j.negate.negate).eventuality = j.eventuality :=
  Eventuality.negate_negate j.eventuality

/-- Double negation returns to the original evidence. -/
theorem negate_negate_evidence (j : EventualityJudgment Entity Pred) :
    (j.negate.negate).evidence = j.evidence := by
  apply Evidence.ext' <;> simp [negate]

end EventualityJudgment

/-! ## §2 Level 2 — Statement Judgments

Level 2 enriches Level 1 with:
- The Hobbs Rexist bridge (□A→A)
- DTS derivations (OB ⇒ PE, etc.)

Matches `statement_level.metta` and `DTS.metta`. -/

/-- A statement judgment: a Level 1 judgment plus its derivation history.
    The constructors track how the judgment was derived. -/
inductive StatementJudgment (Entity Pred : Type*) where
  /-- Lift a Level 1 judgment. -/
  | fromL1 : EventualityJudgment Entity Pred → StatementJudgment Entity Pred
  /-- Apply the Rexist bridge: if modality = rexist, assert as ground truth.
      Matches `statement_level.metta:37-44`. -/
  | rexistBridge : EventualityJudgment Entity Pred →
      StatementJudgment Entity Pred
  /-- Apply a DTS derivation: derive a new modality from an existing judgment.
      For example: OB(e) ⇒ PE(e). -/
  | dtsDerive : EventualityJudgment Entity Pred → DeonticModality →
      StatementJudgment Entity Pred
  /-- Apply negation inference from Rexist status.
      If Rexist(e) holds, then ¬Rexist(¬e).
      Matches `statement_level.metta:128-152`. -/
  | rexistNeg : EventualityJudgment Entity Pred →
      StatementJudgment Entity Pred

namespace StatementJudgment

variable {Entity Pred : Type*}

/-- Extract the underlying eventuality judgment from a statement judgment. -/
def toJudgment : StatementJudgment Entity Pred → EventualityJudgment Entity Pred
  | fromL1 j => j
  | rexistBridge j => j
  | dtsDerive j m =>
    { eventuality := j.eventuality
      modality := m
      evidence := j.evidence }
  | rexistNeg j =>
    { eventuality := j.eventuality.negate
      modality := .rexist
      evidence := Evidence.mk j.evidence.neg j.evidence.pos }

/-- DTS derive preserves evidence. -/
theorem dtsDerive_evidence (j : EventualityJudgment Entity Pred) (m : DeonticModality) :
    (dtsDerive j m).toJudgment.evidence = j.evidence := rfl

end StatementJudgment

/-! ## §3 Level 3 — Governance Verdicts

The highest level detects logical/deontic problems in a set of judgments:
- Contradictions: both Rexist(e) and Rexist(¬e)
- Violations: OB(e) but ¬Rexist(e)
- Conflicts: OB(e) and OB(¬e) (via derived permission)
- Necessary violations: conflict where every resolution violates

Matches `judgement_level.metta`. -/

/-- Governance verdict: the outcome of analyzing a set of judgments. -/
inductive GovernanceVerdict where
  /-- No issues found. -/
  | compliant
  /-- An obligation is not fulfilled in reality. -/
  | violation
  /-- Two norms conflict (e.g., something is both obligatory and forbidden). -/
  | conflict
  /-- A conflict where every resolution path leads to a violation. -/
  | necessaryViolation
  /-- Contradictory factual assertions (e.g., both Rexist(e) and Rexist(¬e)). -/
  | contradiction
  deriving DecidableEq, Repr

section Detection

variable {Entity Pred : Type*} [DecidableEq Pred]

/-- A judgment list contains a contradiction:
    both `Rexist(e)` and `Rexist(¬e)` have positive evidence for matching predicates.

    Matches `judgement_level.metta:27-32`. -/
def HasContradiction
    (js : List (EventualityJudgment Entity Pred)) : Prop :=
  ∃ j₁ ∈ js, ∃ j₂ ∈ js,
    j₁.modality = .rexist ∧ j₁.evidence.pos ≠ 0 ∧
    j₂.modality = .rexist ∧ j₂.evidence.pos ≠ 0 ∧
    j₁.eventuality.predicate = j₂.eventuality.predicate ∧
    j₁.eventuality.polarity ≠ j₂.eventuality.polarity

/-- A judgment list contains a violation:
    `Obligatory(e)` has positive evidence but no matching `Rexist(e)` with positive evidence.

    Matches `judgement_level.metta:74-81`. -/
def HasViolation
    (js : List (EventualityJudgment Entity Pred)) : Prop :=
  ∃ j_ob ∈ js,
    j_ob.modality = .obligatory ∧ j_ob.evidence.pos ≠ 0 ∧
    ∀ j_re ∈ js,
      j_re.modality = .rexist →
      j_re.eventuality.predicate = j_ob.eventuality.predicate →
      j_re.eventuality.polarity = j_ob.eventuality.polarity →
      j_re.evidence.pos = 0

/-- A judgment list contains a conflict:
    both `Obligatory(e)` and `Obligatory(¬e)` have positive evidence for matching predicates.

    Matches `judgement_level.metta:88-99`. -/
def HasConflict
    (js : List (EventualityJudgment Entity Pred)) : Prop :=
  ∃ j₁ ∈ js, ∃ j₂ ∈ js,
    j₁.modality = .obligatory ∧ j₁.evidence.pos ≠ 0 ∧
    j₂.modality = .obligatory ∧ j₂.evidence.pos ≠ 0 ∧
    j₁.eventuality.predicate = j₂.eventuality.predicate ∧
    j₁.eventuality.polarity ≠ j₂.eventuality.polarity

/-- A necessary violation: a conflict where there is also a violation.

    Matches `judgement_level.metta:107-127`. -/
def HasNecessaryViolation
    (js : List (EventualityJudgment Entity Pred)) : Prop :=
  HasConflict js ∧ HasViolation js

/-- The overall governance analysis: return the most severe verdict. -/
noncomputable def governanceAnalysis
    (js : List (EventualityJudgment Entity Pred)) : GovernanceVerdict :=
  @ite _ (HasContradiction js) (Classical.propDecidable _) .contradiction
    (@ite _ (HasNecessaryViolation js) (Classical.propDecidable _) .necessaryViolation
      (@ite _ (HasConflict js) (Classical.propDecidable _) .conflict
        (@ite _ (HasViolation js) (Classical.propDecidable _) .violation
          .compliant)))

end Detection

/-! ## §4 Soundness Theorems -/

section GovernanceAnalysisSoundness

variable {Entity Pred : Type*} [DecidableEq Pred]

set_option linter.unusedSectionVars false in
private theorem governanceAnalysis_compliant_aux
    (js : List (EventualityJudgment Entity Pred))
    (hc : governanceAnalysis js = .compliant) :
    ¬ HasContradiction js ∧ ¬ HasNecessaryViolation js ∧
    ¬ HasConflict js ∧ ¬ HasViolation js := by
  unfold governanceAnalysis at hc
  split_ifs at hc with h1 h2 h3 h4
  all_goals first | exact absurd hc (by decide) | exact ⟨h1, h2, h3, h4⟩

/-- If the verdict is `compliant`, there are no violations. -/
theorem compliant_no_violation
    (js : List (EventualityJudgment Entity Pred))
    (hc : governanceAnalysis js = .compliant) :
    ¬ HasViolation js :=
  (governanceAnalysis_compliant_aux js hc).2.2.2

/-- If the verdict is `compliant`, there are no conflicts. -/
theorem compliant_no_conflict
    (js : List (EventualityJudgment Entity Pred))
    (hc : governanceAnalysis js = .compliant) :
    ¬ HasConflict js :=
  (governanceAnalysis_compliant_aux js hc).2.2.1

/-- If the verdict is `compliant`, there are no contradictions. -/
theorem compliant_no_contradiction
    (js : List (EventualityJudgment Entity Pred))
    (hc : governanceAnalysis js = .compliant) :
    ¬ HasContradiction js :=
  (governanceAnalysis_compliant_aux js hc).1

end GovernanceAnalysisSoundness

section ExtractionTheorems

variable {Entity Pred : Type*}

/-- If a violation is detected, there exists an obligatory judgment with positive
    evidence that has no matching rexist judgment. -/
theorem violation_has_unmatched_obligation
    (js : List (EventualityJudgment Entity Pred))
    (hv : HasViolation js) :
    ∃ j ∈ js,
      j.modality = .obligatory ∧
      j.evidence.pos ≠ 0 ∧
      ∀ j' ∈ js,
        j'.modality = .rexist →
        j'.eventuality.predicate = j.eventuality.predicate →
        j'.eventuality.polarity = j.eventuality.polarity →
        j'.evidence.pos = 0 := hv

/-- If a conflict is detected, there exist two obligatory judgments on
    opposite-polarity eventualities with the same predicate. -/
theorem conflict_has_opposite_obligations
    (js : List (EventualityJudgment Entity Pred))
    (hv : HasConflict js) :
    ∃ j₁ ∈ js, ∃ j₂ ∈ js,
      j₁.modality = .obligatory ∧
      j₂.modality = .obligatory ∧
      j₁.evidence.pos ≠ 0 ∧
      j₂.evidence.pos ≠ 0 ∧
      j₁.eventuality.predicate = j₂.eventuality.predicate ∧
      j₁.eventuality.polarity ≠ j₂.eventuality.polarity := by
  obtain ⟨j₁, hm₁, j₂, hm₂, hmod₁, hpos₁, hmod₂, hpos₂, hpred, hpol⟩ := hv
  exact ⟨j₁, hm₁, j₂, hm₂, hmod₁, hmod₂, hpos₁, hpos₂, hpred, hpol⟩

/-- Under a consistent DTS, a conflict on the same predicate is impossible:
    OB(e) and OB(¬e) cannot both hold.

    This theorem shows that the `conflict` verdict can only arise in an
    inconsistent normative framework. -/
theorem consistent_dts_precludes_conflict
    {P : Type*} (d : DTS P) (p : P) :
    ¬ (d.ob p ∧ d.ob (d.neg p)) := by
  intro ⟨hob, hob_neg⟩
  exact d.consistent p hob hob_neg

/-- A necessary violation is at least as severe as a conflict. -/
theorem necessaryViolation_implies_conflict
    (js : List (EventualityJudgment Entity Pred))
    (hnv : HasNecessaryViolation js) :
    HasConflict js :=
  hnv.1

/-- A necessary violation is at least as severe as a violation. -/
theorem necessaryViolation_implies_violation
    (js : List (EventualityJudgment Entity Pred))
    (hnv : HasNecessaryViolation js) :
    HasViolation js :=
  hnv.2

end ExtractionTheorems

end Mettapedia.Logic.GovernanceReasoning.Judgments
