import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWMOSLFBridge
import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.PLNRevision

/-!
# PLN Xi Rule Registry

Instantiates the WM-calculus rewrite rule templates for the **exact-track** PLN rules:
deduction, source rule (induction), sink rule (abduction), and revision.

Each rule is a `WMRewriteRule` with explicit side conditions `Σ`. The registry
also provides:

- **Strength equivalence theorems**: derived from screening-off alone (non-tautological)
- **Structured Bayes+deduction decomposition**: for source/sink rules
- **OSLF atom bridge theorems**: evidence-level and threshold-level via `PLNWMOSLFBridge`

## Rule Classification

| Rule | Track | WM Form | Legacy Formula |
|------|-------|---------|----------------|
| Deduction | Exact | `xi_deduction_rewrite` | `plnDeductionStrength` |
| SourceRule | Exact | `xi_sourceRule_rewrite` | `plnInductionStrength` |
| SinkRule | Exact | `xi_sinkRule_rewrite` | `plnAbductionStrength` |
| Revision | Exact | `BinaryWorldModel.evidence_add` (axiom) | `revision` = hplus |

Heuristic rules (modus ponens, symmetric MP, inversion) are NOT included here
and require explicit bound/conditional theorems — see future `PLNXiHeuristicRules.lean`.

All theorems are fully proved (0 sorry).
-/

namespace Mettapedia.Logic.PLNXiRuleRegistry

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWMOSLFBridge
open Mettapedia.Logic.PLN
open Mettapedia.Logic.PLNRevision
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.OSLFEvidenceSemantics

open scoped ENNReal

/-! ## §1 Exact-Track Rewrite Rules

These rules derive query evidence from other query evidence under explicit
side conditions. They stay in the `BinaryEvidence` world and compose with the
WM-calculus bridge. -/

section ExactTrack

variable {Atom State : Type*} [EvidenceType State] [BinaryWorldModel State (AtomQuery Atom)]

/-! ### Deduction

The deduction rewrite template is already defined in `PLNWorldModelCalculus.lean`.
We provide a canonical instantiation with a generic `combine` function and
explicit screening-off side condition. -/

/-- Screening-off side condition for deduction: the `combine` function correctly
computes `link A C` evidence from `link A B` and `link B C` evidence.

This is the abstract formulation. Concrete models (e.g. ChainBN) discharge it
via `chainBN_pos_screeningOff` + `chainBN_neg_screeningOff`. -/
def DeductionScreeningOff
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence) : Prop :=
  ∀ W : State,
    combine
      (AtomQuery.linkEvidence (State := State) (Atom := Atom) W A B)
      (AtomQuery.linkEvidence (State := State) (Atom := Atom) W B C) =
    AtomQuery.linkEvidence (State := State) (Atom := Atom) W A C

/-- Deduction rewrite rule: under screening-off, `link A C` evidence is
computed from `link A B` and `link B C` via `combine`. -/
def xi_deduction_rewrite
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence) :
    WMRewriteRule State (AtomQuery Atom) :=
  { side := DeductionScreeningOff (State := State) A B C combine
    conclusion := AtomQuery.link A C
    derive := fun W =>
      combine (AtomQuery.linkEvidence W A B) (AtomQuery.linkEvidence W B C)
    sound := fun hSigma W => hSigma W }

/-- Direct verification: the deduction rule derives the correct evidence. -/
theorem xi_deduction_derives
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence) (W : State) :
    (xi_deduction_rewrite (State := State) A B C combine).derive W =
      combine (AtomQuery.linkEvidence W A B) (AtomQuery.linkEvidence W B C) := rfl

/-! ### Source Rule (Induction)

Pattern: `B → A, B → C ⊢ A → C` via Bayes-inverting B→A to A→B, then deduction.

At evidence level: combine `link B A` and `link B C` to get `link A C`. -/

/-- Source-rule side condition: combining link evidence from `B→A` and `B→C`
correctly computes `link A C` evidence (Bayes+Deduction at evidence level). -/
def SourceRuleScreeningOff
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence) : Prop :=
  ∀ W : State,
    combine
      (AtomQuery.linkEvidence (State := State) (Atom := Atom) W B A)
      (AtomQuery.linkEvidence (State := State) (Atom := Atom) W B C) =
    AtomQuery.linkEvidence (State := State) (Atom := Atom) W A C

/-- Source rule (induction) rewrite: under Σ, `link A C` evidence is computed
from `link B A` and `link B C` via `combine`. -/
def xi_sourceRule_rewrite
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence) :
    WMRewriteRule State (AtomQuery Atom) :=
  { side := SourceRuleScreeningOff (State := State) A B C combine
    conclusion := AtomQuery.link A C
    derive := fun W =>
      combine (AtomQuery.linkEvidence W B A) (AtomQuery.linkEvidence W B C)
    sound := fun hSigma W => hSigma W }

/-- Direct verification for source rule. -/
theorem xi_sourceRule_derives
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence) (W : State) :
    (xi_sourceRule_rewrite (State := State) A B C combine).derive W =
      combine (AtomQuery.linkEvidence W B A) (AtomQuery.linkEvidence W B C) := rfl

/-! ### Sink Rule (Abduction)

Pattern: `A → B, C → B ⊢ A → C` via Bayes-inverting C→B to B→C, then deduction. -/

/-- Sink-rule side condition: combining link evidence from `A→B` and `C→B`
correctly computes `link A C` evidence (Bayes+Deduction at evidence level). -/
def SinkRuleScreeningOff
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence) : Prop :=
  ∀ W : State,
    combine
      (AtomQuery.linkEvidence (State := State) (Atom := Atom) W A B)
      (AtomQuery.linkEvidence (State := State) (Atom := Atom) W C B) =
    AtomQuery.linkEvidence (State := State) (Atom := Atom) W A C

/-- Sink rule (abduction) rewrite: under Σ, `link A C` evidence is computed
from `link A B` and `link C B` via `combine`. -/
def xi_sinkRule_rewrite
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence) :
    WMRewriteRule State (AtomQuery Atom) :=
  { side := SinkRuleScreeningOff (State := State) A B C combine
    conclusion := AtomQuery.link A C
    derive := fun W =>
      combine (AtomQuery.linkEvidence W A B) (AtomQuery.linkEvidence W C B)
    sound := fun hSigma W => hSigma W }

/-- Direct verification for sink rule. -/
theorem xi_sinkRule_derives
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence) (W : State) :
    (xi_sinkRule_rewrite (State := State) A B C combine).derive W =
      combine (AtomQuery.linkEvidence W A B) (AtomQuery.linkEvidence W C B) := rfl

/-! ### Structured Bayes+Deduction Decomposition

The source and sink rules are conceptually Bayes inversion followed by deduction.
These structures make that decomposition explicit. -/

/-- Structured source-rule side condition: Bayes inversion of link B→A
to A→B, followed by deduction A→B, B→C ⊢ A→C. -/
structure SourceRuleBayesDed
    (A B C : Atom) (invert : BinaryEvidence → BinaryEvidence)
    (dedCombine : BinaryEvidence → BinaryEvidence → BinaryEvidence) : Prop where
  /-- Bayes inversion: link B→A evidence maps to link A→B evidence. -/
  bayes : ∀ W : State,
    invert (AtomQuery.linkEvidence (State := State) (Atom := Atom) W B A) =
      AtomQuery.linkEvidence (State := State) (Atom := Atom) W A B
  /-- Deduction: combining link A→B and B→C gives link A→C. -/
  deduction : DeductionScreeningOff (State := State) A B C dedCombine

/-- Structured source-rule implies the flat SourceRuleScreeningOff. -/
theorem sourceBayesDed_implies_screeningOff
    (A B C : Atom) (invert : BinaryEvidence → BinaryEvidence)
    (dedCombine : BinaryEvidence → BinaryEvidence → BinaryEvidence)
    (h : SourceRuleBayesDed (State := State) A B C invert dedCombine) :
    SourceRuleScreeningOff (State := State) A B C
      (fun eBA eBC => dedCombine (invert eBA) eBC) := by
  intro W
  show dedCombine (invert (AtomQuery.linkEvidence W B A))
    (AtomQuery.linkEvidence W B C) = AtomQuery.linkEvidence W A C
  rw [h.bayes W]
  exact h.deduction W

/-- Structured sink-rule side condition: Bayes inversion of link C→B
to B→C, followed by deduction A→B, B→C ⊢ A→C. -/
structure SinkRuleBayesDed
    (A B C : Atom) (invert : BinaryEvidence → BinaryEvidence)
    (dedCombine : BinaryEvidence → BinaryEvidence → BinaryEvidence) : Prop where
  /-- Bayes inversion: link C→B evidence maps to link B→C evidence. -/
  bayes : ∀ W : State,
    invert (AtomQuery.linkEvidence (State := State) (Atom := Atom) W C B) =
      AtomQuery.linkEvidence (State := State) (Atom := Atom) W B C
  /-- Deduction: combining link A→B and B→C gives link A→C. -/
  deduction : DeductionScreeningOff (State := State) A B C dedCombine

/-- Structured sink-rule implies the flat SinkRuleScreeningOff. -/
theorem sinkBayesDed_implies_screeningOff
    (A B C : Atom) (invert : BinaryEvidence → BinaryEvidence)
    (dedCombine : BinaryEvidence → BinaryEvidence → BinaryEvidence)
    (h : SinkRuleBayesDed (State := State) A B C invert dedCombine) :
    SinkRuleScreeningOff (State := State) A B C
      (fun eAB eCB => dedCombine eAB (invert eCB)) := by
  intro W
  show dedCombine (AtomQuery.linkEvidence W A B)
    (invert (AtomQuery.linkEvidence W C B)) = AtomQuery.linkEvidence W A C
  rw [h.bayes W]
  exact h.deduction W

/-! ### Revision

Revision is the WM axiom itself: `evidence (W₁ + W₂) q = evidence W₁ q + evidence W₂ q`.
No separate rule needed — it's built into `BinaryWorldModel.evidence_add`.

The bridge theorem `semE_wm_atom_revision_q` (PLNWMOSLFBridge) already handles
this at the OSLF level. We provide named wrappers for the rule registry. -/

/-- Revision evidence equality for arbitrary query. -/
theorem xi_revision_evidence (W₁ W₂ : State) (q : AtomQuery Atom) :
    BinaryWorldModel.evidence (W₁ + W₂) q =
      BinaryWorldModel.evidence (State := State) (Query := AtomQuery Atom) W₁ q +
      BinaryWorldModel.evidence (State := State) (Query := AtomQuery Atom) W₂ q :=
  BinaryWorldModel.evidence_add W₁ W₂ q

/-- Revision at link level. -/
theorem xi_revision_link (W₁ W₂ : State) (A B : Atom) :
    AtomQuery.linkEvidence (W₁ + W₂) A B =
      AtomQuery.linkEvidence (State := State) (Atom := Atom) W₁ A B +
      AtomQuery.linkEvidence (State := State) (Atom := Atom) W₂ A B :=
  BinaryWorldModel.evidence_add W₁ W₂ (AtomQuery.link A B)

/-- Revision at proposition level. -/
theorem xi_revision_prop (W₁ W₂ : State) (A : Atom) :
    AtomQuery.propEvidence (W₁ + W₂) A =
      AtomQuery.propEvidence (State := State) (Atom := Atom) W₁ A +
      AtomQuery.propEvidence (State := State) (Atom := Atom) W₂ A :=
  BinaryWorldModel.evidence_add W₁ W₂ (AtomQuery.prop A)

end ExactTrack

/-! ## §2 Strength Equivalence

These theorems prove that screening-off ALONE implies the derived strength
equals the WM link strength — no additional hypothesis needed. -/

section StrengthEquivalence

variable {Atom State : Type*} [EvidenceType State] [BinaryWorldModel State (AtomQuery Atom)]

/-- Under screening-off, the deduction rule's derived evidence has the
same strength as the direct WM link A→C evidence. This is a CONSEQUENCE
of the screening-off condition alone — no additional hypothesis needed. -/
theorem xi_deduction_strength_eq_link
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence)
    (hSO : DeductionScreeningOff (State := State) A B C combine)
    (W : State) :
    BinaryEvidence.toStrength ((xi_deduction_rewrite (State := State) A B C combine).derive W) =
      AtomQuery.linkStrength (State := State) (Atom := Atom) W A C := by
  unfold AtomQuery.linkStrength AtomQuery.linkEvidence
  show BinaryEvidence.toStrength (combine _ _) = BinaryEvidence.toStrength (BinaryWorldModel.evidence W _)
  congr 1
  exact hSO W

/-- Under screening-off, source rule's derived strength = link A→C strength. -/
theorem xi_sourceRule_strength_eq_link
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence)
    (hSO : SourceRuleScreeningOff (State := State) A B C combine)
    (W : State) :
    BinaryEvidence.toStrength ((xi_sourceRule_rewrite (State := State) A B C combine).derive W) =
      AtomQuery.linkStrength (State := State) (Atom := Atom) W A C := by
  unfold AtomQuery.linkStrength AtomQuery.linkEvidence
  show BinaryEvidence.toStrength (combine _ _) = BinaryEvidence.toStrength (BinaryWorldModel.evidence W _)
  congr 1
  exact hSO W

/-- Under screening-off, sink rule's derived strength = link A→C strength. -/
theorem xi_sinkRule_strength_eq_link
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence)
    (hSO : SinkRuleScreeningOff (State := State) A B C combine)
    (W : State) :
    BinaryEvidence.toStrength ((xi_sinkRule_rewrite (State := State) A B C combine).derive W) =
      AtomQuery.linkStrength (State := State) (Atom := Atom) W A C := by
  unfold AtomQuery.linkStrength AtomQuery.linkEvidence
  show BinaryEvidence.toStrength (combine _ _) = BinaryEvidence.toStrength (BinaryWorldModel.evidence W _)
  congr 1
  exact hSO W

/-- Revision strength is a weighted average of component strengths.

Direct re-statement of `revision_strength_weighted_avg` from `PLNRevision.lean`
specialized to WM query evidence. -/
theorem xi_revision_strength_weighted_avg
    (W₁ W₂ : State) (q : AtomQuery Atom)
    (h₁ : (BinaryWorldModel.evidence W₁ q).total ≠ 0)
    (h₂ : (BinaryWorldModel.evidence W₂ q).total ≠ 0)
    (h₁₂ : (BinaryWorldModel.evidence (W₁ + W₂) q).total ≠ 0)
    (h₁_top : (BinaryWorldModel.evidence W₁ q).total ≠ ⊤)
    (h₂_top : (BinaryWorldModel.evidence W₂ q).total ≠ ⊤) :
    BinaryEvidence.toStrength (BinaryWorldModel.evidence (W₁ + W₂) q) =
      ((BinaryWorldModel.evidence W₁ q).total / (BinaryWorldModel.evidence (W₁ + W₂) q).total) *
        BinaryEvidence.toStrength (BinaryWorldModel.evidence W₁ q) +
      ((BinaryWorldModel.evidence W₂ q).total / (BinaryWorldModel.evidence (W₁ + W₂) q).total) *
        BinaryEvidence.toStrength (BinaryWorldModel.evidence W₂ q) := by
  have heq := xi_revision_evidence (State := State) W₁ W₂ q
  rw [heq]
  rw [heq] at h₁₂
  exact revision_strength_weighted_avg
    (BinaryWorldModel.evidence W₁ q) (BinaryWorldModel.evidence W₂ q)
    h₁ h₂ h₁₂ h₁_top h₂_top

end StrengthEquivalence

/-! ## §3 OSLF Atom Bridge

These theorems connect the xi rules to OSLF evidence semantics via
`wmRewriteRule_semE_atom_eq_derive` and `wmRewriteRule_threshold_atom`
from `PLNWMOSLFBridge`. -/

section OSLFBridge

variable {Atom State : Type*} [EvidenceType State] [BinaryWorldModel State (AtomQuery Atom)]

/-! ### BinaryEvidence-level bridges (semE) -/

/-- Deduction rule lifts to OSLF atom evidence: if the atom encodes `link A C`,
its evidence equals the `combine` output. -/
theorem xi_deduction_semE_atom
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence)
    (hSO : DeductionScreeningOff (State := State) A B C combine)
    (R : Pattern → Pattern → Prop) (W : State)
    (enc : String → Pattern → AtomQuery Atom)
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.link A C) :
    semE R (wmEvidenceAtomSemQ W enc) (.atom a) p =
      (xi_deduction_rewrite (State := State) A B C combine).derive W :=
  wmRewriteRule_semE_atom_eq_derive R
    (xi_deduction_rewrite A B C combine) hSO W enc a p hEnc

/-- Source rule lifts to OSLF atom evidence. -/
theorem xi_sourceRule_semE_atom
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence)
    (hSO : SourceRuleScreeningOff (State := State) A B C combine)
    (R : Pattern → Pattern → Prop) (W : State)
    (enc : String → Pattern → AtomQuery Atom)
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.link A C) :
    semE R (wmEvidenceAtomSemQ W enc) (.atom a) p =
      (xi_sourceRule_rewrite (State := State) A B C combine).derive W :=
  wmRewriteRule_semE_atom_eq_derive R
    (xi_sourceRule_rewrite A B C combine) hSO W enc a p hEnc

/-- Sink rule lifts to OSLF atom evidence. -/
theorem xi_sinkRule_semE_atom
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence)
    (hSO : SinkRuleScreeningOff (State := State) A B C combine)
    (R : Pattern → Pattern → Prop) (W : State)
    (enc : String → Pattern → AtomQuery Atom)
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.link A C) :
    semE R (wmEvidenceAtomSemQ W enc) (.atom a) p =
      (xi_sinkRule_rewrite (State := State) A B C combine).derive W :=
  wmRewriteRule_semE_atom_eq_derive R
    (xi_sinkRule_rewrite A B C combine) hSO W enc a p hEnc

/-! ### Threshold bridges (sem)

These connect xi rules to strength-threshold Prop semantics.
`hTau` is stated in terms of `rule.derive W` to avoid formula drift. -/

/-- Deduction rule gives threshold atom truth. -/
theorem xi_deduction_threshold_atom
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence)
    (hSO : DeductionScreeningOff (State := State) A B C combine)
    (R : Pattern → Pattern → Prop) (W : State) (tau : ℝ≥0∞)
    (enc : String → Pattern → AtomQuery Atom)
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.link A C)
    (hTau : tau ≤ BinaryEvidence.toStrength
      ((xi_deduction_rewrite (State := State) A B C combine).derive W)) :
    sem R (thresholdAtomSemOfWMQ W tau enc) (.atom a) p :=
  wmRewriteRule_threshold_atom R
    (xi_deduction_rewrite A B C combine) hSO W tau enc a p hEnc hTau

/-- Source rule gives threshold atom truth. -/
theorem xi_sourceRule_threshold_atom
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence)
    (hSO : SourceRuleScreeningOff (State := State) A B C combine)
    (R : Pattern → Pattern → Prop) (W : State) (tau : ℝ≥0∞)
    (enc : String → Pattern → AtomQuery Atom)
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.link A C)
    (hTau : tau ≤ BinaryEvidence.toStrength
      ((xi_sourceRule_rewrite (State := State) A B C combine).derive W)) :
    sem R (thresholdAtomSemOfWMQ W tau enc) (.atom a) p :=
  wmRewriteRule_threshold_atom R
    (xi_sourceRule_rewrite A B C combine) hSO W tau enc a p hEnc hTau

/-- Sink rule gives threshold atom truth. -/
theorem xi_sinkRule_threshold_atom
    (A B C : Atom) (combine : BinaryEvidence → BinaryEvidence → BinaryEvidence)
    (hSO : SinkRuleScreeningOff (State := State) A B C combine)
    (R : Pattern → Pattern → Prop) (W : State) (tau : ℝ≥0∞)
    (enc : String → Pattern → AtomQuery Atom)
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.link A C)
    (hTau : tau ≤ BinaryEvidence.toStrength
      ((xi_sinkRule_rewrite (State := State) A B C combine).derive W)) :
    sem R (thresholdAtomSemOfWMQ W tau enc) (.atom a) p :=
  wmRewriteRule_threshold_atom R
    (xi_sinkRule_rewrite A B C combine) hSO W tau enc a p hEnc hTau

end OSLFBridge

end Mettapedia.Logic.PLNXiRuleRegistry
