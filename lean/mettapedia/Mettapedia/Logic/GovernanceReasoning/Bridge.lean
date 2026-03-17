import Mettapedia.Logic.GovernanceReasoning.Core
import Mettapedia.Logic.PLNWorldModelCalculus

/-!
# Governance Reasoning: WM Calculus Bridge

Links the governance-reasoning types (eventualities, modalities, DTS) to the
PLN world-model calculus (`BinaryWorldModel`, `WMRewriteRule`, `BinaryEvidence`).

## Architecture

- §1 Deontic query encoder (following `EventQueryEncoder` pattern)
- §2 Rexist bridge rule (Hobbs □A→A as `WMRewriteRule`)
- §3 DTS evidence bridge (evidence-level DTS under consistent WM)
- §4 Role contradiction (thematic role disagreement → negation)

## References

- Hobbs, J. (1985). "Ontological Promiscuity"
- governance-reasoning-engine/reason/statement_level.metta (□A→A bridge)
- governance-reasoning-engine/reason/eventuality_level.metta (role negation)
-/

namespace Mettapedia.Logic.GovernanceReasoning.Bridge

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.GovernanceReasoning.Core

open scoped ENNReal

/-! ## §1 Deontic Query Encoder

Following the `EventQueryEncoder` pattern from `PLNProbabilisticEventCalculus.lean:97`:
a structure packaging the mapping from (modality, eventuality) pairs and
ground triples to WM queries. -/

/-- Query encoder for deontic governance reasoning.

    Maps (modality × eventuality) pairs to WM queries, and ground triples
    to WM queries.  This is the semantic bridge between the governance
    type system and the WM evidence calculus. -/
structure DeonticQueryEncoder (Entity Pred Query : Type*) where
  /-- Encode a modal query: "what is the evidence that eventuality `e` has modality `m`?" -/
  modalQuery : DeonticModality → Eventuality Entity Pred → Query
  /-- Encode a ground query: "what is the evidence for ct-triple `t`?" -/
  groundQuery : CTTriple Entity Pred → Query

namespace DeonticQueryEncoder

variable {State Entity Pred Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- Extract evidence for a modal judgment from a WM state. -/
def modalEvidence (W : State) (enc : DeonticQueryEncoder Entity Pred Query)
    (m : DeonticModality) (e : Eventuality Entity Pred) : BinaryEvidence :=
  BinaryWorldModel.evidence (State := State) (Query := Query) W (enc.modalQuery m e)

/-- Extract evidence for a ground triple from a WM state. -/
def groundEvidence (W : State) (enc : DeonticQueryEncoder Entity Pred Query)
    (t : CTTriple Entity Pred) : BinaryEvidence :=
  BinaryWorldModel.evidence (State := State) (Query := Query) W (enc.groundQuery t)

/-- Extract posterior-mean strength for a modal judgment. -/
noncomputable def modalStrength (W : State) (enc : DeonticQueryEncoder Entity Pred Query)
    (m : DeonticModality) (e : Eventuality Entity Pred) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (modalEvidence (State := State) W enc m e)

/-- Modal evidence commutes with revision. -/
theorem modalEvidence_add (W₁ W₂ : State)
    (enc : DeonticQueryEncoder Entity Pred Query)
    (m : DeonticModality) (e : Eventuality Entity Pred) :
    modalEvidence (State := State) (W₁ + W₂) enc m e =
      modalEvidence (State := State) W₁ enc m e +
        modalEvidence (State := State) W₂ enc m e := by
  simp [modalEvidence, BinaryWorldModel.evidence_add]

/-- Ground evidence commutes with revision. -/
theorem groundEvidence_add (W₁ W₂ : State)
    (enc : DeonticQueryEncoder Entity Pred Query)
    (t : CTTriple Entity Pred) :
    groundEvidence (State := State) (W₁ + W₂) enc t =
      groundEvidence (State := State) W₁ enc t +
        groundEvidence (State := State) W₂ enc t := by
  simp [groundEvidence, BinaryWorldModel.evidence_add]

end DeonticQueryEncoder

/-! ## §2 Rexist Bridge Rule

The Hobbs bridge: □A→A ("everything that really exists holds true").

In the governance-reasoning-engine (`statement_level.metta:37-44`):
if a meta-triple is tagged as `rexist` and `hold`, the underlying ct-triple
is asserted as ground truth.

We formalize this as a `WMRewriteRule` whose side condition is the
bridge hypothesis: rexist evidence equals ground evidence. -/

section RexistBridge

variable {State Entity Pred Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- The Hobbs Rexist bridge hypothesis for an eventuality:
    rexist-evidence for `e` equals ground-evidence for the corresponding ct-triple.

    This is a semantic assumption about the world model: the act of asserting
    that an eventuality "really exists" is equivalent to asserting the
    corresponding ground fact. -/
def RexistBridge
    (enc : DeonticQueryEncoder Entity Pred Query)
    (e : Eventuality Entity Pred)
    (t : CTTriple Entity Pred) : Prop :=
  WMQueryEq (State := State) (Query := Query) (enc.modalQuery .rexist e) (enc.groundQuery t)

/-- The Rexist bridge as a `WMRewriteRule`:
    under the bridge hypothesis, rexist-evidence derives ground-evidence.

    Matches `statement_level.metta:37-44` (□A→A bridge). -/
def rexistBridgeRule
    (enc : DeonticQueryEncoder Entity Pred Query)
    (e : Eventuality Entity Pred) (t : CTTriple Entity Pred)
    (hBridge : RexistBridge (State := State) enc e t) :
    WMRewriteRule State Query :=
  { side := True
    conclusion := enc.groundQuery t
    derive := fun W => BinaryWorldModel.evidence (State := State) (Query := Query) W (enc.modalQuery .rexist e)
    sound := by
      intro _ W
      exact hBridge W }

/-- Contrapositive of the bridge: if ground evidence is zero, rexist evidence is zero.
    This formalizes the converse direction used in `statement_level.metta:128-152`. -/
theorem rexistBridge_zero_ground
    (enc : DeonticQueryEncoder Entity Pred Query)
    (e : Eventuality Entity Pred) (t : CTTriple Entity Pred)
    (hBridge : RexistBridge (State := State) enc e t)
    (W : State)
    (hZero : BinaryWorldModel.evidence (State := State) (Query := Query) W (enc.groundQuery t) = 0) :
    BinaryWorldModel.evidence (State := State) (Query := Query) W (enc.modalQuery .rexist e) = 0 := by
  rw [hBridge W, hZero]

end RexistBridge

/-! ## §3 DTS BinaryEvidence Bridge

BinaryEvidence-level versions of the DTS axioms under a "consistent deontic WM" hypothesis.

A consistent deontic WM ensures that obligation-evidence for `e` and obligation-evidence
for `¬e` cannot both be positive (mirroring `DTS.consistent`). -/

section DTSEvidence

variable {State Entity Pred Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- A consistent deontic world model: if obligation evidence for `e` is positive,
    then obligation evidence for `¬e` is zero.

    This is the evidence-level analogue of `DTS.consistent`:
    OB(p) ⇒ ¬OB(¬p). -/
structure ConsistentDeonticWM
    (enc : DeonticQueryEncoder Entity Pred Query)
    (negE : Eventuality Entity Pred → Eventuality Entity Pred) where
  /-- If obligation evidence for `e` is positive, obligation evidence for `¬e` is zero. -/
  ob_consistent : ∀ (W : State) (e : Eventuality Entity Pred),
    DeonticQueryEncoder.modalEvidence (State := State) W enc .obligatory e ≠ 0 →
    DeonticQueryEncoder.modalEvidence (State := State) W enc .obligatory (negE e) = 0

/-- If obligation evidence for `e` is positive and the WM is consistent,
    then obligation evidence for `¬e` is zero. (Direct accessor.) -/
theorem ob_neg_zero_of_ob_pos
    (enc : DeonticQueryEncoder Entity Pred Query)
    (negE : Eventuality Entity Pred → Eventuality Entity Pred)
    (hCons : ConsistentDeonticWM (State := State) enc negE)
    (W : State) (e : Eventuality Entity Pred)
    (hPos : DeonticQueryEncoder.modalEvidence (State := State) W enc .obligatory e ≠ 0) :
    DeonticQueryEncoder.modalEvidence (State := State) W enc .obligatory (negE e) = 0 :=
  hCons.ob_consistent W e hPos

/-- A consistent deontic WM induces a propositional DTS on the "has positive evidence" predicate. -/
def consistentDeonticWM_induces_dts
    (enc : DeonticQueryEncoder Entity Pred Query)
    (negE : Eventuality Entity Pred → Eventuality Entity Pred)
    (hNegNeg : ∀ e, negE (negE e) = e)
    (hCons : ConsistentDeonticWM (State := State) enc negE)
    (W : State) :
    DTS (Eventuality Entity Pred) :=
  { ob := fun e => DeonticQueryEncoder.modalEvidence (State := State) W enc .obligatory e ≠ 0
    neg := negE
    neg_neg := hNegNeg
    consistent := fun e hob hob_neg => by
      have := hCons.ob_consistent W e hob
      exact hob_neg this }

end DTSEvidence

/-! ## §4 Role Contradiction

Two eventualities are role-contradictory if they share the same predicate type
but disagree on at least one thematic role assignment.

This formalizes `eventuality_level.metta:16-50`: negation inference from
thematic role disagreement. -/

section RoleContradiction

variable {Entity Pred : Type*}

/-- Two eventualities are role-contradictory when they have the same predicate
    but disagree on at least one thematic role value.

    Matches the negation inference at `eventuality_level.metta:16-50`. -/
def roleContradictory [DecidableEq Entity] [DecidableEq Pred]
    (e₁ e₂ : Eventuality Entity Pred) : Prop :=
  e₁.predicate = e₂.predicate ∧
  ∃ r : ThematicRole, ∃ a b : Entity,
    e₁.roles r = some a ∧ e₂.roles r = some b ∧ a ≠ b

/-- Role contradiction is symmetric. -/
theorem roleContradictory_symm [DecidableEq Entity] [DecidableEq Pred]
    (e₁ e₂ : Eventuality Entity Pred)
    (h : roleContradictory e₁ e₂) : roleContradictory e₂ e₁ := by
  obtain ⟨hpred, r, a, b, ha, hb, hne⟩ := h
  exact ⟨hpred.symm, r, b, a, hb, ha, hne.symm⟩

/-- Role contradiction is irreflexive. -/
theorem roleContradictory_irrefl [DecidableEq Entity] [DecidableEq Pred]
    (e : Eventuality Entity Pred) : ¬ roleContradictory e e := by
  intro ⟨_, _, _, _, ha, hb, hne⟩
  rw [ha] at hb
  exact hne (Option.some_injective _ hb)

/-- If two eventualities with the same predicate agree on all assigned roles,
    they are not role-contradictory. -/
theorem not_roleContradictory_of_agree [DecidableEq Entity] [DecidableEq Pred]
    (e₁ e₂ : Eventuality Entity Pred)
    (_hpred : e₁.predicate = e₂.predicate)
    (hagree : ∀ r a b, e₁.roles r = some a → e₂.roles r = some b → a = b) :
    ¬ roleContradictory e₁ e₂ := by
  intro ⟨_, r, a, b, ha, hb, hne⟩
  exact hne (hagree r a b ha hb)

end RoleContradiction

end Mettapedia.Logic.GovernanceReasoning.Bridge
