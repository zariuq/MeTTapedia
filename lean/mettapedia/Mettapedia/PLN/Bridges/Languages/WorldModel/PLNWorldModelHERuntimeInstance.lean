import Mettapedia.PLN.Bridges.Languages.WorldModel.PLNWorldModelHERuntimeBridge

/-!
# First Concrete HE Runtime-to-WM Instance

Provides the first concrete inhabitant of `HEJudgmentWMInterface`:
given any encoding `encode : Pattern → Query` and any `BinaryWorldModel` instance,
the bridge holds under the side condition that authored HE language steps
are strength-monotone.

The side condition `HEStepMonotone` cleanly separates:
- "the bridge shape works" (proven here, sorry-free)
- "a specific WM satisfies monotonicity" (future theorem, separate file)
-/

namespace Mettapedia.PLN.Bridges.Languages.WorldModel.PLNWorldModelHERuntimeInstance

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.Bridges.Languages.WorldModel.PLNWorldModelRuntimeBridge
open Mettapedia.PLN.Bridges.Languages.WorldModel.PLNWorldModelHERuntimeBridge
open Mettapedia.Languages.MeTTa.RuntimeSpec
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Concrete pointwise interpretation

The first honest HE interpretation also uses runtime patterns as queries and a
pointwise evidence assignment as the WM state.

Positive example:
- a state can score the reduced return-state higher than its predecessor.

Negative example:
- this does not yet identify HE runtime semantics with PureKernel reduction.
-/

/-- Pointwise runtime WM state for HE queries. -/
abbrev HERuntimeEvidenceState := Pattern → BinaryEvidence

/-- Flat HE runtime WM state: every runtime pattern receives the same evidence.

Positive example:
- this gives an honest concrete WM interpretation instance whose monotonicity is
  provable for every HE runtime step.

Negative example:
- it is a baseline interpretation, not yet an action-sensitive predictor. -/
def flatHERuntimeEvidenceState (e : BinaryEvidence) : HERuntimeEvidenceState :=
  fun _ => e

noncomputable instance : EvidenceType HERuntimeEvidenceState where
  toAddCommMonoid := inferInstance

instance : BinaryWorldModel HERuntimeEvidenceState Pattern where
  evidence W q := W q
  evidence_add _ _ _ := rfl
  evidence_zero _ := rfl

@[simp] theorem he_pointwise_queryStrength
    (W : HERuntimeEvidenceState) (p : Pattern) :
    BinaryWorldModel.queryStrength (State := HERuntimeEvidenceState) (Query := Pattern) W p =
      BinaryEvidence.toStrength (W p) := rfl

/-! ## Monotonicity Predicates -/

/-- A world model state satisfies step-monotonicity for HE when every authored
    `HELanguageStep` does not decrease query strength.

    This is the specification target for future WM-specific verification. -/
def HEStepMonotone
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query]
    (encode : Pattern → Query) (W : State) : Prop :=
  ∀ {p q : Pattern}, HELanguageStep p q →
    BinaryWorldModel.queryStrength (State := State) (Query := Query) W (encode p) ≤
      BinaryWorldModel.queryStrength (State := State) (Query := Query) W (encode q)

/-- Concrete monotonicity side condition for the pointwise HE runtime WM state. -/
def HEPointwiseStepMonotone (W : HERuntimeEvidenceState) : Prop :=
  ∀ {p q : Pattern}, HELanguageStep p q →
    BinaryWorldModel.queryStrength (State := HERuntimeEvidenceState) (Query := Pattern) W p ≤
      BinaryWorldModel.queryStrength (State := HERuntimeEvidenceState) (Query := Pattern) W q

/-- The flat pointwise HE WM state is monotone for every runtime step.

This is the first fully concrete interpretation-side theorem:
- runtime relation is fixed
- WM carrier is fixed
- monotonicity is proved without extra assumptions

It is intentionally simple; richer interpretations should refine it later. -/
theorem flatHEPointwiseStepMonotone (e : BinaryEvidence) :
    HEPointwiseStepMonotone (flatHERuntimeEvidenceState e) := by
  intro p q _hstep
  simp [flatHERuntimeEvidenceState, he_pointwise_queryStrength]

/-! ## Concrete Instance -/

/-- First concrete `HEJudgmentWMInterface` inhabitant.

    For any encoding function and any BinaryWorldModel, the interface is satisfied
    under the `HEStepMonotone` side condition. -/
def heWMInterface
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query]
    (encode : Pattern → Query) :
    HEJudgmentWMInterface State Query where
  encode := encode
  side := HEStepMonotone State Query encode
  step_sound := fun hW hstep => hW hstep

/-- First concrete HE runtime-to-WM interpretation instance. -/
def hePointwiseWMInterface :
    HEJudgmentWMInterface HERuntimeEvidenceState Pattern where
  encode := id
  side := HEPointwiseStepMonotone
  step_sound := fun hW hstep => hW hstep

/-- The flat HE runtime WM state yields a concrete star-closure WM obligation. -/
theorem flatHePointwiseStepStar_wmStrength
    {e : BinaryEvidence} {p q : Pattern}
    (hstar : HELanguageStepStar p q) :
    WMStrengthObligation HERuntimeEvidenceState Pattern
      (flatHERuntimeEvidenceState e) p q :=
  hePointwiseWMInterface.toRuntimeJudgmentWMInterface.stepStar_sound
    (flatHEPointwiseStepMonotone e) hstar

@[simp] theorem heWMInterface_encode
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {encode : Pattern → Query} :
    (heWMInterface State Query encode).encode = encode := rfl

@[simp] theorem heWMInterface_side
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {encode : Pattern → Query} :
    (heWMInterface State Query encode).side =
      HEStepMonotone State Query encode := rfl

/-! ## Transport Theorems -/

/-- Star closure of HE steps transports to WM strength inequality
    under the step-monotonicity side condition. -/
theorem heStepStar_wmStrength
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {encode : Pattern → Query}
    {W : State} {p q : Pattern}
    (hW : HEStepMonotone State Query encode W)
    (hstar : HELanguageStepStar p q) :
    WMStrengthObligation State Query W (encode p) (encode q) :=
  (heWMInterface State Query encode).toRuntimeJudgmentWMInterface.stepStar_sound hW hstar

/-- Star closure transport for the concrete pointwise HE interpretation. -/
theorem hePointwiseStepStar_wmStrength
    {W : HERuntimeEvidenceState} {p q : Pattern}
    (hW : HEPointwiseStepMonotone W)
    (hstar : HELanguageStepStar p q) :
    WMStrengthObligation HERuntimeEvidenceState Pattern W p q :=
  hePointwiseWMInterface.toRuntimeJudgmentWMInterface.stepStar_sound hW hstar

/-- A single HE step yields a WM consequence rule under step-monotonicity. -/
def heStep_wmConsequenceRule
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {encode : Pattern → Query}
    {p q : Pattern} (hstep : HELanguageStep p q) :
    WMConsequenceRuleOn State Query :=
  (heWMInterface State Query encode).toRuntimeJudgmentWMInterface.wmConsequenceRuleOn_of_step
    hstep

/-- A single HE step yields a WM consequence rule in the concrete pointwise
interpretation. -/
noncomputable def hePointwiseStep_wmConsequenceRule
    {p q : Pattern} (hstep : HELanguageStep p q) :
    WMConsequenceRuleOn HERuntimeEvidenceState Pattern :=
  hePointwiseWMInterface.toRuntimeJudgmentWMInterface.wmConsequenceRuleOn_of_step hstep

end Mettapedia.PLN.Bridges.Languages.WorldModel.PLNWorldModelHERuntimeInstance
