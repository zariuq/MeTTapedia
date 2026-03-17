import Mettapedia.Logic.PLNWorldModelPeTTaRuntimeBridge

/-!
# First Concrete PeTTa Runtime-to-WM Instance

Provides the first concrete inhabitant of `PeTTaJudgmentWMInterface`:
given any encoding `encode : Pattern → Query` and any `BinaryWorldModel` instance,
the bridge holds under the side condition that evaluation steps are
strength-monotone.

The side condition `PeTTaStepMonotone` cleanly separates:
- "the bridge shape works" (proven here, sorry-free)
- "a specific WM satisfies monotonicity" (future theorem, separate file)
-/

namespace Mettapedia.Logic.PLNWorldModelPeTTaRuntimeInstance

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelRuntimeBridge
open Mettapedia.Logic.PLNWorldModelPeTTaRuntimeBridge
open Mettapedia.Languages.MeTTa.RuntimeSpec
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## Concrete pointwise interpretation

The first honest interpretation instance uses runtime configurations themselves
as queries, with a WM state given by a pointwise evidence assignment.

Positive example:
- a state can assign stronger evidence to a rewritten configuration than to
  its predecessor.

Negative example:
- this does not yet claim that every PeTTa runtime induces such a state
  canonically; it only packages the first concrete WM landing zone.
-/

/-- Pointwise runtime WM state: each configuration carries explicit evidence. -/
abbrev PeTTaRuntimeEvidenceState := Pattern → BinaryEvidence

/-- Flat PeTTa runtime WM state: every runtime pattern receives the same evidence.

Positive example:
- this gives an honest concrete WM interpretation instance whose monotonicity is
  provable for every PeTTa runtime step.

Negative example:
- it is a baseline interpretation, not yet a semantics of PeTTa prediction. -/
def flatPeTTaRuntimeEvidenceState (e : BinaryEvidence) : PeTTaRuntimeEvidenceState :=
  fun _ => e

noncomputable instance : EvidenceType PeTTaRuntimeEvidenceState where
  toAddCommMonoid := inferInstance

instance : BinaryWorldModel PeTTaRuntimeEvidenceState Pattern where
  evidence W q := W q
  evidence_add _ _ _ := rfl

@[simp] theorem pointwise_queryStrength
    (W : PeTTaRuntimeEvidenceState) (p : Pattern) :
    BinaryWorldModel.queryStrength (State := PeTTaRuntimeEvidenceState) (Query := Pattern) W p =
      BinaryEvidence.toStrength (W p) := rfl

/-! ## Monotonicity Predicates -/

/-- A world model state satisfies step-monotonicity for a given PeTTa space and
    encoding when every `MeTTaStep` does not decrease query strength.

    This is the specification target for future WM-specific verification. -/
def PeTTaStepMonotone
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query]
    (s : PeTTaSpace) (encode : Pattern → Query) (W : State) : Prop :=
  ∀ {p q : Pattern}, MeTTaStep s p q →
    BinaryWorldModel.queryStrength (State := State) (Query := Query) W (encode p) ≤
      BinaryWorldModel.queryStrength (State := State) (Query := Query) W (encode q)

/-- Sufficient condition restricted to the `evalStep` constructor:
    rule application is strength-monotone. This is the core case since
    evalStep (and evalcStep) are the only constructors that use space rules. -/
def PeTTaEvalStepMonotone
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query]
    (s : PeTTaSpace) (encode : Pattern → Query) (W : State) : Prop :=
  ∀ (r : RewriteRule) (bs : Bindings) (p q : Pattern),
    r ∈ s.rules → r.premises = [] →
    bs ∈ matchPattern r.left p → applyBindings bs r.right = q →
    BinaryWorldModel.queryStrength (State := State) (Query := Query) W
      (encode (.apply "eval" [p])) ≤
      BinaryWorldModel.queryStrength (State := State) (Query := Query) W (encode q)

/-- Concrete monotonicity side condition for the pointwise runtime WM state. -/
def PeTTaPointwiseStepMonotone (s : PeTTaSpace) (W : PeTTaRuntimeEvidenceState) : Prop :=
  ∀ {p q : Pattern}, MeTTaStep s p q →
    BinaryWorldModel.queryStrength (State := PeTTaRuntimeEvidenceState) (Query := Pattern) W p ≤
      BinaryWorldModel.queryStrength (State := PeTTaRuntimeEvidenceState) (Query := Pattern) W q

/-- The flat pointwise PeTTa WM state is monotone for every runtime step. -/
theorem flatPeTTaPointwiseStepMonotone
    (s : PeTTaSpace) (e : BinaryEvidence) :
    PeTTaPointwiseStepMonotone s (flatPeTTaRuntimeEvidenceState e) := by
  intro p q _hstep
  simp [flatPeTTaRuntimeEvidenceState, pointwise_queryStrength]

/-! ## Concrete Instance -/

/-- First concrete `PeTTaJudgmentWMInterface` inhabitant.

    For any encoding function and any BinaryWorldModel, the interface is satisfied
    under the `PeTTaStepMonotone` side condition. The proof of `step_sound`
    is trivial: it directly applies the side condition. -/
def pettaWMInterface
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query]
    (s : PeTTaSpace) (encode : Pattern → Query) :
    PeTTaJudgmentWMInterface State Query s where
  encode := encode
  side := PeTTaStepMonotone State Query s encode
  step_sound := fun hW hstep => hW hstep

/-- First concrete PeTTa runtime-to-WM interpretation instance.

Queries are runtime patterns themselves, and the world-model state stores
pointwise evidence over those patterns. -/
def pettaPointwiseWMInterface
    (s : PeTTaSpace) :
    PeTTaJudgmentWMInterface PeTTaRuntimeEvidenceState Pattern s where
  encode := id
  side := PeTTaPointwiseStepMonotone s
  step_sound := fun hW hstep => hW hstep

/-- The flat PeTTa runtime WM state yields a concrete star-closure WM obligation. -/
theorem flatPeTTaPointwiseStepStar_wmStrength
    {s : PeTTaSpace} {e : BinaryEvidence} {p q : Pattern}
    (hstar : Relation.ReflTransGen (MeTTaStep s) p q) :
    WMStrengthObligation PeTTaRuntimeEvidenceState Pattern
      (flatPeTTaRuntimeEvidenceState e) p q :=
  (pettaPointwiseWMInterface s).toRuntimeJudgmentWMInterface.stepStar_sound
    (flatPeTTaPointwiseStepMonotone s e) hstar

@[simp] theorem pettaWMInterface_encode
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {s : PeTTaSpace} {encode : Pattern → Query} :
    (pettaWMInterface State Query s encode).encode = encode := rfl

@[simp] theorem pettaWMInterface_side
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {s : PeTTaSpace} {encode : Pattern → Query} :
    (pettaWMInterface State Query s encode).side =
      PeTTaStepMonotone State Query s encode := rfl

/-! ## Transport Theorems -/

/-- Star closure of PeTTa steps transports to WM strength inequality
    under the step-monotonicity side condition. -/
theorem pettaStepStar_wmStrength
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {s : PeTTaSpace} {encode : Pattern → Query}
    {W : State} {p q : Pattern}
    (hW : PeTTaStepMonotone State Query s encode W)
    (hstar : Relation.ReflTransGen (MeTTaStep s) p q) :
    WMStrengthObligation State Query W (encode p) (encode q) :=
  (pettaWMInterface State Query s encode).toRuntimeJudgmentWMInterface.stepStar_sound hW hstar

/-- Star closure transport for the concrete pointwise interpretation. -/
theorem pettaPointwiseStepStar_wmStrength
    {s : PeTTaSpace}
    {W : PeTTaRuntimeEvidenceState} {p q : Pattern}
    (hW : PeTTaPointwiseStepMonotone s W)
    (hstar : Relation.ReflTransGen (MeTTaStep s) p q) :
    WMStrengthObligation PeTTaRuntimeEvidenceState Pattern W p q :=
  (pettaPointwiseWMInterface s).toRuntimeJudgmentWMInterface.stepStar_sound hW hstar

/-- A single PeTTa step yields a WM consequence rule under step-monotonicity. -/
def pettaStep_wmConsequenceRule
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {s : PeTTaSpace} {encode : Pattern → Query}
    {p q : Pattern} (hstep : MeTTaStep s p q) :
    WMConsequenceRuleOn State Query :=
  (pettaWMInterface State Query s encode).toRuntimeJudgmentWMInterface.wmConsequenceRuleOn_of_step
    hstep

/-- A single PeTTa step yields a WM consequence rule in the concrete
pointwise interpretation. -/
def pettaPointwiseStep_wmConsequenceRule
    {s : PeTTaSpace} {p q : Pattern} (hstep : MeTTaStep s p q) :
    WMConsequenceRuleOn PeTTaRuntimeEvidenceState Pattern :=
  (pettaPointwiseWMInterface s).toRuntimeJudgmentWMInterface.wmConsequenceRuleOn_of_step hstep

end Mettapedia.Logic.PLNWorldModelPeTTaRuntimeInstance
