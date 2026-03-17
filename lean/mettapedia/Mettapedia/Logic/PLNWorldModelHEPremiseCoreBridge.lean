import Mettapedia.Languages.MeTTa.HE.CoreFragment
import Mettapedia.Logic.PLNWorldModelRuntimeBridge

/-!
# HE Premise-Core Fragment -> WM Bridge

Composes the first explicit premise-bearing `HE` runtime fragment through the
existing runtime-to-WM consequence surface.

This bridge deliberately does not reuse `HEJudgmentWMInterface`, because that
interface is tied to the older `DeclReducesRel mettaHE` surface.  The premise
fragment lives on the honest `DeclReducesWithPremises` surface instead.

Positive example:
- a premise-bearing top-level HE rule can already be packaged as a
  `WMConsequenceRuleOn` once a WM interpretation for that fragment is fixed.

Negative example:
- this is not yet a guarded-source execution theorem
- this does not identify premise-bearing HE reduction with PureKernel `A/B/C1`
-/

namespace Mettapedia.Logic.PLNWorldModelHEPremiseCoreBridge

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelRuntimeBridge
open Mettapedia.Languages.MeTTa.HE.CoreFragment
open Mettapedia.Languages.MeTTa.RuntimeSpec
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises

/-- WM interface for the first premise-bearing HE runtime fragment. -/
structure HEPremiseCoreWMInterface
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query]
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) where
  encode : Pattern → Query
  side : State → Prop := fun _ => True
  step_sound :
    ∀ {W : State} {p q : Pattern},
      side W →
      HEPremiseCoreStep relEnv p q →
      WMStrengthObligation State Query W (encode p) (encode q)

namespace HEPremiseCoreWMInterface

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]
variable {relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv}

/-- Forget the HE premise-core wrapper back to the generic runtime WM interface. -/
def toRuntimeJudgmentWMInterface
    (I : HEPremiseCoreWMInterface State Query relEnv) :
    RuntimeJudgmentWMInterface State Query Pattern (HEPremiseCoreStep relEnv) where
  spec := heRuntimeSpec
  encode := I.encode
  side := I.side
  step_sound := I.step_sound

@[simp] theorem toRuntimeJudgmentWMInterface_spec
    (I : HEPremiseCoreWMInterface State Query relEnv) :
    I.toRuntimeJudgmentWMInterface.spec = heRuntimeSpec := rfl

@[simp] theorem toRuntimeJudgmentWMInterface_encode
    (I : HEPremiseCoreWMInterface State Query relEnv) :
    I.toRuntimeJudgmentWMInterface.encode = I.encode := rfl

@[simp] theorem toRuntimeJudgmentWMInterface_side
    (I : HEPremiseCoreWMInterface State Query relEnv) :
    I.toRuntimeJudgmentWMInterface.side = I.side := rfl

/-- Any premise-core HE step transports to a WM strength obligation once a
fragment interpretation interface is fixed. -/
theorem hePremiseCoreStep_to_wmStrengthObligation
    (I : HEPremiseCoreWMInterface State Query relEnv)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstep : HEPremiseCoreStep relEnv p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) :=
  I.step_sound hW hstep

/-- Star closure in the HE premise-core fragment transports to WM inequalities
by transitivity. -/
theorem hePremiseCoreStepStar_to_wmStrengthObligation
    (I : HEPremiseCoreWMInterface State Query relEnv)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstar : HEPremiseCoreStepStar relEnv p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) :=
  RuntimeJudgmentWMInterface.stepStar_sound I.toRuntimeJudgmentWMInterface hW hstar

/-- Package one premise-core HE step as a WM consequence rule. -/
def wmConsequenceRuleOn_of_hePremiseCoreStep
    (I : HEPremiseCoreWMInterface State Query relEnv)
    {p q : Pattern}
    (hstep : HEPremiseCoreStep relEnv p q) :
    WMConsequenceRuleOn State Query :=
  RuntimeJudgmentWMInterface.wmConsequenceRuleOn_of_step
    I.toRuntimeJudgmentWMInterface hstep

/-- Package premise-core HE star closure as a WM consequence rule. -/
def wmConsequenceRuleOn_of_hePremiseCoreStepStar
    (I : HEPremiseCoreWMInterface State Query relEnv)
    {p q : Pattern}
    (hstar : HEPremiseCoreStepStar relEnv p q) :
    WMConsequenceRuleOn State Query :=
  RuntimeJudgmentWMInterface.wmConsequenceRuleOn_of_stepStar
    I.toRuntimeJudgmentWMInterface hstar

end HEPremiseCoreWMInterface

end Mettapedia.Logic.PLNWorldModelHEPremiseCoreBridge
