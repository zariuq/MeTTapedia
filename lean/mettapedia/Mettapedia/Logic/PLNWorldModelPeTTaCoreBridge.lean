import Mettapedia.Languages.MeTTa.PeTTa.CoreFragment
import Mettapedia.Logic.PLNWorldModelPeTTaRuntimeBridge

/-!
# PeTTa Core Fragment -> WM Bridge

Composes the first explicit `PeTTaCore` runtime fragment through the existing
runtime-to-WM consequence surface.

This is deliberately a composition result:
- `PeTTaCoreStep` is a smaller runtime fragment
- `PeTTaJudgmentWMInterface` is unchanged
- the fragment lands on the existing WM-facing `C*` side by forgetting
  `PeTTaCoreStep` to `MeTTaStep`

Positive example:
- a core-fragment `evalStep` yields a `WMConsequenceRuleOn`.

Negative example:
- this is not a claim that PeTTa runtime reduces to PureKernel `A` or `B`.
-/

namespace Mettapedia.Logic.PLNWorldModelPeTTaCoreBridge

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelRuntimeBridge
open Mettapedia.Logic.PLNWorldModelPeTTaRuntimeBridge
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.CoreFragment
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Any PeTTa core step transports to a WM strength obligation once a PeTTa
runtime interpretation interface is fixed. -/
theorem pettaCoreStep_to_wmStrengthObligation
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {s : PeTTaSpace}
    (I : PeTTaJudgmentWMInterface State Query s)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstep : PeTTaCoreStep s p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) :=
  PeTTaJudgmentWMInterface.mettaStep_to_wmStrengthObligation
    I hW (toMeTTaStep hstep)

/-- Any star closure in the PeTTa core fragment transports to a WM strength
obligation once a PeTTa runtime interpretation interface is fixed. -/
theorem pettaCoreStepStar_to_wmStrengthObligation
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {s : PeTTaSpace}
    (I : PeTTaJudgmentWMInterface State Query s)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstar : PeTTaCoreStepStar s p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) :=
  PeTTaJudgmentWMInterface.mettaStepStar_to_wmStrengthObligation
    I hW (toMeTTaStepStar hstar)

/-- Package one PeTTa core step as a WM consequence rule via the existing
runtime-to-WM bridge. -/
def wmConsequenceRuleOn_of_pettaCoreStep
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {s : PeTTaSpace}
    (I : PeTTaJudgmentWMInterface State Query s)
    {p q : Pattern}
    (hstep : PeTTaCoreStep s p q) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_mettaStep (toMeTTaStep hstep)

/-- Package PeTTa core star closure as a WM consequence rule via the existing
runtime-to-WM bridge. -/
def wmConsequenceRuleOn_of_pettaCoreStepStar
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {s : PeTTaSpace}
    (I : PeTTaJudgmentWMInterface State Query s)
    {p q : Pattern}
    (hstar : PeTTaCoreStepStar s p q) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_mettaStepStar (toMeTTaStepStar hstar)

end Mettapedia.Logic.PLNWorldModelPeTTaCoreBridge
