import Mettapedia.Languages.MeTTa.HE.CoreFragment
import Mettapedia.Logic.PLNWorldModelHERuntimeBridge

/-!
# HE Core Fragment -> WM Bridge

Composes the first explicit `HECore` runtime fragment through the existing
runtime-to-WM consequence surface.

This is deliberately a composition result:
- `HECoreStep` is a smaller runtime fragment
- `HEJudgmentWMInterface` is unchanged
- the fragment lands on the existing WM-facing `C*` side by forgetting
  `HECoreStep` to `DeclReducesRel mettaHE`

Positive example:
- a core-fragment HE `topRule` yields a `WMConsequenceRuleOn`.

Negative example:
- this is not a claim that HE runtime reduces to PureKernel `A` or `B`.
-/

namespace Mettapedia.Logic.PLNWorldModelHECoreBridge

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelRuntimeBridge
open Mettapedia.Logic.PLNWorldModelHERuntimeBridge
open Mettapedia.Languages.MeTTa.HE.CoreFragment
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Any HE core step transports to a WM strength obligation once an HE
runtime interpretation interface is fixed. -/
theorem heCoreStep_to_wmStrengthObligation
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    (I : HEJudgmentWMInterface State Query)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstep : HECoreStep p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) :=
  HEJudgmentWMInterface.declReducesRel_to_wmStrengthObligation
    I hW (toDeclReducesRel hstep)

/-- Any star closure in the HE core fragment transports to a WM strength
obligation once an HE runtime interpretation interface is fixed. -/
theorem heCoreStepStar_to_wmStrengthObligation
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    (I : HEJudgmentWMInterface State Query)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstar : HECoreStepStar p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) :=
  HEJudgmentWMInterface.declReducesRelStar_to_wmStrengthObligation
    I hW (toDeclReducesRelStar hstar)

/-- Package one HE core step as a WM consequence rule via the existing
runtime-to-WM bridge. -/
def wmConsequenceRuleOn_of_heCoreStep
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    (I : HEJudgmentWMInterface State Query)
    {p q : Pattern}
    (hstep : HECoreStep p q) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_declReducesRel (toDeclReducesRel hstep)

/-- Package HE core star closure as a WM consequence rule via the existing
runtime-to-WM bridge. -/
def wmConsequenceRuleOn_of_heCoreStepStar
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    (I : HEJudgmentWMInterface State Query)
    {p q : Pattern}
    (hstar : HECoreStepStar p q) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_declReducesRelStar (toDeclReducesRelStar hstar)

end Mettapedia.Logic.PLNWorldModelHECoreBridge
