import Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment
import Mettapedia.Logic.PLNWorldModelRuntimeBridge

/-!
# PeTTa Space Core Fragment -> WM Bridge

Composes the first explicit PeTTa atomspace/query fragment through the existing
runtime-to-WM consequence surface.

This sits alongside the rule-firing PeTTa core bridge:
- `PeTTaCoreStep` covers top-level rule-application runtime steps
- `PeTTaSpaceCoreQuery` covers atomspace/query features such as
  `(match &self ...)` and `(get-atoms &self)`

Positive example:
- a packaged `(match &self $x tmpl)` or `(get-atoms &self)` query can now be
  turned into a `WMConsequenceRuleOn`.

Negative example:
- this does not claim that atomspace queries are rewrite firings.
- this does not add `new-space`, which is not yet formalized in the Lean PeTTa stack.
-/

namespace Mettapedia.Logic.PLNWorldModelPeTTaSpaceCoreBridge

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelRuntimeBridge
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- First WM-facing interface for the packaged PeTTa atomspace/query fragment. -/
abbrev PeTTaSpaceCoreWMInterface
    (State Query : Type*)
    [EvidenceType State] [BinaryWorldModel State Query]
    (s : PeTTaSpace) :=
  RuntimeJudgmentWMInterface State Query Pattern (PeTTaSpaceCoreQuery s)

/-- Any packaged PeTTa atomspace/query step transports to a WM strength
obligation once a WM interpretation interface is fixed. -/
theorem pettaSpaceCoreQuery_to_wmStrengthObligation
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {s : PeTTaSpace}
    (I : PeTTaSpaceCoreWMInterface State Query s)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hquery : PeTTaSpaceCoreQuery s p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) :=
  I.step_sound hW hquery

/-- Any star closure in the packaged PeTTa atomspace/query fragment transports
to a WM strength obligation once a WM interpretation interface is fixed. -/
theorem pettaSpaceCoreQueryStar_to_wmStrengthObligation
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {s : PeTTaSpace}
    (I : PeTTaSpaceCoreWMInterface State Query s)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstar : PeTTaSpaceCoreQueryStar s p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) :=
  RuntimeJudgmentWMInterface.stepStar_sound I hW hstar

/-- Package one PeTTa atomspace/query step as a WM consequence rule via the
existing runtime-to-WM bridge. -/
def wmConsequenceRuleOn_of_pettaSpaceCoreQuery
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {s : PeTTaSpace}
    (I : PeTTaSpaceCoreWMInterface State Query s)
    {p q : Pattern}
    (hquery : PeTTaSpaceCoreQuery s p q) :
    WMConsequenceRuleOn State Query :=
  RuntimeJudgmentWMInterface.wmConsequenceRuleOn_of_step I hquery

/-- Package star closure in the PeTTa atomspace/query fragment as a WM
consequence rule via the existing runtime-to-WM bridge. -/
def wmConsequenceRuleOn_of_pettaSpaceCoreQueryStar
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {s : PeTTaSpace}
    (I : PeTTaSpaceCoreWMInterface State Query s)
    {p q : Pattern}
    (hstar : PeTTaSpaceCoreQueryStar s p q) :
    WMConsequenceRuleOn State Query :=
  RuntimeJudgmentWMInterface.wmConsequenceRuleOn_of_stepStar I hstar

end Mettapedia.Logic.PLNWorldModelPeTTaSpaceCoreBridge
