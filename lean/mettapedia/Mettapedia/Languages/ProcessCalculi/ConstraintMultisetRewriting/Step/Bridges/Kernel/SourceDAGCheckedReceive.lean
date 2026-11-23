import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CheckedRequestIngress

/-! Numbered-source reception with one checked inference result reused.
The complete parser is proved equal to SourceDAGReceive.receiveEvent. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceDAGCheckedReceive

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open DefinitionAdapters SignatureFormation ProofExecution ExportReplay SourceDAGReceive

def receiveEvent (source : Json) : Read Unit :=
  NumberedReplay.receiveEvent SourceDAGReceive.termReader SourceDAGReceive.registry true .registered
    CheckedRequestIngress.finish source

def start (input : Input) : Reading where
  input := input
  types := Array.replicate input.types.size none
  terms := Array.replicate input.terms.size none
  registered := SourceProfile.primitiveBasis.received
  symbols := SourceProfile.primitiveBasis.symbols
  history := ExportReceiptHistory.empty_history SourceProfile.primitiveContext SourceProfileModels.policy

theorem registered_history (reading : Reading) :
    Registered.replayFrom SourceProfileModels.policy (Registered.empty SourceProfile.primitiveContext)
      (reading.registered.receipts.toList.map ExportReplay.Event.command) = some reading.registered.registered :=
  ExportReceiptHistory.registered_history SourceProfile.primitiveContext SourceProfileModels.policy
    reading.registered reading.history

/-- Reusing the checked inference output changes nothing observable: `finish` is
`originalFinish`, the ordinary completion for the shared receiver. -/
theorem receiveEvent_eq (source : Json) :
    receiveEvent source = SourceDAGReceive.receiveEvent source := by
  have same : CheckedRequestIngress.finish =
      NumberedReplay.finish SourceDAGReceive.termReader SourceDAGReceive.registry .registered := by
    funext request rule serial inputs parents outputs origin witnesses
    exact CheckedRequestIngress.finish_eq request rule serial inputs parents outputs origin witnesses
  unfold receiveEvent SourceDAGReceive.receiveEvent
  rw [same]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceDAGCheckedReceive
