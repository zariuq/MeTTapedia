import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CheckedRequestReuse
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.SourceDAGReceive

/-!
# Checked inference reuse at the numbered-source ingress

This adapter changes only reuse of the already computed inference output.
The existing source parser, cached parent lookup, declaration context,
source conclusions and complete chronological history are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CheckedRequestIngress

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation SourceDAGReceive

/-- Reading the state passes it to the continuation both as the value read and as the state. -/
theorem get_bind_apply {A : Type} (next : Reading → Read A) (state : Reading) :
    ((get : Read Reading) >>= next) state = next state state := rfl

/-- Accept a source event whose inference was already checked: replay it with the checked output
instead of re-running the primitive check. -/
def accept {request : RuleRequest} (checked : CheckedRequestReuse.Checked SourceProfileModels.policy request)
    (parents sourceParents sourceIds : List Nat) (origin : Origin) (witnesses : InstanceWitnesses)
    (claims : List Sequent) (sources : List SourceTerm) : Read Unit := do
  let before ← get
  let sourceEvent := CheckedRequestReuse.event checked parents sourceParents sourceIds origin witnesses claims
  match checkedReplay : CheckedRequestReuse.apply checked before.registered parents sourceParents sourceIds
      origin witnesses claims with
  | none => fail "registered source event refused"
  | some after =>
      let accepted : ExportReplay.apply SourceProfileModels.policy before.registered sourceEvent = some after :=
        (CheckedRequestReuse.apply_eq checked before.registered parents sourceParents sourceIds origin witnesses claims).symm.trans checkedReplay
      modify fun _ => { before with
        registered := after
        history := ExportReceiptHistory.apply_history SourceProfile.primitiveContext
          SourceProfileModels.policy before.history accepted
        sourceConclusions := ExportCodec.addConclusions before.sourceConclusions sourceIds sources }

/-- Accepting a checked inference is the generic acceptance of the same source event: the reused
replay and the generic replay compute the same result (`CheckedRequestReuse.apply_eq`), so they
refuse together and otherwise install the same registered state, history and conclusions. -/
theorem accept_eq {request : RuleRequest} (checked : CheckedRequestReuse.Checked SourceProfileModels.policy request)
    (parents sourceParents sourceIds : List Nat) (origin : Origin) (witnesses : InstanceWitnesses)
    (claims : List Sequent) (sources : List SourceTerm) :
    accept checked parents sourceParents sourceIds origin witnesses claims sources =
      SourceDAGReceive.acceptEvent
        (CheckedRequestReuse.event checked parents sourceParents sourceIds origin witnesses claims) sources := by
  funext before
  have equivalent := CheckedRequestReuse.apply_eq checked before.registered parents sourceParents sourceIds
    origin witnesses claims
  simp only [accept, SourceDAGReceive.acceptEvent, get_bind_apply]
  refine congrFun ?_ before
  split <;> split
  · rfl
  · rename_i refused _ accepted
    exact absurd (refused.symm.trans (equivalent.trans accepted)) (by simp)
  · rename_i _ accepted refused
    exact absurd (accepted.symm.trans (equivalent.trans refused)) (by simp)
  · rename_i reused accepted generic replayed
    obtain rfl : reused = generic := Option.some.inj (accepted.symm.trans (equivalent.trans replayed))
    rfl

def originalFinish (request : RuleRequest) (rule : String) (serial : Nat)
    (inputs : List (Nat × Theorem)) (sourceParents : List Nat) (outputs : Array Json)
    (origin : Origin) (witnesses : InstanceWitnesses) : Read Unit := do
  let actual ← option (request.check SourceProfileModels.policy) s!"primitive check refused {rule} at {serial}"
  let claims ← outputs.toList.mapM claim
  let node : Receipt := ⟨actual,request,inputs.map (·.1),origin⟩
  let sourceEvent : ExportReplay.Event :=
    ⟨claims.map (·.1),sourceParents,.proof node witnesses,claims.map (·.2.1)⟩
  SourceDAGReceive.acceptEvent sourceEvent (claims.map (·.2.2))

def finish (request : RuleRequest) (rule : String) (serial : Nat)
    (inputs : List (Nat × Theorem)) (sourceParents : List Nat) (outputs : Array Json)
    (origin : Origin) (witnesses : InstanceWitnesses) : Read Unit := do
  match accepted : request.check SourceProfileModels.policy with
  | none => fail s!"primitive check refused {rule} at {serial}"
  | some actual =>
      let checked : CheckedRequestReuse.Checked SourceProfileModels.policy request := ⟨actual, accepted⟩
      let claims ← outputs.toList.mapM claim
      accept checked (inputs.map (·.1)) sourceParents (claims.map (·.1)) origin witnesses
        (claims.map (·.2.1)) (claims.map (·.2.2))

theorem finish_eq (request : RuleRequest) (rule : String) (serial : Nat)
    (inputs : List (Nat × Theorem)) (sourceParents : List Nat) (outputs : Array Json)
    (origin : Origin) (witnesses : InstanceWitnesses) :
    finish request rule serial inputs sourceParents outputs origin witnesses =
      originalFinish request rule serial inputs sourceParents outputs origin witnesses := by
  unfold finish originalFinish
  simp only [accept_eq, CheckedRequestReuse.event, CheckedRequestReuse.node]
  split
  · simp_all [option, fail]
    rfl
  · simp_all [option]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CheckedRequestIngress
