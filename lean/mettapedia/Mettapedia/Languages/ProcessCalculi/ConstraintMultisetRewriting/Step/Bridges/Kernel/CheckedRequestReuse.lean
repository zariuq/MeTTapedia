import Mettapedia.Languages.HOLLight.ExportReplay

/-!
# Reusing an already checked source inference

The source receiver computes a request's output before constructing its
graph node. The ordinary registered replay computes that same output again.
This adapter retains the first check as a certificate. It still checks the
actual ordered cached premises, current declaration formation, source IDs
and claimed outputs. Its result is equal to the unchanged registered replay.

The certificate is indexed by the actual axiom policy and request. It grants
no reusable declaration authority and carries no claim about running time.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CheckedRequestReuse

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation

structure Checked (policy : AxiomPolicy) [DecidablePred policy] (request : RuleRequest) where
  output : Theorem
  accepted : request.check policy = some output

def check? (policy : AxiomPolicy) [DecidablePred policy] (request : RuleRequest) :
    Option (Checked policy request) :=
  match accepted : request.check policy with
  | none => none
  | some output => some ⟨output, accepted⟩

theorem check?_output (policy : AxiomPolicy) [DecidablePred policy] (request : RuleRequest) :
    (check? policy request).map Checked.output = request.check policy := by
  unfold check?
  split <;> simp_all

def node {policy : AxiomPolicy} [DecidablePred policy] {request : RuleRequest}
    (checked : Checked policy request) (parents : List Nat) (origin : Origin) : Receipt :=
  ⟨checked.output, request, parents, origin⟩

def replay {policy : AxiomPolicy} [DecidablePred policy] {request : RuleRequest}
    (checked : Checked policy request) (cache : Array Theorem) (parents : List Nat) :
    Option (Array Theorem) := do
  let inputs ← DerivationGraph.lookupPremises cache parents
  if theoremListStructuralSame request.premises inputs then
    some (cache.push checked.output)
  else none

theorem replay_eq {policy : AxiomPolicy} [DecidablePred policy] {request : RuleRequest}
    (checked : Checked policy request) (cache : Array Theorem) (parents : List Nat) (origin : Origin) :
    replay checked cache parents = (node checked parents origin).replay (ruleWitness policy) cache := by
  simp [replay, node, DerivationGraph.Node.replay, ruleWitness, RuleRequest.isInstance,
    RuleRequest.outputSameB, checked.accepted]

def commandCheck {policy : AxiomPolicy} [DecidablePred policy] {request : RuleRequest}
    (checked : Checked policy request) (context : TheoryContext) (cache : Array Theorem)
    (parents : List Nat) (witnesses : InstanceWitnesses) : Option Registered.Output := do
  let _ ← replay checked cache parents
  if Registered.requestFormedB context.signature witnesses request = true ∧
      theoremFormedB context.signature witnesses checked.output = true then
    pure ⟨context, [checked.output]⟩
  else none

theorem commandCheck_eq {policy : AxiomPolicy} [DecidablePred policy] {request : RuleRequest}
    (checked : Checked policy request) (context : TheoryContext) (cache : Array Theorem)
    (parents : List Nat) (origin : Origin) (witnesses : InstanceWitnesses) :
    commandCheck checked context cache parents witnesses =
      (Registered.Command.proof (node checked parents origin) witnesses).check policy context cache := by
  unfold commandCheck Registered.Command.check
  rw [replay_eq checked cache parents origin]
  rfl

def event {policy : AxiomPolicy} [DecidablePred policy] {request : RuleRequest}
    (checked : Checked policy request) (parents sourceParents sourceIds : List Nat)
    (origin : Origin) (witnesses : InstanceWitnesses) (claims : List Sequent) : ExportReplay.Event :=
  ⟨sourceIds, sourceParents, .proof (node checked parents origin) witnesses, claims⟩

def apply {policy : AxiomPolicy} [DecidablePred policy] {request : RuleRequest}
    (checked : Checked policy request) (before : ExportReplay.State)
    (parents sourceParents sourceIds : List Nat) (origin : Origin)
    (witnesses : InstanceWitnesses) (claims : List Sequent) : Option ExportReplay.State := do
  let resolved ← ExportReplay.resolveParents before sourceParents
  if resolved ≠ parents ∨ ExportReplay.idsFreshB before sourceIds ≠ true then none
  else do
    let output ← commandCheck checked before.registered.context before.registered.cache parents witnesses
    if sourceIds.length ≠ output.theorems.length ∨
        ExportReplay.claimsSame claims output.theorems ≠ true then none
    else
      let sourceEvent := event checked parents sourceParents sourceIds origin witnesses claims
      let after : Registered.State :=
        ⟨output.context, before.registered.cache ++ output.theorems.toArray,
          before.registered.receipts.push ⟨sourceEvent.command, output.theorems⟩⟩
      pure ⟨after, ExportReplay.addAddresses before.addresses before.registered.cache.size sourceIds,
        before.receipts.push sourceEvent⟩

theorem apply_eq {policy : AxiomPolicy} [DecidablePred policy] {request : RuleRequest}
    (checked : Checked policy request) (before : ExportReplay.State)
    (parents sourceParents sourceIds : List Nat) (origin : Origin)
    (witnesses : InstanceWitnesses) (claims : List Sequent) :
    apply checked before parents sourceParents sourceIds origin witnesses claims =
      ExportReplay.apply policy before (event checked parents sourceParents sourceIds origin witnesses claims) := by
  unfold apply ExportReplay.apply
  rw [commandCheck_eq checked before.registered.context before.registered.cache parents origin witnesses]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CheckedRequestReuse
