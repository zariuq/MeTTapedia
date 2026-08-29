import Mettapedia.GSLT.Core.HeterogeneousHeapDispatch
import Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem

open Mettapedia.GSLT.LanguageDef

/-!
# Source compressed-heap bridge

The authored compressed Metamath machine has one heterogeneous heap: proof
node identities and assertion schemas occupy the same indexed sequence.  This
module forgets assertion contents but never their positions, then projects the
source proof-lookup and save branches into the reusable occurrence-heap GSLT.

This is a semantic projection, not decompression.  Proof actions remain
dynamic, and assertion entries remain opaque occupants of the shared heap.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapSourceBridge

open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceInferenceProjection

/-- Forget an assertion schema's contents while preserving its heap position;
retain a proof entry as an occurrence carrying its exact node identity. -/
def sourceHeapEntry {source : SourcePrefix} :
    SourceGSLTCompressedTheorem.HeapEntry source →
      Entry Nat Unit SourceAssertion
  | .proof nodeId => .occurrence ⟨nodeId, ()⟩
  | .assertion assertion => .opaque assertion

/-- Heterogeneous source heap represented in the reusable protocol. -/
def sourceHeap {source : SourcePrefix}
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source)) :
    List (Entry Nat Unit SourceAssertion) :=
  heap.map sourceHeapEntry

@[simp] theorem sourceHeap_length {source : SourcePrefix}
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source)) :
    (sourceHeap heap).length = heap.length := by
  simp [sourceHeap]

@[simp] theorem sourceHeap_append_proof {source : SourcePrefix}
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (nodeId : Nat) :
    sourceHeap (heap ++ [.proof nodeId]) =
      sourceHeap heap ++ [.occurrence ⟨nodeId, ()⟩] := by
  simp [sourceHeap, sourceHeapEntry]

@[simp] theorem sourceHeap_append_assertion {source : SourcePrefix}
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (assertion : SourceAssertion) :
    sourceHeap (heap ++ [.assertion assertion]) =
      sourceHeap heap ++ [.opaque assertion] := by
  simp [sourceHeap, sourceHeapEntry]

/-- A source proof-heap lookup becomes the exact occurrence lookup at the same
heterogeneous index. -/
theorem sourceHeap_get_proof {source : SourcePrefix}
    {heap : List (SourceGSLTCompressedTheorem.HeapEntry source)}
    {index nodeId : Nat}
    (found : heap[index]? = some (.proof nodeId)) :
    GetElem?.getElem? (sourceHeap heap) index =
      some (Entry.occurrence ⟨nodeId, ()⟩) := by
  simpa [sourceHeap, sourceHeapEntry, List.getElem?_map] using
    congrArg (Option.map sourceHeapEntry) found

/-- A source assertion entry becomes an opaque occupant of the exact same
heap position. -/
theorem sourceHeap_get_assertion {source : SourcePrefix}
    {heap : List (SourceGSLTCompressedTheorem.HeapEntry source)}
    {index : Nat} {assertion : SourceAssertion}
    (found : heap[index]? = some (.assertion assertion)) :
    GetElem?.getElem? (sourceHeap heap) index =
      some (Entry.opaque assertion) := by
  simpa [sourceHeap, sourceHeapEntry, List.getElem?_map] using
    congrArg (Option.map sourceHeapEntry) found

/-- Project exactly the proof branch of a source compressed step.  Assertion
application returns `none`: it is handled by the assertion machine rather than
being misclassified as a proof occurrence. -/
def proofHeapNodeId?
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target} {index : Nat}
    (step : ActionStep before (.step index) after) :
    Option Nat := by
  cases step with
  | proof index nodeId node heapLookup nodeLookup =>
      exact some nodeId
  | assertion => exact none

/-- Positive control: a source proof constructor projects to a protocol step
carrying the same node identity. -/
theorem proof_constructor_projects
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target) (index nodeId : Nat)
    (node : ProofNode source target)
    (heapLookup : before.heap[index]? = some (.proof nodeId))
    (nodeLookup : before.nodes[nodeId]? = some node) :
    proofHeapNodeId?
        (ActionStep.proof before index nodeId node heapLookup nodeLookup) =
        some nodeId ∧
      Step
        ⟨(), sourceHeap before.heap, .lookup () index⟩
        ⟨(), sourceHeap before.heap,
          .holding () index ⟨nodeId, ()⟩⟩ := by
  exact ⟨rfl, Step.lookupHit () (sourceHeap before.heap) index
    ⟨nodeId, ()⟩ (sourceHeap_get_proof heapLookup)⟩

/-- Negative control: an assertion application never projects as a proof-heap
lookup, even though it uses the same numeric heap index. -/
theorem assertion_constructor_does_not_project_as_proof
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target) (index : Nat)
    (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (children : SourceGeneratedProvesForest source target actuals)
    (heapLookup : before.heap[index]? = some (.assertion assertion))
    (member : assertion ∈ source.assertions)
    (stack_eq : before.stack = retained ++ parents)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (resolved : ResolvesForest before.nodes parents actuals children) :
    proofHeapNodeId?
      (ActionStep.assertion before index assertion retained parents children
        heapLookup member stack_eq node resolved) = none := by
  rfl

/-- The same authored assertion constructor positively dispatches through the
opaque branch.  It is excluded only from the proof channel, not from the
heterogeneous heap machine. -/
theorem assertion_constructor_dispatches_as_opaque
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target) (index : Nat)
    (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (children : SourceGeneratedProvesForest source target actuals)
    (heapLookup : before.heap[index]? = some (.assertion assertion))
    (member : assertion ∈ source.assertions)
    (stack_eq : before.stack = retained ++ parents)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (resolved : ResolvesForest before.nodes parents actuals children) :
    proofHeapNodeId?
        (ActionStep.assertion before index assertion retained parents children
          heapLookup member stack_eq node resolved) = none ∧
      Mettapedia.GSLT.HeterogeneousHeapDispatch.Step
        ⟨(), sourceHeap before.heap,
          .lookup () index⟩
        ⟨(), sourceHeap before.heap,
          .foundOpaque () index assertion⟩ := by
  constructor
  · rfl
  · exact Mettapedia.GSLT.HeterogeneousHeapDispatch.Step.opaque
      () (sourceHeap before.heap) index assertion
      (sourceHeap_get_assertion heapLookup)

/-- Every authored `Z` step projects to the protocol's fresh save, retaining
the source node identity and exact heterogeneous heap length. -/
theorem save_projects_exactly
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target}
    (step : ActionStep before .save after) :
    ∃ nodeId node,
      before.stack.getLast? = some nodeId ∧
      before.nodes[nodeId]? = some node ∧
      after.heap = before.heap ++ [.proof nodeId] ∧
      after.saves = before.saves ++ [nodeId] ∧
      Step
        ⟨(), sourceHeap before.heap, .save () ⟨nodeId, ()⟩⟩
        ⟨(), sourceHeap after.heap,
          .saved () before.heap.length ⟨nodeId, ()⟩⟩ := by
  cases step with
  | save nodeId node stackTop nodeLookup =>
      refine ⟨nodeId, node, stackTop, nodeLookup, rfl, rfl, ?_⟩
      simpa using
        (Step.save () (sourceHeap before.heap) ⟨nodeId, ()⟩)

/-- Proof-relevant bridge object for one authored proof lookup followed by
`Z`.  It retains both source steps and the resulting protocol path. -/
structure ProofThenSaveProjection
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before after : MachineState source target) (index nodeId : Nat) where
  node : ProofNode source target
  lookup : ActionStep before (.step index)
    { before with stack := before.stack ++ [nodeId] }
  save : ActionStep
    { before with stack := before.stack ++ [nodeId] } .save after
  heapExact : sourceHeap after.heap =
    sourceHeap before.heap ++ [.occurrence ⟨nodeId, ()⟩]
  savesExact : after.saves = before.saves ++ [nodeId]
  path : (gslt Unit Nat Unit SourceAssertion).RewritePath
    ⟨(), sourceHeap before.heap, .lookup () index⟩
    ⟨(), sourceHeap after.heap,
      .saved () before.heap.length ⟨nodeId, ()⟩⟩

/-- An authored proof constructor immediately followed by `Z` produces one
continuous three-step protocol path.  The saved identity is forced by the
source stack-top premise rather than chosen independently for the target. -/
def proof_then_save_projects_to_protocol_path
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target}
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : before.heap[index]? = some (.proof nodeId))
    (nodeLookup : before.nodes[nodeId]? = some node)
    (save : ActionStep
      { before with stack := before.stack ++ [nodeId] } .save after) :
    ProofThenSaveProjection before after index nodeId := by
  cases save with
  | save savedId savedNode stackTop savedNodeLookup =>
      have sameId : nodeId = savedId := by
        simpa using stackTop
      subst savedId
      exact
        { node := node
          lookup := ActionStep.proof before index nodeId node
            heapLookup nodeLookup
          save := ActionStep.save _ nodeId savedNode stackTop savedNodeLookup
          heapExact := by simp
          savesExact := rfl
          path := by
            simpa using
              (lookupThenSavePath () (sourceHeap before.heap) index
                ⟨nodeId, ()⟩ (sourceHeap_get_proof heapLookup)) }

#print axioms sourceHeap_get_proof
#print axioms sourceHeap_get_assertion
#print axioms proof_constructor_projects
#print axioms assertion_constructor_does_not_project_as_proof
#print axioms assertion_constructor_dispatches_as_opaque
#print axioms save_projects_exactly
#print axioms proof_then_save_projects_to_protocol_path

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapSourceBridge
