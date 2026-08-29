import Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitCanonicalFrame

/-!
# Source-derived occurrence ledger to canonical MM2 proof hit

This module joins the derivation-generated occurrence ledger to the symbolic
scheduled MM2 hit.  The proof occurrence is reconstructed from source
execution and heap lookup; callers supply only the ordinary target frontier
and scanner context.  Scheduler order, matcher substitution, concrete rows,
and output representation are all consequences of the canonical compiler.
-/

set_option autoImplicit false

open Mettapedia.GSLT.LanguageDef

namespace Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerCanonicalHitBridge

open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitCanonicalFrame
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceProjection

/-- Retain only the target-owned scanner context while deriving every machine
frontier from the represented source state.  In particular, the output stack
frontier is exactly the successor of the source stack length. -/
def directProofContextAtMachine
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : DirectProofContext) (state : MachineState source target)
    (index : Nat) :
    DirectProofContext :=
  { context with
      index := index
      heapNext := state.heap.length
      nodeNext := state.nodes.length
      stackPosition := state.stack.length
      nextStackPosition := state.stack.length + 1 }

@[simp] theorem directProofContextAtMachine_index
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : DirectProofContext) (state : MachineState source target)
    (index : Nat) :
    (directProofContextAtMachine context state index).index = index := by
  rfl

@[simp] theorem directProofContextAtMachine_proofOwner
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : DirectProofContext) (state : MachineState source target)
    (index : Nat) :
    (directProofContextAtMachine context state index).proofOwner =
      context.proofOwner := by
  rfl

@[simp] theorem directProofContextAtMachine_frontiers
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : DirectProofContext) (state : MachineState source target)
    (index : Nat) :
    (directProofContextAtMachine context state index).heapNext =
        state.heap.length ∧
      (directProofContextAtMachine context state index).nodeNext =
        state.nodes.length ∧
      (directProofContextAtMachine context state index).stackPosition =
        state.stack.length ∧
      (directProofContextAtMachine context state index).nextStackPosition =
        state.stack.length + 1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every proof entry in the result of an arbitrary verified action execution
selects the occurrence computed by that execution's ledger and realizes the
canonical scheduled MM2 hit. -/
theorem execute_derived_proof_lookup_commutes
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target}
    {actions : List CompressedAction}
    (execution : Execute before actions after)
    (proofPosition : Nat) (initialLedger : NodeOccurrenceLedger before)
    (context : DirectProofContext)
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : after.heap[index]? = some (.proof nodeId))
    (nodeLookup : after.nodes[nodeId]? = some node) :
    let ledger := Execute.occurrenceLedger execution proofPosition initialLedger
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      let item := displayedProofOccurrence nodeId node sourceOccurrence
      DirectProofHitCommutingSquare
        (directProofContextAtMachine context after index) item
        (displayedProofRequestState after ledger index)
        (canonicalDirectProofSpace
          (directProofContextAtMachine context after index) item) := by
  dsimp only
  let ledger := Execute.occurrenceLedger execution proofPosition initialLedger
  obtain ⟨sourceOccurrence, occurrenceLookup, displayedLookup⟩ :=
    displayedHeap_get_proof after ledger index nodeId node heapLookup nodeLookup
  refine ⟨sourceOccurrence, occurrenceLookup, ?_⟩
  apply canonical_direct_proof_hit_commutes
  · rfl
  · simpa [directProofContextAtMachine, displayedProofRequestState]
      using displayedLookup

/-- One source proof action and one canonical MM2 direct hit form the same
local stack extension.  The source action reuses its derivation occurrence,
the target writes that occurrence at the old source stack length, and its
next frontier is exactly the new source stack length. -/
theorem source_proof_action_commutes
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    (context : DirectProofContext)
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : before.heap[index]? = some (.proof nodeId))
    (nodeLookup : before.nodes[nodeId]? = some node) :
    let after : MachineState source target :=
      { before with stack := before.stack ++ [nodeId] }
    ∃ sourceStep : ActionStep before (.step index) after,
      (ActionStep.occurrenceLedger sourceStep proofPosition ledger).occurrences =
          ledger.occurrences ∧
        (directProofContextAtMachine context before index).nextStackPosition =
          after.stack.length ∧
        ∃ sourceOccurrence,
          ledger.occurrences[nodeId]? = some sourceOccurrence ∧
          let item := displayedProofOccurrence nodeId node sourceOccurrence
          DirectProofHitCommutingSquare
            (directProofContextAtMachine context before index) item
            (displayedProofRequestState before ledger index)
            (canonicalDirectProofSpace
              (directProofContextAtMachine context before index) item) := by
  let after : MachineState source target :=
    { before with stack := before.stack ++ [nodeId] }
  let sourceStep : ActionStep before (.step index) after :=
    .proof before index nodeId node heapLookup nodeLookup
  refine ⟨sourceStep, ?_, ?_, ?_⟩
  · simp [ActionStep.occurrenceLedger, actionOccurrenceAtoms,
      heapOccurrenceKinds, heapLookup]
  · simp [directProofContextAtMachine]
  · obtain ⟨sourceOccurrence, occurrenceLookup, displayedLookup⟩ :=
      displayedHeap_get_proof before ledger index nodeId node
        heapLookup nodeLookup
    refine ⟨sourceOccurrence, occurrenceLookup, ?_⟩
    apply canonical_direct_proof_hit_commutes
    · rfl
    · simpa [directProofContextAtMachine, displayedProofRequestState]
        using displayedLookup

/-- Complete compressed-theorem specialization.  Its ledger is the canonical
header/action fold of the admitted source derivation, never a supplied side
packet.  This theorem concerns any proof entry in the final source state; the
full action-by-action simulation remains a separate induction. -/
theorem compressed_theorem_final_proof_lookup_commutes
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords)
    (context : DirectProofContext)
    (index nodeId : Nat) (node : ProofNode before.toSourcePrefix step.target)
    (heapLookup : step.finalState.heap[index]? = some (.proof nodeId))
    (nodeLookup : step.finalState.nodes[nodeId]? = some node) :
    let ledger := CompressedTheoremStep.occurrenceLedger step context.proofOwner
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      let item := displayedProofOccurrence nodeId node sourceOccurrence
      DirectProofHitCommutingSquare
        (directProofContextAtMachine context step.finalState index) item
        (displayedProofRequestState step.finalState ledger index)
        (canonicalDirectProofSpace
          (directProofContextAtMachine context step.finalState index) item) := by
  exact execute_derived_proof_lookup_commutes step.execution 0
    (HeaderBuild.occurrenceLedger step.header context.proofOwner 0
      (NodeOccurrenceLedger.empty before.toSourcePrefix step.target))
    context index nodeId node heapLookup nodeLookup

#print axioms directProofContextAtMachine_index
#print axioms directProofContextAtMachine_proofOwner
#print axioms directProofContextAtMachine_frontiers
#print axioms execute_derived_proof_lookup_commutes
#print axioms source_proof_action_commutes
#print axioms compressed_theorem_final_proof_lookup_commutes

end Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerCanonicalHitBridge
