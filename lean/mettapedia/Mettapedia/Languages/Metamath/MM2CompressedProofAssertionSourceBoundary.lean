import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchExtension

/-!
# Source-derived compressed assertion request boundary

An assertion launch is authorized by a scanner-decoded proof index and an
assertion-valued entry at that exact source heap position.  No substitution,
child proof, assertion result, or source assertion step is assumed here.  The
boundary therefore remains proof-neutral while determining every MM2 launch
row from source state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchExtension
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

def directAssertionContextAtBoundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (scanner : ScannerBoundary) (index cursor : Nat)
    (assertion : SourceAssertion) : DirectAssertionContext :=
  { scopeOwner := context.scopeOwner
    proofOwner := context.proofOwner
    wordPosition := scanner.wordPosition
    remainingBytes := scanner.remainingBytes
    index := index
    cursor := cursor
    heapNext := state.heap.length
    nodeNext := state.nodes.length
    stackPosition := state.stack.length
    assertionPosition := assertionPosition source assertion
    assertionLabel := assertion.label
    hypothesisCount := assertion.hypotheses.length }

@[simp] theorem directAssertionContextAtBoundary_machineRow
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (scanner : ScannerBoundary) (index cursor : Nat)
    (assertion : SourceAssertion) :
    (directAssertionContextAtBoundary context state scanner index cursor
      assertion).machineRow = machineRow context state := by
  rfl

@[simp] theorem directAssertionContextAtBoundary_headerRow
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (scanner : ScannerBoundary) (index cursor : Nat)
    (assertion : SourceAssertion) :
    (directAssertionContextAtBoundary context state scanner index cursor
      assertion).headerRow =
      assertionHeaderRow context.scopeOwner
        (assertionPosition source assertion) assertion := by
  rfl

def sourceAssertionHeapRow
    {source : SourcePrefix} (proofOwner : Atom) (heapPosition : Nat)
    (assertion : SourceAssertion) : Atom :=
  .expression
    [.symbol "mm-compressed-heap-assertion", proofOwner,
      (CompressedIndexCode.ofNat heapPosition).atom,
      natAtom (assertionPosition source assertion), stringAtom assertion.label]

@[simp] theorem directAssertionContextAtBoundary_heapRow
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (scanner : ScannerBoundary) (index cursor : Nat)
    (assertion : SourceAssertion) :
    (directAssertionContextAtBoundary context state scanner index cursor
      assertion).heapRow =
      sourceAssertionHeapRow (source := source) context.proofOwner index
        assertion := by
  rfl

theorem sourceAssertionHeapRow_mem_from_getElem
    {source : SourcePrefix} (proofOwner : Atom) (position : Nat)
    (heap : List (HeapEntry source)) (index : Nat)
    (assertion : SourceAssertion)
    (lookup : heap[index]? = some (.assertion assertion)) :
    sourceAssertionHeapRow (source := source) proofOwner (position + index)
        assertion ∈
      assertionHeapRowsFrom proofOwner position heap := by
  induction heap generalizing position index with
  | nil => simp at lookup
  | cons entry remaining induction =>
      cases index with
      | zero =>
          cases entry with
          | proof nodeId => simp at lookup
          | assertion candidate =>
              simp at lookup
              subst candidate
              simp [sourceAssertionHeapRow, assertionHeapRowsFrom]
      | succ index =>
          cases entry with
          | proof nodeId =>
              have tailLookup :
                  remaining[index]? = some (.assertion assertion) := by
                simpa using lookup
              have positionEq :
                  position + Nat.succ index = (position + 1) + index := by
                omega
              simpa only [assertionHeapRowsFrom, positionEq] using
                induction (position + 1) index tailLookup
          | assertion candidate =>
              have tailLookup :
                  remaining[index]? = some (.assertion assertion) := by
                simpa using lookup
              apply List.mem_cons_of_mem
              have positionEq :
                  position + Nat.succ index = (position + 1) + index := by
                omega
              simpa only [assertionHeapRowsFrom, positionEq] using
                induction (position + 1) index tailLookup

theorem sourceAssertionHeapRow_mem
    {source : SourcePrefix} (proofOwner : Atom)
    (heap : List (HeapEntry source)) (index : Nat)
    (assertion : SourceAssertion)
    (lookup : heap[index]? = some (.assertion assertion)) :
    sourceAssertionHeapRow (source := source) proofOwner index assertion ∈
      assertionHeapRows proofOwner heap := by
  simpa [assertionHeapRows] using
    sourceAssertionHeapRow_mem_from_getElem proofOwner 0 heap index assertion
      lookup

/-- Proof-neutral source authority for an assertion-valued compressed index.
The receipt computes the index from bytes; the heap lookup resolves it; source
well-formedness establishes database authorship. -/
structure SourceAssertionRequest
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index : Nat)
    (assertion : SourceAssertion) : Prop where
  receipt : ProofByteReceipt context scannerBefore scannerAfter occurrence index
  wellFormed : SourceBoundaryWellFormed context state
  heapLookup : state.heap[index]? = some (.assertion assertion)

theorem SourceAssertionRequest.authored
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence} {index : Nat}
    {assertion : SourceAssertion}
    (request : SourceAssertionRequest context state scannerBefore scannerAfter
      occurrence index assertion) :
    assertion ∈ source.assertions := by
  have bound := (List.getElem?_eq_some_iff.mp request.heapLookup).1
  have value := (List.getElem?_eq_some_iff.mp request.heapLookup).2
  apply request.wellFormed.heap_assertions_authored assertion
  have member := state.heap.get_mem ⟨index, bound⟩
  simpa [value] using member

def sourceAssertionAdditionalRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) : List Atom :=
  scannerRow context scanner ::
    (canonicalPassiveRows context state ledger).filter fun row =>
      row != sourceAssertionHeapRow (source := source) context.proofOwner index
        assertion

theorem sourceAssertionAdditionalRows_all_dynamic
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) :
    ∀ row,
      row ∈ sourceAssertionAdditionalRows context state ledger scanner index
        assertion →
      isDynamicRow row = true := by
  intro row member
  simp only [sourceAssertionAdditionalRows, List.mem_cons] at member
  rcases member with rfl | passive
  · exact scannerRow_isDynamic context scanner
  · exact canonicalPassiveRows_all_dynamic context state ledger row
      (List.mem_filter.mp passive).1

/-- Assertion-launch side rows have only the scanner head or one of the six
persistent source-display heads.  In particular they cannot masquerade as a
pending request or heap-lookup cursor. -/
theorem sourceAssertionAdditionalRows_head_cases
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) {row : Atom}
    (member : row ∈ sourceAssertionAdditionalRows context state ledger scanner
      index assertion) :
    compressedDynamicRowHead? row = some "mm-compressed-scan" ∨
      compressedDynamicRowHead? row = some "mm-compressed-heap-proof" ∨
      compressedDynamicRowHead? row = some "mm-compressed-heap-assertion" ∨
      compressedDynamicRowHead? row = some "mm-compressed-node" ∨
      compressedDynamicRowHead? row = some "mm-compressed-stack-cell" ∨
      compressedDynamicRowHead? row = some "mm-stack-cell" ∨
      compressedDynamicRowHead? row = some "mm-compressed-save-receipt" := by
  simp only [sourceAssertionAdditionalRows, List.mem_cons] at member
  rcases member with rfl | passive
  · exact Or.inl rfl
  · rcases canonicalPassiveRows_head_cases context state ledger
      (List.mem_filter.mp passive).1 with
      heapProof | heapAssertion | node | compactStack | normalStack | save
    · exact Or.inr (Or.inl heapProof)
    · exact Or.inr (Or.inr (Or.inl heapAssertion))
    · exact Or.inr (Or.inr (Or.inr (Or.inl node)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl compactStack))))
    · exact Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl normalStack)))))
    · exact Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr save)))))

theorem sourceAssertionAdditionalRows_no_supported
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) :
    cSupportedSourceExecFacts
        (sourceAssertionAdditionalRows context state ledger scanner index
          assertion) = [] := by
  unfold cSupportedSourceExecFacts
  rw [List.filterMap_eq_nil_iff]
  intro row member
  exact extractSupportedSourceExecFact_eq_none_of_dynamic row
    (sourceAssertionAdditionalRows_all_dynamic context state ledger scanner
      index assertion row member)

def sourceAssertionRequestSpace
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) : List Atom :=
  canonicalDirectAssertionSpace
      (directAssertionContextAtBoundary context state scanner index cursor
        assertion) ++
    sourceAssertionAdditionalRows context state ledger scanner index assertion

/-- The complete source-derived request still performs the same scheduled
MM2 launch and publishes the same normal-verifier interface. -/
structure SourceAssertionLaunchSquare
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor : Nat)
    (assertion : SourceAssertion) : Prop where
  request : SourceAssertionRequest context state scannerBefore scannerAfter
    occurrence index assertion
  sourceScannerStep :
    SourceStep (.request occurrence scannerBefore.phase)
      (.outcome occurrence (.decoded [.step index] scannerAfter.phase))
  assertionAuthored : assertion ∈ source.assertions
  heapRowSourceDerived :
    sourceAssertionHeapRow (source := source) context.proofOwner index assertion ∈
      assertionHeapRows context.proofOwner state.heap
  scheduled :
    cReflectiveSourceWorkQueueStep .leaveInert
        (sourceAssertionRequestSpace context state ledger scannerAfter index
          cursor assertion) =
      some (cFireReflectiveSourceExecFact
        (sourceAssertionRequestSpace context state ledger scannerAfter index
          cursor assertion) speculativeDirectAssertionDirective)
  publishesNormalInterface :
    let launchContext := directAssertionContextAtBoundary context state
      scannerAfter index cursor assertion
    ∀ row ∈ launchContext.launchRows,
      row ∈ cFireReflectiveSourceExecFact
        (sourceAssertionRequestSpace context state ledger scannerAfter index
          cursor assertion) speculativeDirectAssertionDirective
  nativeTarget :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      (sourceAssertionRequestSpace context state ledger scannerAfter index
        cursor assertion)
      (reflectiveNativeListExactTargetNativeType .leaveInert
        (cFireReflectiveSourceExecFact
          (sourceAssertionRequestSpace context state ledger scannerAfter index
            cursor assertion) speculativeDirectAssertionDirective)).pred

theorem source_assertion_launch_square
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor : Nat)
    (assertion : SourceAssertion)
    (request : SourceAssertionRequest context state scannerBefore scannerAfter
      occurrence index assertion) :
    SourceAssertionLaunchSquare context state ledger scannerBefore scannerAfter
      occurrence index cursor assertion where
  request := request
  sourceScannerStep := request.receipt.sourceStep
  assertionAuthored := request.authored
  heapRowSourceDerived :=
    sourceAssertionHeapRow_mem context.proofOwner state.heap index assertion
      request.heapLookup
  scheduled := by
    exact canonicalDirectAssertionSpace_append_steps
      (directAssertionContextAtBoundary context state scannerAfter index cursor
        assertion)
      (sourceAssertionAdditionalRows context state ledger scannerAfter index
        assertion)
      (sourceAssertionAdditionalRows_no_supported context state ledger
        scannerAfter index assertion)
  publishesNormalInterface := by
    exact canonicalDirectAssertionSpace_append_publishes
      (directAssertionContextAtBoundary context state scannerAfter index cursor
        assertion)
      (sourceAssertionAdditionalRows context state ledger scannerAfter index
        assertion)
  nativeTarget := by
    exact canonicalDirectAssertionSpace_append_inhabits_exact_native_target
      (directAssertionContextAtBoundary context state scannerAfter index cursor
        assertion)
      (sourceAssertionAdditionalRows context state ledger scannerAfter index
        assertion)
      (sourceAssertionAdditionalRows_no_supported context state ledger
        scannerAfter index assertion)

#print axioms sourceAssertionAdditionalRows_head_cases

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
