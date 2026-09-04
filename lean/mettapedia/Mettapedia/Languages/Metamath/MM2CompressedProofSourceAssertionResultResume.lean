import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
import Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultResumeSquare
import Mettapedia.Languages.Metamath.MM2CompressedProofSaveContinuous
import Mettapedia.Languages.Metamath.MM2NormalAddressSegment
import Mettapedia.Languages.Metamath.MM2NormalAssertionEntryAddressed
import Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed

/-!
# Source assertion result through compressed scanner resumption

This module joins one source assertion action to the normal-result,
compressed-rejoin, and scanner-resume segment.  The source action ledger uses
the logical action position, while the executable segment uses its encoded
scanner program counter.  Both identities are reconstructed from source
evidence and kept distinct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionResultResume

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoin
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultResumeSquare
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofSaveContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2NormalAddressSegment
open Mettapedia.Languages.Metamath.MM2NormalAssertionEntryAddressed
open Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceInferenceProjection

def assertionResultNode
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (member : assertion ∈ source.assertions)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (children : SourceGeneratedProvesForest source target actuals)
    (parents : List Nat) : ProofNode source target :=
  { formula := result
    tree := .assertion member node children
    parents := parents }

def assertionAfter
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target) (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (member : assertion ∈ source.assertions)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (children : SourceGeneratedProvesForest source target actuals) :
    MachineState source target :=
  { before with
    nodes := before.nodes ++
      [assertionResultNode assertion result member node children parents]
    stack := retained ++ [before.nodes.length] }

def sourceAssertionStep
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target) (index : Nat)
    (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (children : SourceGeneratedProvesForest source target actuals)
    (heapLookup : before.heap[index]? = some (.assertion assertion))
    (member : assertion ∈ source.assertions)
    (stack_eq : before.stack = retained ++ parents)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (resolved : ResolvesForest before.nodes parents actuals children) :
    ActionStep before (.step index)
      (assertionAfter before assertion result retained parents member node
        children) :=
  .assertion before index assertion retained parents children heapLookup member
    stack_eq node resolved

theorem resolvesForest_lengths
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {nodes : List (ProofNode source target)}
    {parents : List Nat} {formulas : List ConstantHeadedFormula}
    {forest : SourceGeneratedProvesForest source target formulas}
    (resolved : ResolvesForest nodes parents formulas forest) :
    parents.length = formulas.length := by
  induction resolved with
  | nil => rfl
  | cons node forest lookup tail induction =>
      simp only [List.length_cons, Nat.succ.injEq]
      exact induction

def normalResultContextAtSourceAssertion
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scanner : ScannerBoundary) (index : Nat) (assertion : SourceAssertion)
    (retained : List Nat) (result : ConstantHeadedFormula) :
    NormalResultContext :=
  { scopeOwner := context.scopeOwner
    proofOwner := context.proofOwner
    wordPosition := scanner.wordPosition
    remainingBytes := scanner.remainingBytes
    index := index
    heapNext := before.heap.length
    nodeNext := before.nodes.length
    stackBase := retained.length
    assertionLabel := assertion.label
    resultTypecode := result.typecode
    resultBody := result.body }

def encodedAssertionOccurrence
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scanner : ScannerBoundary) (index : Nat) (assertion : SourceAssertion)
    (retained : List Nat) (result : ConstantHeadedFormula) : Atom :=
  (normalResultContextAtSourceAssertion context before scanner index assertion
    retained result).rejoinContext.occurrence

def sourceAssertionAddressSegment
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scanner : ScannerBoundary) (index : Nat) (assertion : SourceAssertion)
    (retained : List Nat) (result : ConstantHeadedFormula) :
    NormalAddressSegment :=
  compressedResultSegment
    (normalResultContextAtSourceAssertion context before scanner index assertion
      retained result)

@[simp] theorem sourceAssertion_launch_result_pc_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scanner : ScannerBoundary) (index cursor : Nat)
    (assertion : SourceAssertion) (retained : List Nat)
    (result : ConstantHeadedFormula) :
    (directAssertionContextAtBoundary context before scanner index cursor
      assertion).pc =
      (normalResultContextAtSourceAssertion context before scanner index
        assertion retained result).pc := by
  rfl

@[simp] theorem sourceAssertion_launch_result_context_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scanner : ScannerBoundary) (index cursor : Nat)
    (assertion : SourceAssertion) (retained : List Nat)
    (result : ConstantHeadedFormula) :
    (directAssertionContextAtBoundary context before scanner index cursor
      assertion).assertionContextRow =
      (normalResultContextAtSourceAssertion context before scanner index
        assertion retained result).rejoinContext.contextRow := by
  rfl

@[simp] theorem sourceAssertion_launch_result_label_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scanner : ScannerBoundary) (index cursor : Nat)
    (assertion : SourceAssertion) (retained : List Nat)
    (result : ConstantHeadedFormula) :
    (directAssertionContextAtBoundary context before scanner index cursor
      assertion).normalLabelRow =
      (normalResultContextAtSourceAssertion context before scanner index
        assertion retained result).rejoinContext.normalLabelRow := by
  rfl

theorem sourceAssertion_address_segment_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scanner : ScannerBoundary) (index : Nat) (assertion : SourceAssertion)
    (retained : List Nat) (result : ConstantHeadedFormula) :
    let normalContext := normalResultContextAtSourceAssertion context before
      scanner index assertion retained result
    let segment := sourceAssertionAddressSegment context before scanner index
      assertion retained result
    segment.bodyBuiltRow context.proofOwner context.scopeOwner assertion.label
          result.typecode retained.length result.body =
        normalContext.bodyBuiltRow ∧
      segment.controlRow context.scopeOwner context.proofOwner
          (retained.length + 1) =
        normalContext.rejoinContext.returnedControlRow ∧
      segment.assertionStackRow context.proofOwner retained.length
          result.typecode result.body assertion.label =
        normalContext.rejoinContext.returnedStackRow ∧
      segment.linkedLabelRow context.proofOwner assertion.label =
        normalContext.rejoinContext.normalLabelRow := by
  dsimp only [sourceAssertionAddressSegment]
  exact
    ⟨compressed_bodyBuiltRow_exact _, compressed_controlRow_exact _,
      compressed_assertionStackRow_exact _, compressed_linkedLabelRow_exact _⟩

/-- The target-oriented ledger extends the prior source ledger by the exact
scanner address used by the executable assertion continuation. -/
def encodedAssertionLedger
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (member : assertion ∈ source.assertions)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (children : SourceGeneratedProvesForest source target actuals) :
    NodeOccurrenceLedger
      (assertionAfter before assertion result retained parents member node
        children) :=
  { occurrences := ledger.occurrences ++
      [encodedAssertionOccurrence context before scanner index assertion
        retained result]
    aligned := by
      simp [assertionAfter, ledger.aligned] }

@[simp] theorem normalResultContextAtSourceAssertion_resultFormula
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scanner : ScannerBoundary) (index : Nat) (assertion : SourceAssertion)
    (retained : List Nat) (result : ConstantHeadedFormula) :
    (normalResultContextAtSourceAssertion context before scanner index assertion
      retained result).resultFormula = formulaAtom result := by
  rfl

/-- The encoded scanner address and the logical action address are different
representations.  A later execution invariant must transport between them; it
must not identify them by reflexivity. -/
theorem encodedAssertionOccurrence_ne_actionOccurrence
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scanner : ScannerBoundary) (index proofPosition : Nat)
    (assertion : SourceAssertion) (retained : List Nat)
    (result : ConstantHeadedFormula) :
    encodedAssertionOccurrence context before scanner index assertion retained
        result ≠
      compressedAssertionOccurrenceAtom proofPosition assertion.label := by
  change
    Atom.expression
        [Atom.symbol "mm-assertion-occurrence",
          Atom.expression
            [Atom.symbol "mm-compressed-assertion-pc",
              natAtom scanner.wordPosition,
              listAtom natAtom (scanner.remainingBytes.map UInt8.toNat),
              (CompressedIndexCode.ofNat index).atom],
          stringAtom assertion.label] ≠
      Atom.expression
        [Atom.symbol "mm-assertion-occurrence",
          (CompressedIndexCode.ofNat proofPosition).atom,
          stringAtom assertion.label]
  intro equal
  have fields := Atom.expression.inj equal
  simp [CompressedIndexCode.atom, compressedIndexCodeAtom] at fields

theorem encodedAssertionLedger_new_lookup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (member : assertion ∈ source.assertions)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (children : SourceGeneratedProvesForest source target actuals) :
    (encodedAssertionLedger context before ledger scanner index assertion result
      retained parents member node children).occurrences[before.nodes.length]? =
        some (encodedAssertionOccurrence context before scanner index assertion
          retained result) := by
  simp [encodedAssertionLedger, ledger.aligned]

theorem actionAssertionLedger_new_lookup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target) (ledger : NodeOccurrenceLedger before)
    (index proofPosition : Nat) (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (children : SourceGeneratedProvesForest source target actuals)
    (heapLookup : before.heap[index]? = some (.assertion assertion))
    (member : assertion ∈ source.assertions)
    (stack_eq : before.stack = retained ++ parents)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (resolved : ResolvesForest before.nodes parents actuals children) :
    let step := sourceAssertionStep before index assertion result retained
      parents children heapLookup member stack_eq node resolved
    (ActionStep.occurrenceLedger step proofPosition ledger).occurrences[before.nodes.length]? =
      some (compressedAssertionOccurrenceAtom proofPosition assertion.label) := by
  simp [ActionStep.occurrenceLedger, actionOccurrenceAtoms,
    heapOccurrenceKinds, heapLookup, ledger.aligned]

theorem assertionAfter_new_node_lookup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target) (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (member : assertion ∈ source.assertions)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (children : SourceGeneratedProvesForest source target actuals) :
    (assertionAfter before assertion result retained parents member node
      children).nodes[before.nodes.length]? =
        some (assertionResultNode assertion result member node children
          parents) := by
  simp [assertionAfter]

theorem assertionAfter_new_stack_lookup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target) (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (member : assertion ∈ source.assertions)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (children : SourceGeneratedProvesForest source target actuals) :
    (assertionAfter before assertion result retained parents member node
      children).stack[retained.length]? = some before.nodes.length := by
  simp [assertionAfter]

theorem sourceNormalResult_returnedMachine_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scanner : ScannerBoundary) (index : Nat) (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (member : assertion ∈ source.assertions)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (children : SourceGeneratedProvesForest source target actuals) :
    (normalResultContextAtSourceAssertion context before scanner index assertion
      retained result).rejoinContext.returnedMachineRow =
      machineRow context
        (assertionAfter before assertion result retained parents member node
          children) := by
  simp [normalResultContextAtSourceAssertion,
    NormalResultContext.rejoinContext, RejoinContext.returnedMachineRow,
    RejoinContext.code, machineRow, assertionAfter]

theorem sourceNormalResult_resultNode_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scanner : ScannerBoundary) (index : Nat) (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (member : assertion ∈ source.assertions)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (children : SourceGeneratedProvesForest source target actuals) :
    (normalResultContextAtSourceAssertion context before scanner index assertion
      retained result).rejoinContext.resultNodeRow =
      nodeRow context.proofOwner
        (displayedProofOccurrence before.nodes.length
          (assertionResultNode assertion result member node children parents)
          (encodedAssertionOccurrence context before scanner index assertion
            retained result)) := by
  rfl

theorem sourceNormalResult_resultStack_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (scanner : ScannerBoundary) (index : Nat) (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (member : assertion ∈ source.assertions)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (children : SourceGeneratedProvesForest source target actuals) :
    (normalResultContextAtSourceAssertion context before scanner index assertion
      retained result).rejoinContext.resultStackRow =
      compressedStackRow context.proofOwner retained.length
        (displayedProofOccurrence before.nodes.length
          (assertionResultNode assertion result member node children parents)
          (encodedAssertionOccurrence context before scanner index assertion
            retained result)) := by
  rfl

theorem sourceNormalResult_rows_source_derived
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (member : assertion ∈ source.assertions)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (children : SourceGeneratedProvesForest source target actuals) :
    let after := assertionAfter before assertion result retained parents member
      node children
    let encodedLedger := encodedAssertionLedger context before ledger scanner
      index assertion result retained parents member node children
    let normalContext := normalResultContextAtSourceAssertion context before
      scanner index assertion retained result
    normalContext.rejoinContext.resultNodeRow ∈
        sourceNodeRows context.proofOwner after encodedLedger ∧
      normalContext.rejoinContext.resultStackRow ∈
        sourceStackRows context.proofOwner after encodedLedger := by
  dsimp only
  let newNode := assertionResultNode assertion result member node children parents
  let occurrence := encodedAssertionOccurrence context before scanner index
    assertion retained result
  have nodeLookup := assertionAfter_new_node_lookup before assertion result
    retained parents member node children
  have stackLookup := assertionAfter_new_stack_lookup before assertion result
    retained parents member node children
  have occurrenceLookup := encodedAssertionLedger_new_lookup context before
    ledger scanner index assertion result retained parents member node children
  constructor
  · rw [sourceNormalResult_resultNode_exact context before scanner index
      assertion result retained parents member node children]
    exact nodeRow_mem_sourceNodeRows context.proofOwner _ _ _ newNode occurrence
      nodeLookup occurrenceLookup
  · rw [sourceNormalResult_resultStack_exact context before scanner index
      assertion result retained parents member node children]
    exact compressedStackRow_mem_sourceStackRows context.proofOwner _ _ _ _
      newNode occurrence stackLookup nodeLookup occurrenceLookup

/-- Source-indexed result boundary.  It combines the semantic assertion step,
the exact logical and encoded occurrence lookups, and the actual three-step
normal-result-to-scanner target segment. -/
structure SourceAssertionResultResumeBoundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (scanner : ScannerBoundary)
    (index proofPosition : Nat) (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (children : SourceGeneratedProvesForest source target actuals)
    (heapLookup : before.heap[index]? = some (.assertion assertion))
    (member : assertion ∈ source.assertions)
    (stack_eq : before.stack = retained ++ parents)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (resolved : ResolvesForest before.nodes parents actuals children) where
  sourceStep : ActionStep before (.step index)
    (assertionAfter before assertion result retained parents member node
      children)
  sourceBoundaryAfter : SourceBoundaryWellFormed context
    (assertionAfter before assertion result retained parents member node
      children)
  logicalOccurrenceLookup :
    (ActionStep.occurrenceLedger sourceStep proofPosition ledger).occurrences[before.nodes.length]? =
      some (compressedAssertionOccurrenceAtom proofPosition assertion.label)
  encodedOccurrenceLookup :
    (encodedAssertionLedger context before ledger scanner index assertion result
      retained parents member node children).occurrences[before.nodes.length]? =
        some (encodedAssertionOccurrence context before scanner index assertion
          retained result)
  occurrenceRepresentationsDistinct :
    encodedAssertionOccurrence context before scanner index assertion retained
        result ≠
      compressedAssertionOccurrenceAtom proofPosition assertion.label
  resultFormulaExact :
    (normalResultContextAtSourceAssertion context before scanner index assertion
      retained result).resultFormula = formulaAtom result
  addressSegmentExact :
    let normalContext := normalResultContextAtSourceAssertion context before
      scanner index assertion retained result
    let segment := sourceAssertionAddressSegment context before scanner index
      assertion retained result
    segment.bodyBuiltRow context.proofOwner context.scopeOwner assertion.label
          result.typecode retained.length result.body =
        normalContext.bodyBuiltRow ∧
      segment.controlRow context.scopeOwner context.proofOwner
          (retained.length + 1) =
        normalContext.rejoinContext.returnedControlRow ∧
      segment.assertionStackRow context.proofOwner retained.length
          result.typecode result.body assertion.label =
        normalContext.rejoinContext.returnedStackRow ∧
      segment.linkedLabelRow context.proofOwner assertion.label =
        normalContext.rejoinContext.normalLabelRow
  targetSegment : NormalResultCompressedResumeSquare
    (normalResultContextAtSourceAssertion context before scanner index assertion
      retained result)
  rowsSourceDerived :
    let after := assertionAfter before assertion result retained parents member
      node children
    let encodedLedger := encodedAssertionLedger context before ledger scanner
      index assertion result retained parents member node children
    let normalContext := normalResultContextAtSourceAssertion context before
      scanner index assertion retained result
    normalContext.rejoinContext.resultNodeRow ∈
        sourceNodeRows context.proofOwner after encodedLedger ∧
      normalContext.rejoinContext.resultStackRow ∈
        sourceStackRows context.proofOwner after encodedLedger

def sourceAssertionResultResumeBoundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (scanner : ScannerBoundary)
    (index proofPosition : Nat) (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (children : SourceGeneratedProvesForest source target actuals)
    (heapLookup : before.heap[index]? = some (.assertion assertion))
    (member : assertion ∈ source.assertions)
    (stack_eq : before.stack = retained ++ parents)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (resolved : ResolvesForest before.nodes parents actuals children)
    (wellFormed : SourceBoundaryWellFormed context before) :
    SourceAssertionResultResumeBoundary context before ledger scanner index
      proofPosition assertion result retained parents children heapLookup member
      stack_eq node resolved := by
  let step := sourceAssertionStep before index assertion result retained parents
    children heapLookup member stack_eq node resolved
  refine
    { sourceStep := step
      sourceBoundaryAfter := wellFormed.actionStep step
      logicalOccurrenceLookup := ?_
      encodedOccurrenceLookup := ?_
      occurrenceRepresentationsDistinct := ?_
      resultFormulaExact := ?_
      addressSegmentExact := ?_
      targetSegment := normal_result_compressed_resume_square _
      rowsSourceDerived := ?_ }
  · exact actionAssertionLedger_new_lookup before ledger index proofPosition
      assertion result retained parents children heapLookup member stack_eq node
      resolved
  · exact encodedAssertionLedger_new_lookup context before ledger scanner index
      assertion result retained parents member node children
  · exact encodedAssertionOccurrence_ne_actionOccurrence context before scanner
      index proofPosition assertion retained result
  · exact normalResultContextAtSourceAssertion_resultFormula context before
      scanner index assertion retained result
  · exact sourceAssertion_address_segment_exact context before scanner index
      assertion retained result
  · exact sourceNormalResult_rows_source_derived context before ledger scanner
      index assertion result retained parents member node children

/-- One scanner-authenticated assertion request, its actual launch transition,
and its source-derived result/resume boundary.  The normal assertion
calculation between those endpoints remains an explicit separate obligation. -/
structure SourceAssertionLaunchResumeBoundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor proofPosition : Nat)
    (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (children : SourceGeneratedProvesForest source target actuals)
    (request : SourceAssertionRequest context before scannerBefore scannerAfter
      occurrence index assertion)
    (stack_eq : before.stack = retained ++ parents)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (resolved : ResolvesForest before.nodes parents actuals children) where
  launch : SourceAssertionLaunchSquare context before ledger scannerBefore
    scannerAfter occurrence index cursor assertion
  resultBoundary : SourceAssertionResultResumeBoundary context before ledger scannerAfter index
      proofPosition assertion result retained parents children request.heapLookup
      request.authored stack_eq node resolved

def sourceAssertionLaunchResumeBoundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor proofPosition : Nat)
    (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (children : SourceGeneratedProvesForest source target actuals)
    (request : SourceAssertionRequest context before scannerBefore scannerAfter
      occurrence index assertion)
    (stack_eq : before.stack = retained ++ parents)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (resolved : ResolvesForest before.nodes parents actuals children) :
    SourceAssertionLaunchResumeBoundary context before ledger scannerBefore
      scannerAfter occurrence index cursor proofPosition assertion result
      retained parents children request stack_eq node resolved :=
  { launch := source_assertion_launch_square context before ledger scannerBefore
      scannerAfter occurrence index cursor assertion request
    resultBoundary := sourceAssertionResultResumeBoundary context before ledger
      scannerAfter index proofPosition assertion result retained parents children
      request.heapLookup request.authored stack_eq node resolved
      request.wellFormed }

/-- The assertion launch/result boundary enriched by the complete scheduled
assertion-entry and result-body traces at the compressed proof address.
Hypothesis matching and disjoint-variable checking remain separate obligations
between those traces. -/
structure SourceAssertionLaunchBodyResumeBoundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor proofPosition : Nat)
    (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (children : SourceGeneratedProvesForest source target actuals)
    (request : SourceAssertionRequest context before scannerBefore scannerAfter
      occurrence index assertion)
    (stack_eq : before.stack = retained ++ parents)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (resolved : ResolvesForest before.nodes parents actuals children) where
  endpoints : SourceAssertionLaunchResumeBoundary context before ledger
    scannerBefore scannerAfter occurrence index cursor proofPosition assertion
    result retained parents children request stack_eq node resolved
  launchStackTopExact :
    (directAssertionContextAtBoundary context before scannerAfter index cursor
      assertion).stackPosition =
        retained.length + assertion.hypotheses.length
  launchEntryRowsExact :
    let launchContext := directAssertionContextAtBoundary context before
      scannerAfter index cursor assertion
    let segment := sourceAssertionAddressSegment context before scannerAfter
      index assertion retained result
    [launchContext.normalControlRow, launchContext.normalLabelRow,
        launchContext.headerRow] =
      (normalAssertionStartPhaseAtomsAt context.scopeOwner context.proofOwner
        segment (retained.length + assertion.hypotheses.length)
        (assertionPosition source assertion) assertion).drop 1
  entryTrace :
    let segment := sourceAssertionAddressSegment context before scannerAfter
      index assertion retained result
    AddressedAssertionEntryTrace context.scopeOwner context.proofOwner segment
      retained.length (assertionPosition source assertion) assertion
  bodyTrace :
    let segment := sourceAssertionAddressSegment context before scannerAfter
      index assertion retained result
    AddressedBodyBuildTrace context.proofOwner segment.currentProof
      (segment.resultContext context.scopeOwner assertion.label result.typecode
        retained.length) substitution assertion.formula.body [] result.body
  bodyBuiltRowExact :
    let normalContext := normalResultContextAtSourceAssertion context before
      scannerAfter index assertion retained result
    let segment := sourceAssertionAddressSegment context before scannerAfter
      index assertion retained result
    normalBodyBuiltRowAt context.proofOwner segment.currentProof
        (segment.resultContext context.scopeOwner assertion.label result.typecode
          retained.length) result.body =
      normalContext.bodyBuiltRow

def sourceAssertionLaunchBodyResumeBoundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor proofPosition : Nat)
    (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (children : SourceGeneratedProvesForest source target actuals)
    (request : SourceAssertionRequest context before scannerBefore scannerAfter
      occurrence index assertion)
    (stack_eq : before.stack = retained ++ parents)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (resolved : ResolvesForest before.nodes parents actuals children)
    (presentation :
      calculusLanguageDefOfSourcePrefix? source = some target.1) :
    SourceAssertionLaunchBodyResumeBoundary context before ledger scannerBefore
      scannerAfter occurrence index cursor proofPosition assertion result
      retained parents children request stack_eq node resolved := by
  have projectionPresentation :
      calculusLanguageDefOfProjection? source.toProjection = some target.1 := by
    rw [← calculusLanguageDefOfSourcePrefix?_eq_runtime]
    exact presentation
  have projectionMember :
      assertion.toProjectionView ∈ source.toProjection.assertions := by
    exact List.mem_map_of_mem request.authored
  have instances :=
    (assertionRuleApplication_iff_instances source.toProjection target
      projectionPresentation projectionMember).mp node.application
  obtain ⟨hypothesisInstances, _resultTypecode⟩ := instances
  have arity : assertion.hypotheses.length = actuals.length :=
    hypothesisInstances.lengths
  have parentLength : parents.length = actuals.length :=
    resolvesForest_lengths resolved
  have stackTopExact : before.stack.length =
      retained.length + assertion.hypotheses.length := by
    have stackLength := congrArg List.length stack_eq
    simpa [List.length_append, parentLength, arity] using stackLength
  let segment := sourceAssertionAddressSegment context before scannerAfter index
    assertion retained result
  refine
    { endpoints := sourceAssertionLaunchResumeBoundary context before ledger
        scannerBefore scannerAfter occurrence index cursor proofPosition
        assertion result retained parents children request stack_eq node resolved
      launchStackTopExact := ?_
      launchEntryRowsExact := ?_
      entryTrace := ?_
      bodyTrace := ?_
      bodyBuiltRowExact := ?_ }
  · exact stackTopExact
  · simp [normalAssertionStartPhaseAtomsAt,
      MM2CompressedProofAssertionContinuous.DirectAssertionContext.normalControlRow,
      MM2CompressedProofAssertionContinuous.DirectAssertionContext.normalLabelRow,
      MM2CompressedProofAssertionContinuous.DirectAssertionContext.headerRow,
      MM2CompressedProofAssertionContinuous.DirectAssertionContext.pc,
      MM2CompressedProofAssertionContinuous.DirectAssertionContext.nextPC,
      MM2CompressedProofAssertionContinuous.DirectAssertionContext.code,
      MM2CompressedProofAssertionContinuous.DirectAssertionContext.bytes,
      MM2CompressedProofNormalResultRejoin.NormalResultContext.pc,
      MM2CompressedProofNormalResultRejoin.NormalResultContext.nextPC,
      MM2CompressedProofNormalResultRejoin.NormalResultContext.code,
      MM2CompressedProofNormalResultRejoin.NormalResultContext.bytes,
      directAssertionContextAtBoundary, sourceAssertionAddressSegment,
      compressedResultSegment, normalResultContextAtSourceAssertion,
      NormalAddressSegment.linkedLabelRow, assertionHeaderRow, stackTopExact]
  · exact addressedAssertionEntryTrace_exact context.scopeOwner
      context.proofOwner segment retained.length
      (assertionPosition source assertion) assertion
  · exact GeneratedAssertionNode.result_has_addressed_body_trace
      source.toProjection target projectionPresentation projectionMember node
      context.proofOwner segment.currentProof
      (segment.resultContext context.scopeOwner assertion.label result.typecode
        retained.length)
  · let normalContext := normalResultContextAtSourceAssertion context before
      scannerAfter index assertion retained result
    calc
      normalBodyBuiltRowAt context.proofOwner segment.currentProof
          (segment.resultContext context.scopeOwner assertion.label
            result.typecode retained.length) result.body =
        segment.bodyBuiltRow context.proofOwner context.scopeOwner
          assertion.label result.typecode retained.length result.body :=
            normalBodyBuiltRowAt_segment_exact segment context.scopeOwner
              context.proofOwner assertion.label result.typecode retained.length
              result.body
      _ = normalContext.bodyBuiltRow :=
        (sourceAssertion_address_segment_exact context before scannerAfter index
          assertion retained result).1

section AxiomAudit

#print axioms encodedAssertionOccurrence_ne_actionOccurrence
#print axioms sourceAssertion_launch_result_pc_exact
#print axioms sourceAssertion_launch_result_context_exact
#print axioms sourceAssertion_launch_result_label_exact
#print axioms sourceAssertion_address_segment_exact
#print axioms encodedAssertionLedger_new_lookup
#print axioms actionAssertionLedger_new_lookup
#print axioms sourceNormalResult_returnedMachine_exact
#print axioms sourceNormalResult_resultNode_exact
#print axioms sourceNormalResult_resultStack_exact
#print axioms sourceNormalResult_rows_source_derived
#print axioms sourceAssertionResultResumeBoundary
#print axioms sourceAssertionLaunchResumeBoundary
#print axioms resolvesForest_lengths
#print axioms sourceAssertionLaunchBodyResumeBoundary

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionResultResume
