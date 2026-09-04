import Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionResultResume
import Mettapedia.Languages.Metamath.MM2NormalAssertionFloatingAddressed

/-!
# Source-bound compressed floating-hypothesis execution

This module reconstructs the first floating-hypothesis transition from the
source assertion instance, resolved parent stack, and occurrence ledger.  The
child occurrence is discovered from the aligned source ledger rather than
accepted as target evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSourceFloatingHypothesis

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionResultResume
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
open Mettapedia.Languages.Metamath.MM2NormalAddressSegment
open Mettapedia.Languages.Metamath.MM2NormalAssertionEntryAddressed
open Mettapedia.Languages.Metamath.MM2NormalAssertionFloatingAddressed
open Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- Pointwise source-stack encoding for the normal observation paired with
the existing compact observation. -/
theorem normalStackRow_mem_sourceStackRowsFrom
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (position : Nat)
    (stack : List Nat) (index nodeId : Nat)
    (node : ProofNode source target) (occurrence : Atom)
    (stackLookup : stack[index]? = some nodeId)
    (nodeLookup : state.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some occurrence) :
    normalStackRow proofOwner (position + index)
        (displayedProofOccurrence nodeId node occurrence) ∈
      sourceStackRowsFrom proofOwner state ledger position stack := by
  induction stack generalizing position index with
  | nil => simp at stackLookup
  | cons head stack induction =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at stackLookup
          subst head
          simp [sourceStackRowsFrom, nodeLookup, occurrenceLookup]
      | succ index =>
          simp only [List.getElem?_cons_succ] at stackLookup
          have tail := induction (position := position + 1) (index := index)
            stackLookup
          have positionEq :
              position + Nat.succ index = position + 1 + index := by
            omega
          rw [positionEq]
          simp only [sourceStackRowsFrom]
          split
          · exact List.mem_append_right _ tail
          · simpa only [List.nil_append] using tail

theorem normalStackRow_mem_sourceStackRows
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (proofOwner : Atom) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (stackPosition nodeId : Nat)
    (node : ProofNode source target) (occurrence : Atom)
    (stackLookup : state.stack[stackPosition]? = some nodeId)
    (nodeLookup : state.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some occurrence) :
    normalStackRow proofOwner stackPosition
        (displayedProofOccurrence nodeId node occurrence) ∈
      sourceStackRows proofOwner state ledger := by
  simpa [sourceStackRows] using
    normalStackRow_mem_sourceStackRowsFrom proofOwner state ledger 0
      state.stack stackPosition nodeId node occurrence stackLookup nodeLookup
      occurrenceLookup

theorem occurrenceLedger_lookup_exists_of_node_lookup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) (ledger : NodeOccurrenceLedger state)
    (nodeId : Nat) (node : ProofNode source target)
    (nodeLookup : state.nodes[nodeId]? = some node) :
    ∃ occurrence, ledger.occurrences[nodeId]? = some occurrence := by
  have nodeBound := (List.getElem?_eq_some_iff.mp nodeLookup).1
  have occurrenceBound : nodeId < ledger.occurrences.length := by
    rw [ledger.aligned]
    exact nodeBound
  let occurrence := ledger.occurrences[nodeId]'occurrenceBound
  refine ⟨occurrence, ?_⟩
  rw [List.getElem?_eq_some_iff]
  exact ⟨occurrenceBound, rfl⟩

/-- One source floating-hypothesis constructor and one resolved parent produce
the exact scheduled compressed-address MM2 step. -/
theorem sourceFloatingHypothesis_inhabits_addressed_target
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) (retained : List Nat)
    (result : ConstantHeadedFormula)
    {hypothesisLabel typecode variableName : String}
    {hypotheses : List HypothesisView}
    {actual : ConstantHeadedFormula}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances
      (.floating hypothesisLabel typecode variableName :: hypotheses)
      (actual :: actuals) (⟨variableName, actual⟩ :: substitution))
    (hypotheses_eq : assertion.hypotheses =
      .floating hypothesisLabel typecode variableName :: hypotheses)
    {parent : Nat} {parents : List Nat}
    {child : SourceGeneratedProvesTree source target actual}
    {children : SourceGeneratedProvesForest source target actuals}
    (resolved : ResolvesForest before.nodes (parent :: parents)
      (actual :: actuals) (.cons child children))
    (stack_eq : before.stack = retained ++ parent :: parents) :
    ∃ sourceOccurrence,
      ledger.occurrences[parent]? = some sourceOccurrence ∧
      normalStackRowAt context.proofOwner
          ((sourceAssertionAddressSegment context before scanner index assertion
            retained result).stackAddress retained.length)
          actual sourceOccurrence ∈
        sourceStackRows context.proofOwner before ledger ∧
      let segment := sourceAssertionAddressSegment context before scanner index
        assertion retained result
      let phase := normalAssertionFloatingPhaseSpaceAt context.scopeOwner
        context.proofOwner segment assertion.label 0 1
        assertion.hypotheses.length retained.length (retained.length + 1)
        retained.length hypothesisLabel typecode variableName actual.body
        sourceOccurrence
      let targetSpace := fireReflectiveSourceExecFact phase
        normalAssertionFloatingDirective
      (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
          (reflectiveSourceExecExactTargetNativeType targetSpace).pred ∧
        normalAssertionBindRowAt context.scopeOwner context.proofOwner segment
              assertion.label 1 (1 + hypotheses.length)
              (retained.length + 1) retained.length ∈ targetSpace ∧
          normalAssertionSubstitutionRowAt context.proofOwner
                segment.currentProof variableName actual.body ∈ targetSpace ∧
            normalAssertionChildRowAt context.proofOwner segment.currentProof
                0 sourceOccurrence ∈ targetSpace := by
  have hypothesisEndEq : assertion.hypotheses.length =
      1 + hypotheses.length := by
    rw [hypotheses_eq]
    simp only [List.length_cons]
    omega
  cases instances with
  | floating typecodeEqual tailInstances =>
      cases resolved with
      | cons node forest nodeLookup tailResolved =>
          obtain ⟨sourceOccurrence, occurrenceLookup⟩ :=
            occurrenceLedger_lookup_exists_of_node_lookup before ledger parent
              node nodeLookup
          have stackLookup : before.stack[retained.length]? = some parent := by
            rw [stack_eq]
            simp
          have rowMember := normalStackRow_mem_sourceStackRows
            context.proofOwner before ledger retained.length parent node
            sourceOccurrence stackLookup nodeLookup occurrenceLookup
          let segment := sourceAssertionAddressSegment context before scanner
            index assertion retained result
          have addressedRowMember :
              normalStackRowAt context.proofOwner
                  (segment.stackAddress retained.length)
                  node.formula
                  sourceOccurrence ∈
                sourceStackRows context.proofOwner before ledger := by
            simpa [segment, sourceAssertionAddressSegment,
              compressedResultSegment, normalResultContextAtSourceAssertion,
              MM2CompressedProofNormalResultRejoin.NormalResultContext.code,
              normalStackRowAt, normalStackRow, displayedProofOccurrence]
              using rowMember
          refine ⟨sourceOccurrence, occurrenceLookup, addressedRowMember, ?_⟩
          change node.formula.typecode = typecode at typecodeEqual
          subst typecode
          simpa [hypothesisEndEq] using
            (normalAssertionFloatingPhaseAt_inhabits_target_native_type
              context.scopeOwner context.proofOwner segment assertion.label 0 1
              assertion.hypotheses.length retained.length
              (retained.length + 1) retained.length hypothesisLabel
              node.formula.typecode variableName node.formula.body
              sourceOccurrence)

section AxiomAudit

#print axioms normalStackRow_mem_sourceStackRows
#print axioms occurrenceLedger_lookup_exists_of_node_lookup
#print axioms sourceFloatingHypothesis_inhabits_addressed_target

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofSourceFloatingHypothesis
