import Mettapedia.Languages.Metamath.MM2CompressedProofSourceFloatingHypothesis
import Mettapedia.Languages.Metamath.MM2NormalAssertionEssentialAddressed

/-!
# Source-bound compressed essential-hypothesis execution

This module reconstructs the first essential-hypothesis transition from the
source assertion instance, semantic substitution relation, resolved parent
stack, and occurrence ledger.  The target body-match trace and child
occurrence are consequences of source evidence rather than target inputs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSourceEssentialHypothesis

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionResultResume
open Mettapedia.Languages.Metamath.MM2CompressedProofSourceFloatingHypothesis
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
open Mettapedia.Languages.Metamath.MM2NormalAddressSegment
open Mettapedia.Languages.Metamath.MM2NormalAssertionEssentialAddressed
open Mettapedia.Languages.Metamath.MM2NormalAssertionFloatingAddressed
open Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK

/-- The head of an essential-match derivation is the exact formula
substitution judgment for the head essential hypothesis and actual. -/
theorem essentialMatches_head
    {substitution : FiniteSubstitution} {label : String}
    {formula actual : ConstantHeadedFormula}
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    (matchEvidence : EssentialMatches substitution
      (.essential label formula :: hypotheses) (actual :: actuals)) :
    FormulaSubstitutionSemantics substitution formula actual := by
  exact matchEvidence.1

/-- One source essential-hypothesis constructor, its semantic match, and one
resolved parent produce the exact compressed-address MM2 trace. -/
theorem sourceEssentialHypothesis_has_addressed_trace
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) (retained : List Nat)
    (result : ConstantHeadedFormula)
    {hypothesisLabel : String} {formula : ConstantHeadedFormula}
    {hypotheses : List HypothesisView}
    {actual : ConstantHeadedFormula}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances
      (.essential hypothesisLabel formula :: hypotheses)
      (actual :: actuals) substitution)
    (matchEvidence : EssentialMatches substitution
      (.essential hypothesisLabel formula :: hypotheses)
      (actual :: actuals))
    (hypotheses_eq : assertion.hypotheses =
      .essential hypothesisLabel formula :: hypotheses)
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
      AddressedEssentialHypothesisTrace context.scopeOwner context.proofOwner
        segment assertion.label 0 1 assertion.hypotheses.length retained.length
        (retained.length + 1) retained.length hypothesisLabel formula actual
        sourceOccurrence substitution := by
  have hypothesisEndEq : assertion.hypotheses.length =
      1 + hypotheses.length := by
    rw [hypotheses_eq]
    simp only [List.length_cons]
    omega
  cases instances with
  | essential typecodeEqual tailInstances =>
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
                  node.formula sourceOccurrence ∈
                sourceStackRows context.proofOwner before ledger := by
            simpa [segment, sourceAssertionAddressSegment,
              compressedResultSegment, normalResultContextAtSourceAssertion,
              MM2CompressedProofNormalResultRejoin.NormalResultContext.code,
              normalStackRowAt, normalStackRow, displayedProofOccurrence]
              using rowMember
          refine ⟨sourceOccurrence, occurrenceLookup, addressedRowMember, ?_⟩
          simpa [hypothesisEndEq] using
            (addressedEssentialHypothesisTrace_of_semantics context.scopeOwner
              context.proofOwner segment assertion.label 0 1
              assertion.hypotheses.length retained.length
              (retained.length + 1) retained.length hypothesisLabel formula
              node.formula sourceOccurrence substitution typecodeEqual
              (essentialMatches_head matchEvidence))

section AxiomAudit

#print axioms essentialMatches_head
#print axioms sourceEssentialHypothesis_has_addressed_trace

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofSourceEssentialHypothesis
