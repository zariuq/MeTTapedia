import Mettapedia.Languages.Metamath.MM2CompressedProofSourceEssentialHypothesis

/-!
# Source-bound ordered mandatory-hypothesis execution

Floating and essential hypotheses share one recursive addressed trace.  The
completed substitution remains fixed while the residual floating bindings
shrink, and each stack occurrence is reconstructed from the source parent
identity and occurrence ledger.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSourceMandatoryHypotheses

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
open Mettapedia.Languages.Metamath.MM2CompressedProofSourceEssentialHypothesis
open Mettapedia.Languages.Metamath.MM2CompressedProofSourceFloatingHypothesis
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
open Mettapedia.Languages.Metamath.MM2NormalAddressSegment
open Mettapedia.Languages.Metamath.MM2NormalAssertionEssentialAddressed
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

/-- Exact addressed target evidence for one floating hypothesis. -/
def AddressedFloatingHypothesisStep
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actual : ConstantHeadedFormula) (childOccurrence : Atom) : Prop :=
  let phase := normalAssertionFloatingPhaseSpaceAt scopeOwner proofOwner
    segment assertionLabel hypothesisPosition nextHypothesisPosition
    hypothesisEnd stackPosition nextStackPosition stackBase hypothesisLabel
    typecode variableName actual.body childOccurrence
  let target := fireReflectiveSourceExecFact phase
    normalAssertionFloatingDirective
  (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalAssertionBindRowAt scopeOwner proofOwner segment assertionLabel
          nextHypothesisPosition hypothesisEnd nextStackPosition stackBase ∈
        target ∧
      normalAssertionSubstitutionRowAt proofOwner segment.currentProof
            variableName actual.body ∈ target ∧
        normalAssertionChildRowAt proofOwner segment.currentProof
            hypothesisPosition childOccurrence ∈ target

theorem addressedFloatingHypothesisStep_of_typecode_eq
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actual : ConstantHeadedFormula) (childOccurrence : Atom)
    (typecodeEqual : actual.typecode = typecode) :
    AddressedFloatingHypothesisStep scopeOwner proofOwner segment
      assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
      stackPosition nextStackPosition stackBase hypothesisLabel typecode
      variableName actual childOccurrence := by
  rcases actual with ⟨actualTypecode, actualBody⟩
  change actualTypecode = typecode at typecodeEqual
  subst actualTypecode
  simpa only [AddressedFloatingHypothesisStep] using
    (normalAssertionFloatingPhaseAt_inhabits_target_native_type scopeOwner
      proofOwner segment assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode variableName actualBody
      childOccurrence)

/-- One ordered trace over all mandatory hypotheses.  Every occurrence and
stack row is tied to the source node list and the source-derived ledger. -/
inductive SourceAddressedMandatoryHypothesesTrace
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (segment : NormalAddressSegment)
    (assertionLabel : String) (hypothesisEnd stackBase : Nat)
    (completeSubstitution : FiniteSubstitution) :
    List HypothesisView → List ConstantHeadedFormula → List Nat →
      FiniteSubstitution → Nat → Nat → Prop where
  | nil (stackPosition : Nat) :
      SourceAddressedMandatoryHypothesesTrace context before ledger segment
        assertionLabel hypothesisEnd stackBase completeSubstitution
        [] [] [] [] hypothesisEnd stackPosition
  | floating {label typecode variableName : String}
      {actual : ConstantHeadedFormula}
      {hypotheses : List HypothesisView}
      {actuals : List ConstantHeadedFormula}
      {parent : Nat} {parents : List Nat}
      {residualSubstitution : FiniteSubstitution}
      (hypothesisPosition stackPosition : Nat)
      (typecodeEqual : actual.typecode = typecode)
      (bindingMember :
        ({ variableName, replacement := actual } : FormulaBinding) ∈
          completeSubstitution)
      (node : ProofNode source target) (formulaExact : node.formula = actual)
      (nodeLookup : before.nodes[parent]? = some node)
      (occurrence : Atom)
      (occurrenceLookup : ledger.occurrences[parent]? = some occurrence)
      (stackRow : normalStackRowAt context.proofOwner
          (segment.stackAddress stackPosition) actual occurrence ∈
        sourceStackRows context.proofOwner before ledger)
      (step : AddressedFloatingHypothesisStep context.scopeOwner
        context.proofOwner segment assertionLabel hypothesisPosition
        (hypothesisPosition + 1) hypothesisEnd stackPosition
        (stackPosition + 1) stackBase label typecode variableName actual
        occurrence)
      (tail : SourceAddressedMandatoryHypothesesTrace context before ledger
        segment assertionLabel hypothesisEnd stackBase completeSubstitution
        hypotheses actuals parents residualSubstitution
        (hypothesisPosition + 1) (stackPosition + 1)) :
      SourceAddressedMandatoryHypothesesTrace context before ledger segment
        assertionLabel hypothesisEnd stackBase completeSubstitution
        (.floating label typecode variableName :: hypotheses)
        (actual :: actuals) (parent :: parents)
        ({ variableName, replacement := actual } :: residualSubstitution)
        hypothesisPosition stackPosition
  | essential {label : String} {formula actual : ConstantHeadedFormula}
      {hypotheses : List HypothesisView}
      {actuals : List ConstantHeadedFormula}
      {parent : Nat} {parents : List Nat}
      {residualSubstitution : FiniteSubstitution}
      (hypothesisPosition stackPosition : Nat)
      (typecodeEqual : actual.typecode = formula.typecode)
      (matchSemantics :
        FormulaSubstitutionSemantics completeSubstitution formula actual)
      (node : ProofNode source target) (formulaExact : node.formula = actual)
      (nodeLookup : before.nodes[parent]? = some node)
      (occurrence : Atom)
      (occurrenceLookup : ledger.occurrences[parent]? = some occurrence)
      (stackRow : normalStackRowAt context.proofOwner
          (segment.stackAddress stackPosition) actual occurrence ∈
        sourceStackRows context.proofOwner before ledger)
      (step : AddressedEssentialHypothesisTrace context.scopeOwner
        context.proofOwner segment assertionLabel hypothesisPosition
        (hypothesisPosition + 1) hypothesisEnd stackPosition
        (stackPosition + 1) stackBase label formula actual occurrence
        completeSubstitution)
      (tail : SourceAddressedMandatoryHypothesesTrace context before ledger
        segment assertionLabel hypothesisEnd stackBase completeSubstitution
        hypotheses actuals parents residualSubstitution
        (hypothesisPosition + 1) (stackPosition + 1)) :
      SourceAddressedMandatoryHypothesesTrace context before ledger segment
        assertionLabel hypothesisEnd stackBase completeSubstitution
        (.essential label formula :: hypotheses) (actual :: actuals)
        (parent :: parents) residualSubstitution hypothesisPosition
        stackPosition

private theorem sourceAddressedMandatoryHypothesesTrace_of_semantics_aux
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) (retained : List Nat)
    (result : ConstantHeadedFormula)
    (completeSubstitution : FiniteSubstitution)
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {residualSubstitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals residualSubstitution)
    (essentialChecks :
      EssentialMatches completeSubstitution hypotheses actuals)
    {parents : List Nat}
    {children : SourceGeneratedProvesForest source target actuals}
    (resolved : ResolvesForest before.nodes parents actuals children)
    (residualSubset : ∀ binding, binding ∈ residualSubstitution →
      binding ∈ completeSubstitution)
    (hypothesisPosition : Nat) (stackPrefix : List Nat)
    (positionEnd : hypothesisPosition + hypotheses.length =
      assertion.hypotheses.length)
    (stackExact : before.stack = stackPrefix ++ parents) :
    SourceAddressedMandatoryHypothesesTrace context before ledger
      (sourceAssertionAddressSegment context before scanner index assertion
        retained result)
      assertion.label assertion.hypotheses.length retained.length
      completeSubstitution hypotheses actuals parents residualSubstitution
      hypothesisPosition stackPrefix.length := by
  induction instances generalizing hypothesisPosition stackPrefix parents with
  | nil =>
      cases resolved
      simp only [List.length_nil, Nat.add_zero] at positionEnd
      subst hypothesisPosition
      exact SourceAddressedMandatoryHypothesesTrace.nil stackPrefix.length
  | @floating label typecode variableName actual hypotheses actuals
      residualSubstitution typecodeEqual tailInstances inductionHypothesis =>
      cases resolved with
      | @cons parent parents formulas node forest nodeLookup tailResolved =>
          obtain ⟨occurrence, occurrenceLookup⟩ :=
            occurrenceLedger_lookup_exists_of_node_lookup before ledger _ node
              nodeLookup
          have stackLookup : before.stack[stackPrefix.length]? =
              some parent := by
            rw [stackExact]
            simp
          have rowMember := normalStackRow_mem_sourceStackRows
            context.proofOwner before ledger stackPrefix.length parent node
            occurrence stackLookup nodeLookup occurrenceLookup
          let segment := sourceAssertionAddressSegment context before scanner
            index assertion retained result
          have addressedRowMember :
              normalStackRowAt context.proofOwner
                  (segment.stackAddress stackPrefix.length)
                  node.formula occurrence ∈
                sourceStackRows context.proofOwner before ledger := by
            simpa [segment, sourceAssertionAddressSegment,
              compressedResultSegment, normalResultContextAtSourceAssertion,
              MM2CompressedProofNormalResultRejoin.NormalResultContext.code,
              normalStackRowAt, normalStackRow, displayedProofOccurrence]
              using rowMember
          have bindingMember :
              ({ variableName, replacement := node.formula } :
                FormulaBinding) ∈ completeSubstitution :=
            residualSubset _ (by simp)
          have tailSubset : ∀ binding, binding ∈ residualSubstitution →
              binding ∈ completeSubstitution := by
            intro binding member
            exact residualSubset binding (by simp [member])
          have tailEnd : hypothesisPosition + 1 + hypotheses.length =
              assertion.hypotheses.length := by
            simp only [List.length_cons] at positionEnd
            omega
          have tailStackExact : before.stack =
              (stackPrefix ++ [parent]) ++ parents := by
            rw [stackExact]
            simp [List.append_assoc]
          have tailTrace := inductionHypothesis essentialChecks tailResolved
            tailSubset (hypothesisPosition + 1) (stackPrefix ++ [parent])
            tailEnd tailStackExact
          exact SourceAddressedMandatoryHypothesesTrace.floating
            hypothesisPosition stackPrefix.length typecodeEqual bindingMember
            node rfl nodeLookup occurrence
            occurrenceLookup addressedRowMember
            (addressedFloatingHypothesisStep_of_typecode_eq context.scopeOwner
              context.proofOwner segment assertion.label hypothesisPosition
              (hypothesisPosition + 1) assertion.hypotheses.length
              stackPrefix.length (stackPrefix.length + 1) retained.length label
              typecode variableName node.formula occurrence typecodeEqual)
            (by simpa using tailTrace)
  | @essential label formula actual hypotheses actuals residualSubstitution
      typecodeEqual tailInstances inductionHypothesis =>
      cases resolved with
      | @cons parent parents formulas node forest nodeLookup tailResolved =>
          obtain ⟨occurrence, occurrenceLookup⟩ :=
            occurrenceLedger_lookup_exists_of_node_lookup before ledger _ node
              nodeLookup
          have stackLookup : before.stack[stackPrefix.length]? =
              some parent := by
            rw [stackExact]
            simp
          have rowMember := normalStackRow_mem_sourceStackRows
            context.proofOwner before ledger stackPrefix.length parent node
            occurrence stackLookup nodeLookup occurrenceLookup
          let segment := sourceAssertionAddressSegment context before scanner
            index assertion retained result
          have addressedRowMember :
              normalStackRowAt context.proofOwner
                  (segment.stackAddress stackPrefix.length)
                  node.formula occurrence ∈
                sourceStackRows context.proofOwner before ledger := by
            simpa [segment, sourceAssertionAddressSegment,
              compressedResultSegment, normalResultContextAtSourceAssertion,
              MM2CompressedProofNormalResultRejoin.NormalResultContext.code,
              normalStackRowAt, normalStackRow, displayedProofOccurrence]
              using rowMember
          have tailEnd : hypothesisPosition + 1 + hypotheses.length =
              assertion.hypotheses.length := by
            simp only [List.length_cons] at positionEnd
            omega
          have tailStackExact : before.stack =
              (stackPrefix ++ [parent]) ++ parents := by
            rw [stackExact]
            simp [List.append_assoc]
          have tailTrace := inductionHypothesis essentialChecks.2 tailResolved
            residualSubset (hypothesisPosition + 1)
            (stackPrefix ++ [parent]) tailEnd tailStackExact
          exact SourceAddressedMandatoryHypothesesTrace.essential
            hypothesisPosition stackPrefix.length typecodeEqual
            essentialChecks.1 node rfl nodeLookup occurrence
            occurrenceLookup addressedRowMember
            (addressedEssentialHypothesisTrace_of_semantics context.scopeOwner
              context.proofOwner segment assertion.label hypothesisPosition
              (hypothesisPosition + 1) assertion.hypotheses.length
              stackPrefix.length (stackPrefix.length + 1) retained.length label
              formula node.formula occurrence completeSubstitution
              typecodeEqual essentialChecks.1)
            (by simpa using tailTrace)

/-- Independent mandatory-hypothesis semantics and the resolved source forest
construct the complete ordered addressed target trace. -/
theorem sourceAddressedMandatoryHypothesesTrace_of_semantics
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) (retained : List Nat)
    (result : ConstantHeadedFormula)
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    (substitution : FiniteSubstitution)
    (instances : HypothesisInstances hypotheses actuals substitution)
    (essentialChecks : EssentialMatches substitution hypotheses actuals)
    {parents : List Nat}
    {children : SourceGeneratedProvesForest source target actuals}
    (resolved : ResolvesForest before.nodes parents actuals children)
    (hypothesesExact : assertion.hypotheses = hypotheses)
    (stackExact : before.stack = retained ++ parents) :
    SourceAddressedMandatoryHypothesesTrace context before ledger
      (sourceAssertionAddressSegment context before scanner index assertion
        retained result)
      assertion.label assertion.hypotheses.length retained.length substitution
      hypotheses actuals parents substitution 0 retained.length := by
  apply sourceAddressedMandatoryHypothesesTrace_of_semantics_aux context before
    ledger scanner index assertion retained result substitution instances
    essentialChecks resolved (fun _ member => member) 0 retained
  · simp [hypothesesExact]
  · exact stackExact

/-- A complete addressed source trace reconstructs the exact floating-instance
relation and every essential semantic match; the target trace invents neither. -/
theorem SourceAddressedMandatoryHypothesesTrace.reflects_semantics
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {before : MachineState source target}
    {ledger : NodeOccurrenceLedger before} {segment : NormalAddressSegment}
    {assertionLabel : String} {hypothesisEnd stackBase : Nat}
    {completeSubstitution : FiniteSubstitution}
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula} {parents : List Nat}
    {residualSubstitution : FiniteSubstitution}
    {hypothesisPosition stackPosition : Nat}
    (trace : SourceAddressedMandatoryHypothesesTrace context before ledger
      segment assertionLabel hypothesisEnd stackBase completeSubstitution
      hypotheses actuals parents residualSubstitution hypothesisPosition
      stackPosition) :
    HypothesisInstances hypotheses actuals residualSubstitution ∧
      EssentialMatches completeSubstitution hypotheses actuals := by
  induction trace with
  | nil => exact ⟨HypothesisInstances.nil, trivial⟩
  | floating hypothesisPosition stackPosition typecodeEqual bindingMember node
      formulaExact nodeLookup occurrence occurrenceLookup stackRow step tail
      inductionHypothesis =>
      exact ⟨HypothesisInstances.floating typecodeEqual inductionHypothesis.1,
        inductionHypothesis.2⟩
  | essential hypothesisPosition stackPosition typecodeEqual matchSemantics
      node formulaExact nodeLookup occurrence occurrenceLookup stackRow step
      tail inductionHypothesis =>
      exact ⟨HypothesisInstances.essential typecodeEqual inductionHypothesis.1,
        ⟨matchSemantics, inductionHypothesis.2⟩⟩

section AxiomAudit

#print axioms addressedFloatingHypothesisStep_of_typecode_eq
#print axioms sourceAddressedMandatoryHypothesesTrace_of_semantics
#print axioms SourceAddressedMandatoryHypothesesTrace.reflects_semantics

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofSourceMandatoryHypotheses
