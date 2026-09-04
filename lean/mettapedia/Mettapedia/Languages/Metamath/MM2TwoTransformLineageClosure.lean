import Mettapedia.Languages.Metamath.MM2TwoTransformProgram
import Mettapedia.Languages.Metamath.MM2VerifierLineageOrigin
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutableSchemaParserBridge

/-!
# Executable-lineage closure for the two Metamath-to-MM2 transforms

The verifier transform contributes the complete finite executable-schema
inventory.  The source-data transform is checked recursively against that
inventory, including proof packets, action plans, DV plans, and assertion
publication rows.  Their actual concatenation therefore enters rule-scoped
MORK execution under one finite-lineage invariant, which is preserved for
arbitrary fuel.  Groundness and fixed expression heads remain available as
independent factors.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2TwoTransformLineageClosure

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTOperations
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofData
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2NormalLabelInventory
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2SourceAssertionExecution
open Mettapedia.Languages.Metamath.MM2SourceAssertionPlan
open Mettapedia.Languages.Metamath.MM2SourceAssertionPublication
open Mettapedia.Languages.Metamath.MM2SourceDVOccurrenceLookup
open Mettapedia.Languages.Metamath.MM2SourceDVPairPlan
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceEssentialDeclaration
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.MM2SourceScopeExecution
open Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
open Mettapedia.Languages.Metamath.MM2SourceVariableTypecodeLookup
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.MM2TwoTransformProgram
open Mettapedia.Languages.Metamath.MM2VerifierExecutableOrigin
open Mettapedia.Languages.Metamath.MM2VerifierLineageOrigin
open Mettapedia.Languages.Metamath.MM2VerifierProgram
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

/-- The source owner is admissible at the two-transform boundary when it is
ground and passes the same recursive executable-schema check as the generated
verifier.  Owners are data, but making this condition explicit prevents an
unusual structured owner from becoming a second code-admission channel. -/
def SourceOwnerLineageAuthorized (owner : Atom) : Prop :=
  isGroundAtom owner = true ∧
    executableSchemaTemplateSafe verifierExecutableRawFacts owner = true

/-- Source-side rows are constructed under the executable inventory emitted by
the fixed verifier transformation. -/
private abbrev SourceDataSchemaSafe (atom : Atom) : Bool :=
  executableSchemaTemplateSafe verifierExecutableRawFacts atom

/-- The executable-schema checker is the constructive introduction rule for
the semantic lineage predicate used by rule-scoped MORK execution. -/
private theorem sourceDataSchemaSafe_authorized {atom : Atom}
    (safe : SourceDataSchemaSafe atom) :
    VerifierExecutableLineageAuthorized atom := by
  exact executableSchemaTemplateSafe_authorized verifierExecutableRawFacts
    atom (by simpa using safe)

@[simp] private theorem natAtom_schemaSafe (value : Nat) :
    SourceDataSchemaSafe (natAtom value) := by
  simp [SourceDataSchemaSafe, natAtom, executableSchemaTemplateSafe,
    executableSchemaTemplatesSafe, extractRawExecFact]

@[simp] private theorem charListAtom_schemaSafe (values : List Char) :
    SourceDataSchemaSafe (charListAtom values) := by
  induction values with
  | nil =>
      simp [SourceDataSchemaSafe, charListAtom,
        executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
        extractRawExecFact]
  | cons head tail induction =>
      simp [SourceDataSchemaSafe, charListAtom, charAtom, natAtom,
        executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
        extractRawExecFact, induction]

@[simp] private theorem stringAtom_schemaSafe (value : String) :
    SourceDataSchemaSafe (stringAtom value) := by
  simp [SourceDataSchemaSafe, stringAtom, executableSchemaTemplateSafe,
    executableSchemaTemplatesSafe, extractRawExecFact]

@[simp] private theorem runtimeSymAtom_schemaSafe
    (symbol : Metamath.Verify.Sym) :
    SourceDataSchemaSafe (runtimeSymAtom symbol) := by
  cases symbol <;>
    simp [SourceDataSchemaSafe, runtimeSymAtom,
      executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
      extractRawExecFact]

@[simp] private theorem listAtom_schemaSafe {Source : Type}
    (encode : Source → Atom)
    (encodedSafe : ∀ value, SourceDataSchemaSafe (encode value)) :
    ∀ values, SourceDataSchemaSafe (listAtom encode values)
  | [] => by
      simp [SourceDataSchemaSafe, listAtom, executableSchemaTemplateSafe,
        executableSchemaTemplatesSafe, extractRawExecFact]
  | head :: tail => by
      simp [SourceDataSchemaSafe, listAtom, executableSchemaTemplateSafe,
        executableSchemaTemplatesSafe, extractRawExecFact,
        encodedSafe head, listAtom_schemaSafe encode encodedSafe tail]

@[simp] private theorem locatedByteSpanAtom_schemaSafe
    (span :
      Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan) :
    SourceDataSchemaSafe (locatedByteSpanAtom span) := by
  simp [SourceDataSchemaSafe, locatedByteSpanAtom,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe]

@[simp] private theorem locatedNameAtom_schemaSafe
    (name :
      Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.LocatedName) :
    SourceDataSchemaSafe (locatedNameAtom name) := by
  simp [SourceDataSchemaSafe, locatedNameAtom,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe]

@[simp] private theorem locatedTokenAtom_schemaSafe
    (token :
      Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.LocatedToken) :
    SourceDataSchemaSafe (locatedTokenAtom token) := by
  have byteSafe : ∀ byte, SourceDataSchemaSafe (byteAtom byte) := by
    intro byte
    exact natAtom_schemaSafe byte.toNat
  simp [SourceDataSchemaSafe, locatedTokenAtom,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
    listAtom_schemaSafe, byteSafe]

@[simp] private theorem proofPayloadAtom_schemaSafe
    (proof :
      Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.ProofPayload) :
    SourceDataSchemaSafe (proofPayloadAtom proof) := by
  cases proof <;>
    simp [SourceDataSchemaSafe, proofPayloadAtom,
      executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
      listAtom_schemaSafe]

@[simp] private theorem rawStatementAtom_schemaSafe
    (statement :
      Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.RawStatement) :
    SourceDataSchemaSafe (rawStatementAtom statement) := by
  cases statement <;>
    simp [SourceDataSchemaSafe, rawStatementAtom,
      executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
      listAtom_schemaSafe]

@[simp] private theorem formulaAtom_schemaSafe
    (formula : ConstantHeadedFormula) :
    SourceDataSchemaSafe (formulaAtom formula) := by
  simp [SourceDataSchemaSafe, formulaAtom, executableSchemaTemplateSafe,
    executableSchemaTemplatesSafe, listAtom_schemaSafe]

@[simp] private theorem hypothesisAtom_schemaSafe
    (hypothesis : HypothesisView) :
    SourceDataSchemaSafe (hypothesisAtom hypothesis) := by
  cases hypothesis <;>
    simp [SourceDataSchemaSafe, hypothesisAtom,
      executableSchemaTemplateSafe, executableSchemaTemplatesSafe]

@[simp] private theorem stringPairAtom_schemaSafe (pair : String × String) :
    SourceDataSchemaSafe (stringPairAtom pair) := by
  simp [SourceDataSchemaSafe, stringPairAtom, executableSchemaTemplateSafe,
    executableSchemaTemplatesSafe]

@[simp] private theorem sourceFrameAtom_schemaSafe (frame : SourceFrame) :
    SourceDataSchemaSafe (sourceFrameAtom frame) := by
  simp [SourceDataSchemaSafe, sourceFrameAtom,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
    listAtom_schemaSafe]

@[simp] private theorem sourceAssertionAtom_schemaSafe
    (assertion : SourceAssertion) :
    SourceDataSchemaSafe (sourceAssertionAtom assertion) := by
  simp [SourceDataSchemaSafe, sourceAssertionAtom,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
    listAtom_schemaSafe]

private theorem assertionExecutionRowsFor_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (position : Nat) (assertion : SourceAssertion) :
    (assertionExecutionRowsFor owner position assertion).all
      SourceDataSchemaSafe = true := by
  simp [assertionExecutionRowsFor, assertionHeaderRow,
    assertionHypothesisRows, assertionHypothesisRow,
    assertionHypothesisSuccessorRows, assertionHypothesisSuccessorRow,
    assertionDVHeaderRow, assertionDVPairRows, assertionDVPairRow,
    assertionDVSuccessorRows, assertionResultRow, SourceDataSchemaSafe,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe, ownerSafe]
  constructor <;>
    intro row rowPosition inBounds equal <;>
    subst row <;>
    simp [executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
      ownerSafe]

@[simp] private theorem linkedRow_schemaSafe
    (family : String) (owner payload : Atom) (position nextPosition : Nat)
    (ownerSafe : SourceDataSchemaSafe owner)
    (payloadSafe : SourceDataSchemaSafe payload) :
    SourceDataSchemaSafe
      (linkedRow family owner position nextPosition payload) := by
  simp [SourceDataSchemaSafe, linkedRow, executableSchemaTemplateSafe,
    executableSchemaTemplatesSafe, ownerSafe, payloadSafe]

private theorem linkedRows_all_schemaSafe {Source : Type}
    (family : String) (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (encode : Source → Atom) (values : List Source)
    (payloadsSafe : values.all
      (fun value => SourceDataSchemaSafe (encode value)) = true) :
    (linkedRows family owner encode values).all SourceDataSchemaSafe = true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [mem_linkedRows_iff] at member
  obtain ⟨position, inBounds, rfl⟩ := member
  apply linkedRow_schemaSafe
  · exact ownerSafe
  · exact (List.all_eq_true.mp payloadsSafe) values[position]
      (List.get_mem values ⟨position, inBounds⟩)

@[simp] private theorem indexedRow_schemaSafe
    (family : String) (owner payload : Atom) (position : Nat)
    (ownerSafe : SourceDataSchemaSafe owner)
    (payloadSafe : SourceDataSchemaSafe payload) :
    SourceDataSchemaSafe (indexedRow family owner position payload) := by
  simp [SourceDataSchemaSafe, indexedRow, executableSchemaTemplateSafe,
    executableSchemaTemplatesSafe, ownerSafe, payloadSafe]

private theorem indexedRows_all_schemaSafe {Source : Type}
    (family : String) (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (encode : Source → Atom) (values : List Source)
    (payloadsSafe : values.all
      (fun value => SourceDataSchemaSafe (encode value)) = true) :
    (indexedRows family owner encode values).all SourceDataSchemaSafe = true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [mem_indexedRows_iff] at member
  obtain ⟨position, inBounds, rfl⟩ := member
  apply indexedRow_schemaSafe
  · exact ownerSafe
  · exact (List.all_eq_true.mp payloadsSafe) values[position]
      (List.get_mem values ⟨position, inBounds⟩)

@[simp] private theorem indexSuccessorRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner) (count : Nat) :
    (indexSuccessorRows owner count).all SourceDataSchemaSafe = true := by
  simp [indexSuccessorRows, SourceDataSchemaSafe,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe, ownerSafe]

@[simp] private theorem sourceActionOwner_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner) (position : Nat) :
    SourceDataSchemaSafe (sourceActionOwner owner position) := by
  simp [sourceActionOwner, SourceDataSchemaSafe,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe, ownerSafe]

@[simp] private theorem sourceProofOwnerAtom_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner) (position : Nat) :
    SourceDataSchemaSafe (sourceProofOwnerAtom owner position) := by
  simp [sourceProofOwnerAtom, SourceDataSchemaSafe,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe, ownerSafe]

@[simp] private theorem compressedIndexCodeAtom_schemaSafe
    (reversePrefixDigits : List Nat) (terminalDigit : Nat) :
    SourceDataSchemaSafe
      (compressedIndexCodeAtom reversePrefixDigits terminalDigit) := by
  simp [compressedIndexCodeAtom, SourceDataSchemaSafe,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
    listAtom_schemaSafe]

@[simp] private theorem compressedIndexCode_atom_schemaSafe
    (code : CompressedIndexCode) : SourceDataSchemaSafe code.atom := by
  simp [CompressedIndexCode.atom]

private theorem compressedIndexSuccessorRowsFrom_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (count : Nat) (current : CompressedIndexCode) :
    (compressedIndexSuccessorRowsFrom owner count current).all
      SourceDataSchemaSafe = true := by
  induction count generalizing current with
  | zero => rfl
  | succ count induction =>
      simp [compressedIndexSuccessorRowsFrom, compressedIndexSuccessorRow,
        SourceDataSchemaSafe, executableSchemaTemplateSafe,
        executableSchemaTemplatesSafe, ownerSafe, induction]

private theorem compressedIndexSuccessorRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner) (count : Nat) :
    (compressedIndexSuccessorRows owner count).all
      SourceDataSchemaSafe = true := by
  exact compressedIndexSuccessorRowsFrom_all_schemaSafe owner ownerSafe count
    CompressedIndexCode.zero

private theorem compressedNormalStackSuccessorRows_all_schemaSafe
    (proofOwner : Atom) (ownerSafe : SourceDataSchemaSafe proofOwner)
    (count : Nat) :
    (compressedNormalStackSuccessorRows proofOwner count).all
      SourceDataSchemaSafe = true := by
  simp [compressedNormalStackSuccessorRows, SourceDataSchemaSafe,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe, ownerSafe]

private theorem proofInputRows_all_schemaSafe
    (scopeOwner proofOwner : Atom)
    (scopeSafe : SourceDataSchemaSafe scopeOwner)
    (proofSafe : SourceDataSchemaSafe proofOwner)
    (proof : ProofInput) :
    (proofInputRows scopeOwner proofOwner proof).all
      SourceDataSchemaSafe = true := by
  cases proof with
  | normal theoremLabel formula proofLabels =>
      have labelRowsSafe := linkedRows_all_schemaSafe "normal-proof-label"
        proofOwner proofSafe stringAtom proofLabels (by simp)
      simp [proofInputRows, ProofInputTables.rows, proofInputTables,
        labelRowsSafe, indexSuccessorRows_all_schemaSafe, SourceDataSchemaSafe,
        executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
        scopeSafe, proofSafe]
  | compressed theoremLabel formula header body =>
      have headerRowsSafe := indexedRows_all_schemaSafe
        "compressed-header-label" proofOwner proofSafe stringAtom header
        (by simp)
      have wordSafe : ∀ word : List UInt8,
          SourceDataSchemaSafe (compressedWordAtom word) := by
        intro word
        simp [compressedWordAtom, uint8Atom]
      have bodyRowsSafe := indexedRows_all_schemaSafe
        "compressed-body-word" proofOwner proofSafe compressedWordAtom body
        (by simp [wordSafe])
      simp [proofInputRows, ProofInputTables.rows, proofInputTables,
        headerRowsSafe, bodyRowsSafe, indexSuccessorRows_all_schemaSafe,
        SourceDataSchemaSafe, executableSchemaTemplateSafe,
        executableSchemaTemplatesSafe, scopeSafe, proofSafe]

@[simp] private theorem normalLabelEntryAtom_schemaSafe
    (entry : Mettapedia.GSLT.FiniteOccurrenceLookup.Entry String
      NormalLabelKind) :
    SourceDataSchemaSafe (normalLabelEntryAtom entry) := by
  rcases entry with ⟨key, kind⟩
  cases kind <;>
    simp [normalLabelEntryAtom, normalLabelKindAtom, SourceDataSchemaSafe,
      executableSchemaTemplateSafe, executableSchemaTemplatesSafe]

private theorem normalLabelInventoryRows_all_schemaSafe
    (proofOwner : Atom) (ownerSafe : SourceDataSchemaSafe proofOwner)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState) :
    (normalLabelInventoryRows proofOwner state).all
      SourceDataSchemaSafe = true := by
  simp [normalLabelInventoryRows, normalLabelCandidateRows,
    normalLabelCandidateRow, normalLabelFrontierRow, linkedRow,
    SourceDataSchemaSafe, executableSchemaTemplateSafe,
    executableSchemaTemplatesSafe, ownerSafe]

@[simp] private theorem compressedHeaderInputAtom_schemaSafe
    (input : CompressedHeaderInput) :
    SourceDataSchemaSafe (compressedHeaderInputAtom input) := by
  cases input <;>
    simp [compressedHeaderInputAtom, SourceDataSchemaSafe,
      executableSchemaTemplateSafe, executableSchemaTemplatesSafe]

private theorem compressedHeaderRows_all_schemaSafe
    (proofOwner : Atom) (ownerSafe : SourceDataSchemaSafe proofOwner)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (formula : ConstantHeadedFormula) (explicitLabels : List String) :
    (compressedHeaderRows proofOwner state formula explicitLabels).all
      SourceDataSchemaSafe = true := by
  apply linkedRows_all_schemaSafe
  · exact ownerSafe
  · simp

private theorem compressedBodyRows_all_schemaSafe
    (proofOwner : Atom) (ownerSafe : SourceDataSchemaSafe proofOwner)
    (bodyWords : List (List UInt8)) :
    (compressedBodyRows proofOwner bodyWords).all
      SourceDataSchemaSafe = true := by
  apply indexedRows_all_schemaSafe
  · exact ownerSafe
  · apply List.all_eq_true.mpr
    intro word _
    simp [compressedWordAtom, uint8Atom]

@[simp] private theorem compressedDerivedOwner_schemaSafe
    (tag : String) (proofOwner : Atom)
    (ownerSafe : SourceDataSchemaSafe proofOwner) (tagNe : tag ≠ "exec") :
    SourceDataSchemaSafe (.expression [.symbol tag, proofOwner]) := by
  simp [SourceDataSchemaSafe, executableSchemaTemplateSafe,
    executableSchemaTemplatesSafe, ownerSafe, tagNe]

private theorem transformedCompressedProofData_rows_all_schemaSafe
    (scopeOwner proofOwner : Atom)
    (scopeSafe : SourceDataSchemaSafe scopeOwner)
    (proofSafe : SourceDataSchemaSafe proofOwner)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8)) :
    (transformCompressedProofData scopeOwner proofOwner state theoremLabel
      formula explicitLabels bodyWords).rows.all SourceDataSchemaSafe = true := by
  have headerSafe := compressedHeaderRows_all_schemaSafe proofOwner proofSafe
    state formula explicitLabels
  have bodySafe := compressedBodyRows_all_schemaSafe proofOwner proofSafe
    bodyWords
  have heapOwnerSafe : SourceDataSchemaSafe (compressedHeapOwner proofOwner) := by
    simp [compressedHeapOwner, proofSafe]
  have nodeOwnerSafe : SourceDataSchemaSafe (compressedNodeOwner proofOwner) := by
    simp [compressedNodeOwner, proofSafe]
  have stackOwnerSafe : SourceDataSchemaSafe (compressedStackOwner proofOwner) := by
    simp [compressedStackOwner, proofSafe]
  have heapSafe := compressedIndexSuccessorRows_all_schemaSafe
    (compressedHeapOwner proofOwner) heapOwnerSafe
    (compressedHeapCapacity state formula explicitLabels bodyWords)
  have nodeSafe := compressedIndexSuccessorRows_all_schemaSafe
    (compressedNodeOwner proofOwner) nodeOwnerSafe
    (compressedNodeCapacity state formula bodyWords)
  have stackSafe := compressedIndexSuccessorRows_all_schemaSafe
    (compressedStackOwner proofOwner) stackOwnerSafe
    (compressedStackCapacity bodyWords)
  have normalStackSafe := compressedNormalStackSuccessorRows_all_schemaSafe
    proofOwner proofSafe (compressedStackCapacity bodyWords)
  simp [CompressedProofDataArtifact.rows, transformCompressedProofData,
    headerSafe, bodySafe, heapSafe, nodeSafe, stackSafe, normalStackSafe,
    indexSuccessorRows_all_schemaSafe, SourceDataSchemaSafe,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
    scopeSafe, proofSafe]

private theorem proofRuntimeRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState) :
    (proofRuntimeRows owner state).all SourceDataSchemaSafe = true := by
  simp [proofRuntimeRows, hypothesisLookupRows, hypothesisLookupRow,
    normalExecutionRows, callerDVRows, callerDVRowsOfPairs,
    callerDVRowsForPair, callerDVRow, assertionExecutionRows,
    SourceDataSchemaSafe, executableSchemaTemplateSafe,
    executableSchemaTemplatesSafe, ownerSafe]
  intro rows position inBounds equal
  subst rows
  exact List.all_eq_true.mp
    (assertionExecutionRowsFor_schemaSafe owner ownerSafe position
      state.assertions[position])

private theorem runtimeAction_payload_schemaSafe_of_delta
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (before after : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (action : RuntimeAction)
    (member : action ∈ sourceStateRuntimeDelta owner before after) :
    SourceDataSchemaSafe action.payload := by
  have classified := runtimeAction_payload_mem_of_mem_runtimeRowDelta action
    (proofRuntimeRows owner before) (proofRuntimeRows owner after) member
  rcases classified with beforeMember | afterMember
  · exact (List.all_eq_true.mp
      (proofRuntimeRows_all_schemaSafe owner ownerSafe before)) _ beforeMember
  · exact (List.all_eq_true.mp
      (proofRuntimeRows_all_schemaSafe owner ownerSafe after)) _ afterMember

private theorem statementActionPlan_actions_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (position : Nat)
    (before after : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (statement : RawStatement) (obligations : List TheoremObligation) :
    (statementActionPlan owner position before after statement obligations).actions.all
      (fun action => SourceDataSchemaSafe action.payload) = true := by
  apply List.all_eq_true.mpr
  intro action member
  exact runtimeAction_payload_schemaSafe_of_delta owner ownerSafe before after
    action member

private theorem buildSourceActionPlansFrom_actions_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (position : Nat)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (statements : List RawStatement)
    (final : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (plans : List StatementActionPlan)
    (built : buildSourceActionPlansFrom owner position state statements =
      .ok (final, plans)) :
    plans.all (fun plan => plan.actions.all
      (fun action => SourceDataSchemaSafe action.payload)) = true := by
  induction statements generalizing position state final plans with
  | nil =>
      simp [buildSourceActionPlansFrom] at built
      obtain ⟨rfl, rfl⟩ := built
      rfl
  | cons statement statements induction =>
      simp only [buildSourceActionPlansFrom] at built
      cases applied : applyStatement state statement with
      | rejected rejection => simp [applied] at built
      | ok pair =>
          obtain ⟨next, obligations⟩ := pair
          simp only [applied] at built
          cases recursive :
              buildSourceActionPlansFrom owner (position + 1) next statements with
          | rejected rejection => simp [recursive] at built
          | ok result =>
              obtain ⟨recursiveFinal, recursivePlans⟩ := result
              simp only [recursive] at built
              obtain ⟨rfl, rfl⟩ := FoldResult.ok.inj built
              have restSafe :=
                induction (position := position + 1) (state := next)
                  (final := final) (plans := recursivePlans) recursive
              simpa only [List.all_cons,
                statementActionPlan_actions_all_schemaSafe owner ownerSafe,
                Bool.true_and] using restSafe

private theorem admitted_actions_all_schemaSafe
    {owner : Atom} (ownerSafe : SourceDataSchemaSafe owner)
    {statements : List RawStatement}
    (input : AdmittedSourceActionPlans owner statements) :
    input.plans.all (fun plan => plan.actions.all
      (fun action => SourceDataSchemaSafe action.payload)) = true := by
  apply buildSourceActionPlansFrom_actions_all_schemaSafe owner ownerSafe 0
    Mettapedia.Languages.Metamath.SourceGSLTState.initialState statements
    input.finalState input.plans
  simpa [buildSourceActionPlans] using input.exact

@[simp] private theorem runtimeActionAtom_schemaSafe (action : RuntimeAction)
    (payloadSafe : SourceDataSchemaSafe action.payload) :
    SourceDataSchemaSafe (runtimeActionAtom action) := by
  cases action <;>
    simp_all [RuntimeAction.payload, runtimeActionAtom, SourceDataSchemaSafe]

private theorem runtimeActionRowsFrom_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (position : Nat) (actions : List RuntimeAction)
    (actionsSafe : actions.all
      (fun action => SourceDataSchemaSafe action.payload) = true) :
    (runtimeActionRowsFrom owner position actions).all
      SourceDataSchemaSafe = true := by
  induction actions generalizing position with
  | nil => rfl
  | cons action actions induction =>
      simp only [List.all_cons, Bool.and_eq_true] at actionsSafe
      simp [runtimeActionRowsFrom, linkedRow_schemaSafe, ownerSafe,
        runtimeActionAtom_schemaSafe action actionsSafe.1,
        induction (position := position + 1) actionsSafe.2]

private theorem statementActionPlan_preparedRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (plan : StatementActionPlan)
    (actionsSafe : plan.actions.all
      (fun action => SourceDataSchemaSafe action.payload) = true) :
    (plan.preparedRows owner).all SourceDataSchemaSafe = true := by
  have gateSafe : SourceDataSchemaSafe (sourceActionGateAtom plan.gate) := by
    cases plan.gate <;>
      simp [sourceActionGateAtom, SourceDataSchemaSafe,
        executableSchemaTemplateSafe]
  simp [StatementActionPlan.preparedRows, StatementActionPlan.rows,
    StatementActionPlan.headerRow, StatementActionPlan.actionRows,
    StatementActionPlan.successorRows, sourceActionOwner_schemaSafe,
    runtimeActionRowsFrom_all_schemaSafe, indexSuccessorRows_all_schemaSafe,
    SourceDataSchemaSafe, executableSchemaTemplateSafe,
    executableSchemaTemplatesSafe, ownerSafe, actionsSafe, gateSafe]

private theorem preparedRowsList_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (plans : List StatementActionPlan)
    (plansSafe : plans.all (fun plan => plan.actions.all
      (fun action => SourceDataSchemaSafe action.payload)) = true) :
    (StatementActionPlan.preparedRowsList owner plans).all
      SourceDataSchemaSafe = true := by
  apply List.all_eq_true.mpr
  intro row member
  simp only [StatementActionPlan.preparedRowsList, List.mem_flatMap] at member
  obtain ⟨plan, planMember, rowMember⟩ := member
  exact (List.all_eq_true.mp
    (statementActionPlan_preparedRows_all_schemaSafe owner ownerSafe plan
      ((List.all_eq_true.mp plansSafe) plan planMember))) row rowMember

private theorem residualSourceActionPlans_all_schemaSafe
    {owner : Atom} (ownerSafe : SourceDataSchemaSafe owner)
    {statements : List RawStatement}
    (actions : AdmittedSourceActionPlans owner statements) :
    (residualSourceActionPlans actions).all (fun plan =>
      plan.actions.all
        (fun action => SourceDataSchemaSafe action.payload)) = true := by
  apply List.all_eq_true.mpr
  intro plan member
  rw [residualSourceActionPlans, List.mem_filter] at member
  exact (List.all_eq_true.mp
    (admitted_actions_all_schemaSafe ownerSafe actions)) plan member.1

private theorem residualSourceActionRows_all_schemaSafe
    {owner : Atom} (ownerSafe : SourceDataSchemaSafe owner)
    {statements : List RawStatement}
    (actions : AdmittedSourceActionPlans owner statements) :
    (residualSourceActionRows actions).all SourceDataSchemaSafe = true := by
  exact preparedRowsList_all_schemaSafe owner ownerSafe
    (residualSourceActionPlans actions)
    (residualSourceActionPlans_all_schemaSafe ownerSafe actions)

private theorem runtimeActionKindRowsFrom_all_schemaSafe
    (actionOwner : Atom) (ownerSafe : SourceDataSchemaSafe actionOwner)
    (position : Nat) (actions : List RuntimeAction) :
    (runtimeActionKindRowsFrom actionOwner position actions).all
      SourceDataSchemaSafe = true := by
  induction actions generalizing position with
  | nil => rfl
  | cons action actions induction =>
      cases action <;>
        simp [runtimeActionKindRowsFrom, runtimeActionKindRow,
          runtimeActionKind, SourceDataSchemaSafe,
          executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
          ownerSafe, induction]

private theorem statementActionPlanActionKindRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (plan : StatementActionPlan) :
    (statementActionPlanActionKindRows owner plan).all
      SourceDataSchemaSafe = true := by
  exact runtimeActionKindRowsFrom_all_schemaSafe
    (sourceActionOwner owner plan.position)
    (sourceActionOwner_schemaSafe owner ownerSafe plan.position) 0 plan.actions

private theorem residualSourceActionKindRows_all_schemaSafe
    {owner : Atom} (ownerSafe : SourceDataSchemaSafe owner)
    {statements : List RawStatement}
    (actions : AdmittedSourceActionPlans owner statements) :
    (residualSourceActionKindRows actions).all SourceDataSchemaSafe = true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [residualSourceActionKindRows, List.mem_flatMap] at member
  obtain ⟨plan, _, rowMember⟩ := member
  exact (List.all_eq_true.mp
    (statementActionPlanActionKindRows_all_schemaSafe owner ownerSafe plan)) row
      rowMember

private theorem sourceDVPairPlanOwner_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner) (position : Nat) :
    SourceDataSchemaSafe (sourceDVPairPlanOwner owner position) := by
  simp [sourceDVPairPlanOwner, SourceDataSchemaSafe,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe, ownerSafe]

private theorem sourceDVPairPlanRowsFrom_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (statementPosition pairPosition : Nat)
    (pairs : List MM2SourceDVPairPlan.DVPair) :
    (sourceDVPairPlanRowsFrom owner statementPosition pairPosition pairs).all
      SourceDataSchemaSafe = true := by
  induction pairs generalizing pairPosition with
  | nil =>
      simp [sourceDVPairPlanRowsFrom, sourceDVPairPlanFrontierAtom,
        sourceDVPairPlanOwner_schemaSafe, SourceDataSchemaSafe,
        executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
        ownerSafe]
  | cons pair pairs induction =>
      simp only [sourceDVPairPlanRowsFrom, List.all_cons, Bool.and_eq_true]
      constructor
      · simp [sourceDVPairPlanLinkAtom, sourceDVPairPlanOwner_schemaSafe,
          SourceDataSchemaSafe, executableSchemaTemplateSafe,
          executableSchemaTemplatesSafe, ownerSafe]
      · exact induction (pairPosition := pairPosition + 1)

private theorem sourceDVPairPlan_rows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (plan : SourceDVPairPlan) :
    (plan.rows owner).all SourceDataSchemaSafe = true := by
  simp only [SourceDVPairPlan.rows, List.all_cons, Bool.and_eq_true]
  constructor
  · simp [sourceDVPairPlanHeaderAtom, SourceDataSchemaSafe,
      executableSchemaTemplateSafe, executableSchemaTemplatesSafe, ownerSafe]
  · exact sourceDVPairPlanRowsFrom_all_schemaSafe owner ownerSafe
      plan.position 0 plan.pairs

private theorem sourceDVPairWitnessRowsFrom_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (statementPosition pairPosition : Nat)
    (witnesses : List SourceDVPairWitness) :
    (sourceDVPairWitnessRowsFrom owner statementPosition pairPosition
      witnesses).all SourceDataSchemaSafe = true := by
  induction witnesses generalizing pairPosition with
  | nil => rfl
  | cons witness witnesses induction =>
      simp [sourceDVPairWitnessRowsFrom, sourceDVPairWitnessLinkAtom,
        sourceDVPairWitnessAtom, sourceDVPairPlanOwner_schemaSafe,
        SourceDataSchemaSafe, executableSchemaTemplateSafe,
        executableSchemaTemplatesSafe, ownerSafe, induction]

private theorem sourceDVPairPlan_witnessRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (plan : SourceDVPairPlan) :
    (plan.witnessRows owner).all SourceDataSchemaSafe = true :=
  sourceDVPairWitnessRowsFrom_all_schemaSafe owner ownerSafe plan.position 0
    plan.witnesses

private theorem admittedDVPair_rows_all_schemaSafe
    {owner : Atom} (ownerSafe : SourceDataSchemaSafe owner)
    {statements : List RawStatement}
    (input : AdmittedSourceDVPairPlans owner statements) :
    input.rows.all SourceDataSchemaSafe = true := by
  apply List.all_eq_true.mpr
  intro row member
  simp only [AdmittedSourceDVPairPlans.rows, sourceDVPairPlanRows,
    List.mem_flatMap] at member
  obtain ⟨plan, _, rowMember⟩ := member
  exact (List.all_eq_true.mp
    (sourceDVPairPlan_rows_all_schemaSafe owner ownerSafe plan)) row rowMember

private theorem admittedDVPair_witnessRows_all_schemaSafe
    {owner : Atom} (ownerSafe : SourceDataSchemaSafe owner)
    {statements : List RawStatement}
    (input : AdmittedSourceDVPairPlans owner statements) :
    input.witnessRows.all SourceDataSchemaSafe = true := by
  apply List.all_eq_true.mpr
  intro row member
  simp only [AdmittedSourceDVPairPlans.witnessRows,
    sourceDVPairPlanWitnessRows, List.mem_flatMap] at member
  obtain ⟨plan, _, rowMember⟩ := member
  exact (List.all_eq_true.mp
    (sourceDVPairPlan_witnessRows_all_schemaSafe owner ownerSafe plan)) row
      rowMember

@[simp] private theorem sourceAssertionCandidateAtom_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (candidate : SourceAssertionCandidate) :
    SourceDataSchemaSafe (sourceAssertionCandidateAtom owner candidate) := by
  have gateSafe : SourceDataSchemaSafe (sourceActionGateAtom candidate.gate) := by
    cases candidate.gate <;>
      simp [sourceActionGateAtom, SourceDataSchemaSafe,
        executableSchemaTemplateSafe]
  simp [sourceAssertionCandidateAtom, gateSafe, SourceDataSchemaSafe,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
    listAtom_schemaSafe, ownerSafe]

private theorem admittedAssertionCandidates_rows_all_schemaSafe
    {owner : Atom} (ownerSafe : SourceDataSchemaSafe owner)
    {statements : List RawStatement}
    (input : AdmittedSourceAssertionCandidates owner statements) :
    input.rows.all SourceDataSchemaSafe = true := by
  simp [AdmittedSourceAssertionCandidates.rows,
    sourceAssertionCandidateAtom_schemaSafe, ownerSafe]

private theorem assertionPublicationPlanRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (candidate : SourceAssertionCandidate) :
    (assertionPublicationPlanRows owner candidate).all
      SourceDataSchemaSafe = true := by
  have payloadSafe :
      (assertionPublicationPayloadRows owner candidate).all
        SourceDataSchemaSafe = true :=
    assertionExecutionRowsFor_schemaSafe owner ownerSafe
      candidate.assertionPosition candidate.assertion
  have publicationOwnerSafe :
      SourceDataSchemaSafe
        (assertionPublicationOwnerAtom owner candidate.position) := by
    simp [assertionPublicationOwnerAtom, SourceDataSchemaSafe,
      executableSchemaTemplateSafe, executableSchemaTemplatesSafe, ownerSafe]
  have linkedSafe :
      (assertionPublicationLinkedRows owner candidate).all
        SourceDataSchemaSafe = true := by
    apply linkedRows_all_schemaSafe
    · exact publicationOwnerSafe
    · simpa using payloadSafe
  have successorSafe :
      (assertionPublicationSuccessorRows owner candidate).all
        SourceDataSchemaSafe = true := by
    exact indexSuccessorRows_all_schemaSafe
      (assertionPublicationOwnerAtom owner candidate.position)
      publicationOwnerSafe _
  simp [assertionPublicationPlanRows, assertionPublicationHeaderAtom,
    SourceDataSchemaSafe, executableSchemaTemplateSafe,
    executableSchemaTemplatesSafe, ownerSafe, linkedSafe, successorSafe]

private theorem nativeAssertionPublicationRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (candidates : List SourceAssertionCandidate) :
    (nativeAssertionPublicationRows owner candidates).all
      SourceDataSchemaSafe = true := by
  apply List.all_eq_true.mpr
  intro row member
  obtain ⟨candidate, _, _, rowMember⟩ :=
    mem_nativeAssertionPublicationRows member
  exact (List.all_eq_true.mp
    (assertionPublicationPlanRows_all_schemaSafe owner ownerSafe candidate)) row
      rowMember

private theorem essentialCandidateRow?_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (plan : StatementActionPlan)
    (actionsSafe : plan.actions.all
      (fun action => SourceDataSchemaSafe action.payload) = true)
    (row : Atom) (derived : essentialCandidateRow? owner plan = some row) :
    SourceDataSchemaSafe row := by
  unfold essentialCandidateRow? at derived
  split at derived <;> simp_all
  rename_i statement label candidateFormula actualOwner actualLabel
  obtain ⟨_, rfl⟩ := derived
  have formulaSafe : SourceDataSchemaSafe candidateFormula := by
    simpa [RuntimeAction.payload, SourceDataSchemaSafe,
      executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
      ownerSafe] using actionsSafe
  simp [essentialCandidateAtom, SourceDataSchemaSafe,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe,
    formulaSafe, ownerSafe]

private theorem essentialCandidateRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (plans : List StatementActionPlan)
    (plansSafe : plans.all (fun plan => plan.actions.all
      (fun action => SourceDataSchemaSafe action.payload)) = true) :
    (essentialCandidateRows owner plans).all SourceDataSchemaSafe = true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [essentialCandidateRows, List.mem_filterMap] at member
  obtain ⟨plan, planMember, derived⟩ := member
  exact essentialCandidateRow?_schemaSafe owner ownerSafe plan
    ((List.all_eq_true.mp plansSafe) plan planMember) row derived

private theorem sourcePreparedTheoremRow_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (position nextPosition : Nat) (statement : RawStatement)
    (obligation : TheoremObligation) :
    SourceDataSchemaSafe
      (sourcePreparedTheoremRow owner position nextPosition statement
        obligation) := by
  simp [sourcePreparedTheoremRow, sourcePreparedTheoremFact,
    sourceProofOwnerAtom_schemaSafe, SourceDataSchemaSafe,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe, ownerSafe]

private theorem sourcePreparedAssertionHeaderRow_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (position : Nat)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (obligation : TheoremObligation) :
    SourceDataSchemaSafe
      (sourcePreparedAssertionHeaderRow owner position state obligation) := by
  let assertion := sourceAssertion state obligation.label.name
    obligation.formula
  have headerSafe : SourceDataSchemaSafe
      (assertionHeaderRow owner state.assertions.length assertion) :=
    (List.all_eq_true.mp
      (assertionExecutionRowsFor_schemaSafe owner ownerSafe
        state.assertions.length assertion)) _ (by
          simp [assertionExecutionRowsFor])
  simp [sourcePreparedAssertionHeaderRow,
    sourcePreparedAssertionHeaderFact, assertion, headerSafe,
    sourceProofOwnerAtom_schemaSafe, SourceDataSchemaSafe,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe, ownerSafe]

private theorem sourcePreparedAssertionSupportRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (position : Nat)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (obligation : TheoremObligation) :
    (sourcePreparedAssertionSupportRows owner position state obligation).all
      SourceDataSchemaSafe = true := by
  let assertion := sourceAssertion state obligation.label.name
    obligation.formula
  apply List.all_eq_true.mpr
  intro row member
  have tailMember :
      row ∈ (assertionExecutionRowsFor owner state.assertions.length
        assertion).tail := by
    simpa [sourcePreparedAssertionSupportRows, assertion] using member
  exact (List.all_eq_true.mp
    (assertionExecutionRowsFor_schemaSafe owner ownerSafe
      state.assertions.length assertion)) row
        (List.mem_of_mem_tail tailMember)

private theorem sourcePreparedProofRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (position : Nat)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (obligation : TheoremObligation) :
    (sourcePreparedProofRows owner position state obligation).all
      SourceDataSchemaSafe = true := by
  rcases obligation with ⟨site, label, formula, proof⟩
  have proofOwnerSafe := sourceProofOwnerAtom_schemaSafe owner ownerSafe position
  cases proof with
  | normal steps =>
      have inputSafe := proofInputRows_all_schemaSafe owner
        (sourceProofOwnerAtom owner position) ownerSafe proofOwnerSafe
        (.normal label.name formula (steps.map (·.name)))
      have inventorySafe := normalLabelInventoryRows_all_schemaSafe
        (sourceProofOwnerAtom owner position) proofOwnerSafe state
      simp [sourcePreparedProofRows, inputSafe, inventorySafe]
  | compressed openParen header closeParen words =>
      simpa only [sourcePreparedProofRows] using
        transformedCompressedProofData_rows_all_schemaSafe owner
          (sourceProofOwnerAtom owner position) ownerSafe proofOwnerSafe state
          label.name formula (header.map (·.name)) (words.map (·.bytes))

private theorem sourcePreparedTheoremRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (position nextPosition : Nat) (statement : RawStatement)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (obligation : TheoremObligation) :
    (sourcePreparedTheoremRows owner position nextPosition statement state
      obligation).all SourceDataSchemaSafe = true := by
  simp [sourcePreparedTheoremRows,
    sourcePreparedTheoremRow_schemaSafe owner ownerSafe,
    sourcePreparedProofRows_all_schemaSafe owner ownerSafe,
    sourcePreparedAssertionHeaderRow_schemaSafe owner ownerSafe,
    sourcePreparedAssertionSupportRows_all_schemaSafe owner ownerSafe]

private theorem sourceDerivedProofRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (statements : List RawStatement) (rows : List Atom)
    (derived : sourceDerivedProofRows owner statements = .ok rows) :
    rows.all SourceDataSchemaSafe = true := by
  exact sourceDerivedProofRows_all_of owner SourceDataSchemaSafe
    (sourcePreparedTheoremRows_all_schemaSafe owner ownerSafe) statements rows
    derived

private theorem canonicalSourceEventRows_all_schemaSafe
    (owner : Atom) (ownerSafe : SourceDataSchemaSafe owner)
    (statements : List RawStatement) :
    (sourceEventStartRow owner :: sourceEventRows owner statements ++
      [sourceEventEndRow owner statements]).all SourceDataSchemaSafe = true := by
  have payloadSafe : statements.all
      (fun statement => SourceDataSchemaSafe (rawStatementAtom statement)) =
        true := by simp
  have rowsSafe := linkedRows_all_schemaSafe "source-statement" owner ownerSafe
    rawStatementAtom statements payloadSafe
  simp [sourceEventRows_eq_linkedRows, sourceEventStartRow,
    sourceEventEndRow, SourceDataSchemaSafe, executableSchemaTemplateSafe,
    executableSchemaTemplatesSafe, ownerSafe, rowsSafe]

/-- The admitted ordered source-event envelope and every recomputed proof data
packet pass the fixed verifier's recursive executable-schema check. -/
theorem AdmittedSourceEventInput.initialRows_all_schemaSafe
    {owner : Atom} (ownerSafe : SourceDataSchemaSafe owner)
    (input : AdmittedSourceEventInput owner) :
    input.initialRows.all SourceDataSchemaSafe = true := by
  have eventSafe : input.rows.all SourceDataSchemaSafe = true := by
    rw [input.canonical]
    exact canonicalSourceEventRows_all_schemaSafe owner ownerSafe
      input.statements
  have derivedSafe : input.derivedRows.all SourceDataSchemaSafe = true :=
    sourceDerivedProofRows_all_schemaSafe owner ownerSafe input.statements
      input.derivedRows input.derivedExact
  simp [AdmittedSourceEventInput.initialRows, eventSafe, derivedSafe]

private theorem deferProofControlRow_schemaSafe (row : Atom)
    (safe : SourceDataSchemaSafe row) :
    SourceDataSchemaSafe (deferProofControlRow row) := by
  unfold deferProofControlRow
  split <;>
    simp_all [SourceDataSchemaSafe, executableSchemaTemplateSafe,
      executableSchemaTemplatesSafe]

private theorem deferProofControls_all_schemaSafe (rows : List Atom)
    (safe : rows.all SourceDataSchemaSafe = true) :
    (deferProofControls rows).all SourceDataSchemaSafe = true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [deferProofControls, List.mem_map] at member
  obtain ⟨source, sourceMember, rfl⟩ := member
  exact deferProofControlRow_schemaSafe source
    ((List.all_eq_true.mp safe) source sourceMember)

private theorem deferCompressedHeaderControlRow_schemaSafe (row : Atom)
    (safe : SourceDataSchemaSafe row) :
    SourceDataSchemaSafe (deferCompressedHeaderControlRow row) := by
  unfold deferCompressedHeaderControlRow
  split <;>
    simp_all [SourceDataSchemaSafe, executableSchemaTemplateSafe,
      executableSchemaTemplatesSafe]

private theorem deferCompressedHeaderControls_all_schemaSafe
    (rows : List Atom) (safe : rows.all SourceDataSchemaSafe = true) :
    (deferCompressedHeaderControls rows).all SourceDataSchemaSafe = true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [deferCompressedHeaderControls, List.mem_map] at member
  obtain ⟨source, sourceMember, rfl⟩ := member
  exact deferCompressedHeaderControlRow_schemaSafe source
    ((List.all_eq_true.mp safe) source sourceMember)

/-- Every row emitted by the admitted source-data transform passes the fixed
verifier's recursive executable-schema checker.  This is stronger than root
proof-neutrality: executable syntax hidden at any depth is covered. -/
theorem sourceDataProgram_all_schemaSafe
    {owner : Atom} (ownerAuthorized : SourceOwnerLineageAuthorized owner)
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    (sourceDataProgram input actions).all SourceDataSchemaSafe = true := by
  let dvPlans := admitSourceDVPairPlans actions
  let assertionCandidates := admitSourceAssertionCandidatesFromActions actions
  have ownerSafe : SourceDataSchemaSafe owner := by
    simpa [SourceDataSchemaSafe] using ownerAuthorized.2
  have deferredSafe := deferCompressedHeaderControls_all_schemaSafe _
    (deferProofControls_all_schemaSafe _
      (AdmittedSourceEventInput.initialRows_all_schemaSafe ownerSafe input))
  have plansSafe := admitted_actions_all_schemaSafe ownerSafe actions
  have dvRowsSafe := admittedDVPair_rows_all_schemaSafe ownerSafe dvPlans
  have dvWitnessSafe :=
    admittedDVPair_witnessRows_all_schemaSafe ownerSafe dvPlans
  have candidateRowsSafe :=
    admittedAssertionCandidates_rows_all_schemaSafe ownerSafe
      assertionCandidates
  have publicationRowsSafe := nativeAssertionPublicationRows_all_schemaSafe
    owner ownerSafe assertionCandidates.candidates
  have essentialRowsSafe := essentialCandidateRows_all_schemaSafe owner
    ownerSafe actions.plans plansSafe
  have residualRowsSafe :=
    residualSourceActionRows_all_schemaSafe ownerSafe actions
  have residualKindsSafe :=
    residualSourceActionKindRows_all_schemaSafe ownerSafe actions
  simp [sourceDataProgram, dvPlans, assertionCandidates, deferredSafe,
    dvRowsSafe, dvWitnessSafe, candidateRowsSafe, publicationRowsSafe,
    essentialRowsSafe, residualRowsSafe, residualKindsSafe,
    objectInventoryRows, objectInventoryRowsFrom, objectFrontierAtom,
    objectRootKey, activeVariableRows, activeVariableLedgerOwner,
    variableTypecodeLedgerRows, variableTypecodeLedgerOwner,
    variableTypecodeInventoryRows, variableTypecodeBindingRows,
    emptyScopedActivityRows, activeHypothesisLedgerOwner,
    activeDistinctLedgerOwner, sourceActivityFrontierAtom,
    dvOccurrenceRows, dvOccurrenceRowsFrom, dvOccurrenceFrontierAtom,
    dvOccurrenceFrontierAtAtom, SourceDataSchemaSafe,
    executableSchemaTemplateSafe, executableSchemaTemplatesSafe, ownerSafe]

/-- The semantic lineage invariant holds for every atom emitted by the
source-data transform. -/
theorem sourceDataProgram_executable_lineageAuthorized
    {owner : Atom} (ownerAuthorized : SourceOwnerLineageAuthorized owner)
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    AtomsWithin VerifierExecutableLineageAuthorized
      (sourceDataProgram input actions) := by
  intro atom member
  apply sourceDataSchemaSafe_authorized
  exact (List.all_eq_true.mp
    (sourceDataProgram_all_schemaSafe ownerAuthorized input actions)) atom
      member

/-- Both independently constructed transformation outputs satisfy the same
recursive executable-lineage invariant at their actual composition boundary. -/
theorem composeProgram_executable_lineageAuthorized
    {owner : Atom} (ownerAuthorized : SourceOwnerLineageAuthorized owner)
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    AtomsWithin VerifierExecutableLineageAuthorized
      (composeProgram authoredMetamathVerifierGSLT input actions) := by
  intro atom member
  simp only [composeProgram, List.mem_append] at member
  rcases member with verifierMember | sourceMember
  · exact genericVerifierProgram_executable_lineageAuthorized atom
      verifierMember
  · exact sourceDataProgram_executable_lineageAuthorized ownerAuthorized
      input actions atom sourceMember

/-- Arbitrary-fuel rule-scoped MORK execution preserves executable provenance
for the actual composition of the proof-independent verifier and admitted
source-data transformations. -/
theorem composeProgram_runN_executable_lineageAuthorized
    (policy : UnsupportedExecPolicy) (fuel : Nat)
    {owner : Atom} (ownerAuthorized : SourceOwnerLineageAuthorized owner)
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    AtomsWithin VerifierExecutableLineageAuthorized
      (cRuleScopedSourceWorkQueueRunN policy fuel
        (composeProgram authoredMetamathVerifierGSLT input actions)).1 := by
  exact cRuleScopedSourceWorkQueueRunN_lineageAuthorized
    verifierExecutableRawFacts policy fuel _
      (composeProgram_executable_lineageAuthorized ownerAuthorized input actions)

@[simp] private theorem listAtom_ground {Source : Type} (encode : Source → Atom)
    (encodedGround : ∀ value, isGroundAtom (encode value) = true) :
    ∀ values, isGroundAtom (listAtom encode values) = true
  | [] => rfl
  | head :: tail => by
      simp [listAtom, isGroundAtom, isGroundAtom.isGroundList,
        encodedGround head, listAtom_ground encode encodedGround tail]

@[simp] private theorem runtimeSymAtom_ground (symbol : Metamath.Verify.Sym) :
    isGroundAtom (runtimeSymAtom symbol) = true := by
  cases symbol <;>
    simp [runtimeSymAtom, isGroundAtom, isGroundAtom.isGroundList]

@[simp] private theorem locatedByteSpanAtom_ground (span :
    Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan) :
    isGroundAtom (locatedByteSpanAtom span) = true := by
  simp [locatedByteSpanAtom, isGroundAtom, isGroundAtom.isGroundList]

@[simp] private theorem locatedNameAtom_ground (name :
    Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.LocatedName) :
    isGroundAtom (locatedNameAtom name) = true := by
  simp [locatedNameAtom, locatedByteSpanAtom_ground,
    isGroundAtom, isGroundAtom.isGroundList]

@[simp] private theorem locatedTokenAtom_ground (token :
    Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.LocatedToken) :
    isGroundAtom (locatedTokenAtom token) = true := by
  have byteGround : ∀ byte, isGroundAtom (byteAtom byte) = true := by
    intro byte
    simp [byteAtom]
  simp [locatedTokenAtom, locatedByteSpanAtom_ground,
    listAtom_ground byteAtom byteGround, isGroundAtom,
    isGroundAtom.isGroundList]

@[simp] private theorem proofPayloadAtom_ground (proof :
    Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.ProofPayload) :
    isGroundAtom (proofPayloadAtom proof) = true := by
  cases proof <;>
    simp [proofPayloadAtom, locatedByteSpanAtom_ground,
      locatedNameAtom_ground, locatedTokenAtom_ground, listAtom_ground,
      isGroundAtom, isGroundAtom.isGroundList]

@[simp] private theorem rawStatementAtom_ground (statement :
    Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.RawStatement) :
    isGroundAtom (rawStatementAtom statement) = true := by
  cases statement <;>
    simp [rawStatementAtom, locatedByteSpanAtom_ground,
      locatedNameAtom_ground, proofPayloadAtom_ground, listAtom_ground,
      isGroundAtom, isGroundAtom.isGroundList]

@[simp] private theorem formulaAtom_ground (formula : ConstantHeadedFormula) :
    isGroundAtom (formulaAtom formula) = true := by
  simp [formulaAtom, runtimeSymAtom_ground, listAtom_ground,
    isGroundAtom, isGroundAtom.isGroundList]

@[simp] private theorem hypothesisAtom_ground (hypothesis : HypothesisView) :
    isGroundAtom (hypothesisAtom hypothesis) = true := by
  cases hypothesis <;>
    simp [hypothesisAtom, formulaAtom_ground,
      isGroundAtom, isGroundAtom.isGroundList]

@[simp] private theorem stringPairAtom_ground (pair : String × String) :
    isGroundAtom (stringPairAtom pair) = true := by
  simp [stringPairAtom, isGroundAtom, isGroundAtom.isGroundList]

@[simp] private theorem sourceFrameAtom_ground (frame : SourceFrame) :
    isGroundAtom (sourceFrameAtom frame) = true := by
  simp [sourceFrameAtom, listAtom_ground,
    isGroundAtom, isGroundAtom.isGroundList]

@[simp] private theorem sourceAssertionAtom_ground (assertion : SourceAssertion) :
    isGroundAtom (sourceAssertionAtom assertion) = true := by
  simp [sourceAssertionAtom, formulaAtom_ground, sourceFrameAtom_ground,
    hypothesisAtom_ground, listAtom_ground,
      isGroundAtom, isGroundAtom.isGroundList]

private theorem assertionExecutionRowsFor_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (position : Nat) (assertion : SourceAssertion) :
    (assertionExecutionRowsFor owner position assertion).all isGroundAtom = true := by
  simp [assertionExecutionRowsFor, assertionHeaderRow,
    assertionHypothesisRows, assertionHypothesisRow,
    assertionHypothesisSuccessorRows, assertionHypothesisSuccessorRow,
    assertionDVHeaderRow, assertionDVPairRows, assertionDVPairRow,
    assertionDVSuccessorRows, assertionResultRow,
    isGroundAtom, isGroundAtom.isGroundList, ownerGround]
  constructor <;>
    intro row position inBounds equal <;>
    subst row <;>
    simp [isGroundAtom, isGroundAtom.isGroundList, ownerGround]

@[simp] private theorem linkedRow_ground (family : String) (owner payload : Atom)
    (position nextPosition : Nat) (ownerGround : isGroundAtom owner = true)
    (payloadGround : isGroundAtom payload = true) :
    isGroundAtom (linkedRow family owner position nextPosition payload) = true := by
  simp [linkedRow, isGroundAtom, isGroundAtom.isGroundList,
    ownerGround, payloadGround]

private theorem linkedRows_all_ground {Source : Type}
    (family : String) (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (encode : Source → Atom) (values : List Source)
    (payloadsGround : values.all (fun value => isGroundAtom (encode value)) =
      true) :
    (linkedRows family owner encode values).all isGroundAtom = true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [mem_linkedRows_iff] at member
  obtain ⟨position, inBounds, rfl⟩ := member
  apply linkedRow_ground
  · exact ownerGround
  · exact (List.all_eq_true.mp payloadsGround) values[position]
      (List.get_mem values ⟨position, inBounds⟩)

@[simp] private theorem indexedRow_ground (family : String)
    (owner payload : Atom) (position : Nat)
    (ownerGround : isGroundAtom owner = true)
    (payloadGround : isGroundAtom payload = true) :
    isGroundAtom (indexedRow family owner position payload) = true := by
  simp [indexedRow, isGroundAtom, isGroundAtom.isGroundList,
    ownerGround, payloadGround]

private theorem indexedRows_all_ground {Source : Type}
    (family : String) (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (encode : Source → Atom) (values : List Source)
    (payloadsGround : values.all (fun value => isGroundAtom (encode value)) =
      true) :
    (indexedRows family owner encode values).all isGroundAtom = true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [mem_indexedRows_iff] at member
  obtain ⟨position, inBounds, rfl⟩ := member
  apply indexedRow_ground
  · exact ownerGround
  · exact (List.all_eq_true.mp payloadsGround) values[position]
      (List.get_mem values ⟨position, inBounds⟩)

@[simp] private theorem indexSuccessorRows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true) (count : Nat) :
    (indexSuccessorRows owner count).all isGroundAtom = true := by
  simp [indexSuccessorRows, isGroundAtom, isGroundAtom.isGroundList,
    ownerGround]

@[simp] private theorem sourceActionOwner_ground (owner : Atom)
    (ownerGround : isGroundAtom owner = true) (position : Nat) :
    isGroundAtom (sourceActionOwner owner position) = true := by
  simp [sourceActionOwner, isGroundAtom, isGroundAtom.isGroundList,
    ownerGround]

@[simp] private theorem sourceProofOwnerAtom_ground (owner : Atom)
    (ownerGround : isGroundAtom owner = true) (position : Nat) :
    isGroundAtom (sourceProofOwnerAtom owner position) = true := by
  simp [sourceProofOwnerAtom, isGroundAtom, isGroundAtom.isGroundList,
    ownerGround]

@[simp] private theorem compressedIndexCodeAtom_ground
    (reversePrefixDigits : List Nat) (terminalDigit : Nat) :
    isGroundAtom
      (compressedIndexCodeAtom reversePrefixDigits terminalDigit) = true := by
  simp [compressedIndexCodeAtom, listAtom_ground,
    isGroundAtom, isGroundAtom.isGroundList]

@[simp] private theorem compressedIndexCode_atom_ground
    (code : CompressedIndexCode) : isGroundAtom code.atom = true := by
  simp [CompressedIndexCode.atom]

private theorem compressedIndexSuccessorRowsFrom_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (count : Nat) (current : CompressedIndexCode) :
    (compressedIndexSuccessorRowsFrom owner count current).all
      isGroundAtom = true := by
  induction count generalizing current with
  | zero => rfl
  | succ count induction =>
      simp [compressedIndexSuccessorRowsFrom, compressedIndexSuccessorRow,
        isGroundAtom, isGroundAtom.isGroundList, ownerGround, induction]

private theorem compressedIndexSuccessorRows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true) (count : Nat) :
    (compressedIndexSuccessorRows owner count).all isGroundAtom = true := by
  exact compressedIndexSuccessorRowsFrom_all_ground owner ownerGround count
    CompressedIndexCode.zero

private theorem compressedNormalStackSuccessorRows_all_ground
    (proofOwner : Atom) (ownerGround : isGroundAtom proofOwner = true)
    (count : Nat) :
    (compressedNormalStackSuccessorRows proofOwner count).all
      isGroundAtom = true := by
  simp [compressedNormalStackSuccessorRows, isGroundAtom,
    isGroundAtom.isGroundList, ownerGround]

private theorem proofInputRows_all_ground
    (scopeOwner proofOwner : Atom)
    (scopeGround : isGroundAtom scopeOwner = true)
    (proofGround : isGroundAtom proofOwner = true)
    (proof : ProofInput) :
    (proofInputRows scopeOwner proofOwner proof).all isGroundAtom = true := by
  cases proof with
  | normal theoremLabel formula proofLabels =>
      have labelRowsGround := linkedRows_all_ground "normal-proof-label"
        proofOwner proofGround stringAtom proofLabels (by simp)
      simp [proofInputRows, ProofInputTables.rows, proofInputTables,
        labelRowsGround, indexSuccessorRows_all_ground,
        formulaAtom_ground, isGroundAtom, isGroundAtom.isGroundList,
        scopeGround, proofGround]
  | compressed theoremLabel formula header body =>
      have headerRowsGround := indexedRows_all_ground
        "compressed-header-label" proofOwner proofGround stringAtom header
        (by simp)
      have wordGround : ∀ word : List UInt8,
          isGroundAtom (compressedWordAtom word) = true := by
        intro word
        simp [compressedWordAtom, uint8Atom]
      have bodyRowsGround := indexedRows_all_ground
        "compressed-body-word" proofOwner proofGround compressedWordAtom body
        (by simp [wordGround])
      simp [proofInputRows, ProofInputTables.rows, proofInputTables,
        headerRowsGround, bodyRowsGround, indexSuccessorRows_all_ground,
        formulaAtom_ground, isGroundAtom, isGroundAtom.isGroundList,
        scopeGround, proofGround]

@[simp] private theorem normalLabelEntryAtom_ground
    (entry : Mettapedia.GSLT.FiniteOccurrenceLookup.Entry String
      NormalLabelKind) :
    isGroundAtom (normalLabelEntryAtom entry) = true := by
  rcases entry with ⟨key, kind⟩
  cases kind <;>
    simp [normalLabelEntryAtom, normalLabelKindAtom,
      isGroundAtom, isGroundAtom.isGroundList]

private theorem normalLabelInventoryRows_all_ground
    (proofOwner : Atom) (ownerGround : isGroundAtom proofOwner = true)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState) :
    (normalLabelInventoryRows proofOwner state).all isGroundAtom = true := by
  simp [normalLabelInventoryRows, normalLabelCandidateRows,
    normalLabelCandidateRow, normalLabelFrontierRow, linkedRow,
    normalLabelEntryAtom_ground, isGroundAtom, isGroundAtom.isGroundList,
    ownerGround]

@[simp] private theorem compressedHeaderInputAtom_ground
    (input : CompressedHeaderInput) :
    isGroundAtom (compressedHeaderInputAtom input) = true := by
  cases input <;>
    simp [compressedHeaderInputAtom,
      formulaAtom_ground, isGroundAtom, isGroundAtom.isGroundList]

private theorem compressedHeaderRows_all_ground
    (proofOwner : Atom) (ownerGround : isGroundAtom proofOwner = true)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (formula : ConstantHeadedFormula) (explicitLabels : List String) :
    (compressedHeaderRows proofOwner state formula explicitLabels).all
      isGroundAtom = true := by
  apply linkedRows_all_ground
  · exact ownerGround
  · simp

private theorem compressedBodyRows_all_ground
    (proofOwner : Atom) (ownerGround : isGroundAtom proofOwner = true)
    (bodyWords : List (List UInt8)) :
    (compressedBodyRows proofOwner bodyWords).all isGroundAtom = true := by
  apply indexedRows_all_ground
  · exact ownerGround
  · apply List.all_eq_true.mpr
    intro word _
    simp [compressedWordAtom, uint8Atom]

@[simp] private theorem compressedDerivedOwner_ground (tag : String)
    (proofOwner : Atom) (ownerGround : isGroundAtom proofOwner = true) :
    isGroundAtom (.expression [.symbol tag, proofOwner]) = true := by
  simp [isGroundAtom, isGroundAtom.isGroundList, ownerGround]

private theorem transformedCompressedProofData_rows_all_ground
    (scopeOwner proofOwner : Atom)
    (scopeGround : isGroundAtom scopeOwner = true)
    (proofGround : isGroundAtom proofOwner = true)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8)) :
    (transformCompressedProofData scopeOwner proofOwner state theoremLabel
      formula explicitLabels bodyWords).rows.all isGroundAtom = true := by
  have headerGround := compressedHeaderRows_all_ground proofOwner proofGround
    state formula explicitLabels
  have bodyGround := compressedBodyRows_all_ground proofOwner proofGround
    bodyWords
  have heapOwnerGround :
      isGroundAtom (compressedHeapOwner proofOwner) = true := by
    simp [compressedHeapOwner, proofGround]
  have nodeOwnerGround :
      isGroundAtom (compressedNodeOwner proofOwner) = true := by
    simp [compressedNodeOwner, proofGround]
  have stackOwnerGround :
      isGroundAtom (compressedStackOwner proofOwner) = true := by
    simp [compressedStackOwner, proofGround]
  have heapGround := compressedIndexSuccessorRows_all_ground
    (compressedHeapOwner proofOwner) heapOwnerGround
    (compressedHeapCapacity state formula explicitLabels bodyWords)
  have nodeGround := compressedIndexSuccessorRows_all_ground
    (compressedNodeOwner proofOwner) nodeOwnerGround
    (compressedNodeCapacity state formula bodyWords)
  have stackGround := compressedIndexSuccessorRows_all_ground
    (compressedStackOwner proofOwner) stackOwnerGround
    (compressedStackCapacity bodyWords)
  have normalStackGround := compressedNormalStackSuccessorRows_all_ground
    proofOwner proofGround (compressedStackCapacity bodyWords)
  simp [CompressedProofDataArtifact.rows, transformCompressedProofData,
    headerGround, bodyGround, heapGround, nodeGround, stackGround,
    normalStackGround, indexSuccessorRows_all_ground,
    formulaAtom_ground, isGroundAtom, isGroundAtom.isGroundList,
    scopeGround, proofGround]

private theorem proofRuntimeRows_all_ground (owner : Atom)
    (ownerGround : isGroundAtom owner = true)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState) :
    (proofRuntimeRows owner state).all isGroundAtom = true := by
  simp [proofRuntimeRows, hypothesisLookupRows, hypothesisLookupRow,
    normalExecutionRows, callerDVRows, callerDVRowsOfPairs,
    callerDVRowsForPair, callerDVRow, assertionExecutionRows,
    isGroundAtom, isGroundAtom.isGroundList, ownerGround]
  intro rows position inBounds equal
  subst rows
  exact List.all_eq_true.mp
    (assertionExecutionRowsFor_ground owner ownerGround position
      state.assertions[position])

private theorem runtimeAction_payload_ground_of_delta
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (before after : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (action : RuntimeAction)
    (member : action ∈ sourceStateRuntimeDelta owner before after) :
    isGroundAtom action.payload = true := by
  have classified := runtimeAction_payload_mem_of_mem_runtimeRowDelta action
    (proofRuntimeRows owner before) (proofRuntimeRows owner after) member
  rcases classified with beforeMember | afterMember
  · exact (List.all_eq_true.mp
      (proofRuntimeRows_all_ground owner ownerGround before)) _ beforeMember
  · exact (List.all_eq_true.mp
      (proofRuntimeRows_all_ground owner ownerGround after)) _ afterMember

private theorem statementActionPlan_actions_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (position : Nat)
    (before after : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (statement :
      Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.RawStatement)
    (obligations : List TheoremObligation) :
    (statementActionPlan owner position before after statement obligations).actions.all
      (fun action => isGroundAtom action.payload) = true := by
  apply List.all_eq_true.mpr
  intro action member
  exact runtimeAction_payload_ground_of_delta owner ownerGround before after
    action member

private theorem buildSourceActionPlansFrom_actions_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (position : Nat)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (statements : List
      Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.RawStatement)
    (final : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (plans : List StatementActionPlan)
    (built : buildSourceActionPlansFrom owner position state statements =
      .ok (final, plans)) :
    plans.all (fun plan =>
      plan.actions.all (fun action => isGroundAtom action.payload)) = true := by
  induction statements generalizing position state final plans with
  | nil =>
      simp [buildSourceActionPlansFrom] at built
      obtain ⟨rfl, rfl⟩ := built
      rfl
  | cons statement statements induction =>
      simp only [buildSourceActionPlansFrom] at built
      cases applied : applyStatement state statement with
      | rejected rejection => simp [applied] at built
      | ok pair =>
          obtain ⟨next, obligations⟩ := pair
          simp only [applied] at built
          cases recursive :
              buildSourceActionPlansFrom owner (position + 1) next statements with
          | rejected rejection => simp [recursive] at built
          | ok result =>
              obtain ⟨recursiveFinal, recursivePlans⟩ := result
              simp only [recursive] at built
              obtain ⟨rfl, rfl⟩ := FoldResult.ok.inj built
              have restSafe :=
                induction (position := position + 1) (state := next)
                  (final := final) (plans := recursivePlans) recursive
              simpa only [List.all_cons,
                statementActionPlan_actions_all_ground owner ownerGround,
                Bool.true_and] using restSafe

private theorem admitted_actions_all_ground
    {owner : Atom} (ownerGround : isGroundAtom owner = true)
    {statements : List
      Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.RawStatement}
    (input : AdmittedSourceActionPlans owner statements) :
    input.plans.all (fun plan =>
      plan.actions.all (fun action => isGroundAtom action.payload)) = true := by
  apply buildSourceActionPlansFrom_actions_all_ground owner ownerGround 0
    Mettapedia.Languages.Metamath.SourceGSLTState.initialState statements
    input.finalState input.plans
  simpa [buildSourceActionPlans] using input.exact

@[simp] private theorem runtimeActionAtom_ground (action : RuntimeAction)
    (payloadGround : isGroundAtom action.payload = true) :
    isGroundAtom (runtimeActionAtom action) = true := by
  cases action <;>
    simp_all [RuntimeAction.payload, runtimeActionAtom]

private theorem runtimeActionRowsFrom_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (position : Nat) (actions : List RuntimeAction)
    (actionsGround : actions.all
      (fun action => isGroundAtom action.payload) = true) :
    (runtimeActionRowsFrom owner position actions).all isGroundAtom = true := by
  induction actions generalizing position with
  | nil => rfl
  | cons action actions induction =>
      simp only [List.all_cons, Bool.and_eq_true] at actionsGround
      simp [runtimeActionRowsFrom, linkedRow_ground, ownerGround,
        runtimeActionAtom_ground action actionsGround.1,
        induction (position := position + 1) actionsGround.2]

private theorem statementActionPlan_preparedRows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (plan : StatementActionPlan)
    (actionsGround : plan.actions.all
      (fun action => isGroundAtom action.payload) = true) :
    (plan.preparedRows owner).all isGroundAtom = true := by
  have gateGround : isGroundAtom (sourceActionGateAtom plan.gate) = true := by
    cases plan.gate <;> simp [sourceActionGateAtom, isGroundAtom]
  simp [StatementActionPlan.preparedRows, StatementActionPlan.rows,
    StatementActionPlan.headerRow, StatementActionPlan.actionRows,
    StatementActionPlan.successorRows, rawStatementAtom_ground,
    sourceActionOwner_ground, runtimeActionRowsFrom_all_ground,
    indexSuccessorRows_all_ground, isGroundAtom, isGroundAtom.isGroundList,
    ownerGround, actionsGround, gateGround]

private theorem preparedRowsList_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (plans : List StatementActionPlan)
    (plansGround : plans.all (fun plan => plan.actions.all
      (fun action => isGroundAtom action.payload)) = true) :
    (StatementActionPlan.preparedRowsList owner plans).all isGroundAtom = true := by
  apply List.all_eq_true.mpr
  intro row member
  simp only [StatementActionPlan.preparedRowsList, List.mem_flatMap] at member
  obtain ⟨plan, planMember, rowMember⟩ := member
  exact (List.all_eq_true.mp
    (statementActionPlan_preparedRows_all_ground owner ownerGround plan
      ((List.all_eq_true.mp plansGround) plan planMember))) row rowMember

private theorem residualSourceActionPlans_all_ground
    {owner : Atom} (ownerGround : isGroundAtom owner = true)
    {statements : List
      Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.RawStatement}
    (actions : AdmittedSourceActionPlans owner statements) :
    (residualSourceActionPlans actions).all (fun plan =>
      plan.actions.all (fun action => isGroundAtom action.payload)) = true := by
  apply List.all_eq_true.mpr
  intro plan member
  rw [residualSourceActionPlans, List.mem_filter] at member
  exact (List.all_eq_true.mp
    (admitted_actions_all_ground ownerGround actions)) plan member.1

private theorem residualSourceActionRows_all_ground
    {owner : Atom} (ownerGround : isGroundAtom owner = true)
    {statements : List
      Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.RawStatement}
    (actions : AdmittedSourceActionPlans owner statements) :
    (residualSourceActionRows actions).all isGroundAtom = true := by
  exact preparedRowsList_all_ground owner ownerGround
    (residualSourceActionPlans actions)
    (residualSourceActionPlans_all_ground ownerGround actions)

private theorem runtimeActionKindRowsFrom_all_ground
    (actionOwner : Atom) (ownerGround : isGroundAtom actionOwner = true)
    (position : Nat) (actions : List RuntimeAction) :
    (runtimeActionKindRowsFrom actionOwner position actions).all
      isGroundAtom = true := by
  induction actions generalizing position with
  | nil => rfl
  | cons action actions induction =>
      cases action <;>
        simp [runtimeActionKindRowsFrom, runtimeActionKindRow,
          runtimeActionKind, isGroundAtom, isGroundAtom.isGroundList,
          ownerGround, induction]

private theorem statementActionPlanActionKindRows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (plan : StatementActionPlan) :
    (statementActionPlanActionKindRows owner plan).all isGroundAtom = true := by
  exact runtimeActionKindRowsFrom_all_ground
    (sourceActionOwner owner plan.position)
    (sourceActionOwner_ground owner ownerGround plan.position) 0 plan.actions

private theorem residualSourceActionKindRows_all_ground
    {owner : Atom} (ownerGround : isGroundAtom owner = true)
    {statements : List
      Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.RawStatement}
    (actions : AdmittedSourceActionPlans owner statements) :
    (residualSourceActionKindRows actions).all isGroundAtom = true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [residualSourceActionKindRows, List.mem_flatMap] at member
  obtain ⟨plan, _, rowMember⟩ := member
  exact (List.all_eq_true.mp
    (statementActionPlanActionKindRows_all_ground owner ownerGround plan)) row
      rowMember

private theorem sourceDVPairPlanOwner_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (position : Nat) :
    isGroundAtom (sourceDVPairPlanOwner owner position) = true := by
  simp [sourceDVPairPlanOwner, isGroundAtom, isGroundAtom.isGroundList,
    ownerGround]

private theorem sourceDVPairPlanRowsFrom_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (statementPosition pairPosition : Nat)
    (pairs : List MM2SourceDVPairPlan.DVPair) :
    (sourceDVPairPlanRowsFrom owner statementPosition pairPosition pairs).all
      isGroundAtom = true := by
  induction pairs generalizing pairPosition with
  | nil =>
      simp [sourceDVPairPlanRowsFrom, sourceDVPairPlanFrontierAtom,
        sourceDVPairPlanOwner_ground, isGroundAtom,
        isGroundAtom.isGroundList, ownerGround]
  | cons pair pairs induction =>
      simp only [sourceDVPairPlanRowsFrom, List.all_cons, Bool.and_eq_true]
      constructor
      · simp [sourceDVPairPlanLinkAtom,
        sourceDVPairPlanOwner_ground, stringPairAtom_ground,
        isGroundAtom, isGroundAtom.isGroundList, ownerGround]
      · exact induction (pairPosition := pairPosition + 1)

private theorem sourceDVPairPlan_rows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (plan : SourceDVPairPlan) :
    (plan.rows owner).all isGroundAtom = true := by
  simp only [SourceDVPairPlan.rows, List.all_cons, Bool.and_eq_true]
  constructor
  · simp [sourceDVPairPlanHeaderAtom, rawStatementAtom_ground,
      isGroundAtom, isGroundAtom.isGroundList, ownerGround]
  · exact sourceDVPairPlanRowsFrom_all_ground owner ownerGround
      plan.position 0 plan.pairs

private theorem sourceDVPairWitnessRowsFrom_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (statementPosition pairPosition : Nat)
    (witnesses : List SourceDVPairWitness) :
    (sourceDVPairWitnessRowsFrom owner statementPosition pairPosition
      witnesses).all isGroundAtom = true := by
  induction witnesses generalizing pairPosition with
  | nil => rfl
  | cons witness witnesses induction =>
      simp [sourceDVPairWitnessRowsFrom, sourceDVPairWitnessLinkAtom,
        sourceDVPairWitnessAtom, sourceDVPairPlanOwner_ground,
        stringPairAtom_ground, isGroundAtom, isGroundAtom.isGroundList,
        ownerGround, induction]

private theorem sourceDVPairPlan_witnessRows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (plan : SourceDVPairPlan) :
    (plan.witnessRows owner).all isGroundAtom = true :=
  sourceDVPairWitnessRowsFrom_all_ground owner ownerGround plan.position 0
    plan.witnesses

private theorem admittedDVPair_rows_all_ground
    {owner : Atom} (ownerGround : isGroundAtom owner = true)
    {statements : List
      Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.RawStatement}
    (input : AdmittedSourceDVPairPlans owner statements) :
    input.rows.all isGroundAtom = true := by
  apply List.all_eq_true.mpr
  intro row member
  simp only [AdmittedSourceDVPairPlans.rows, sourceDVPairPlanRows,
    List.mem_flatMap] at member
  obtain ⟨plan, _, rowMember⟩ := member
  exact (List.all_eq_true.mp
    (sourceDVPairPlan_rows_all_ground owner ownerGround plan)) row rowMember

private theorem admittedDVPair_witnessRows_all_ground
    {owner : Atom} (ownerGround : isGroundAtom owner = true)
    {statements : List
      Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.RawStatement}
    (input : AdmittedSourceDVPairPlans owner statements) :
    input.witnessRows.all isGroundAtom = true := by
  apply List.all_eq_true.mpr
  intro row member
  simp only [AdmittedSourceDVPairPlans.witnessRows,
    sourceDVPairPlanWitnessRows, List.mem_flatMap] at member
  obtain ⟨plan, _, rowMember⟩ := member
  exact (List.all_eq_true.mp
    (sourceDVPairPlan_witnessRows_all_ground owner ownerGround plan)) row
      rowMember

@[simp] private theorem sourceAssertionCandidateAtom_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (candidate : SourceAssertionCandidate) :
    isGroundAtom (sourceAssertionCandidateAtom owner candidate) = true := by
  have gateGround : isGroundAtom (sourceActionGateAtom candidate.gate) = true := by
    cases candidate.gate <;>
      simp [sourceActionGateAtom, isGroundAtom]
  simp [sourceAssertionCandidateAtom, gateGround, rawStatementAtom_ground,
    sourceAssertionAtom_ground, listAtom_ground,
    isGroundAtom, isGroundAtom.isGroundList, ownerGround]

private theorem admittedAssertionCandidates_rows_all_ground
    {owner : Atom} (ownerGround : isGroundAtom owner = true)
    {statements : List
      Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.RawStatement}
    (input : AdmittedSourceAssertionCandidates owner statements) :
    input.rows.all isGroundAtom = true := by
  simp [AdmittedSourceAssertionCandidates.rows,
    sourceAssertionCandidateAtom_ground, ownerGround]

private theorem assertionExecutionRowsFor_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (position : Nat) (assertion : SourceAssertion) :
    (assertionExecutionRowsFor owner position assertion).all isGroundAtom = true :=
  assertionExecutionRowsFor_ground owner ownerGround position assertion

private theorem assertionPublicationPlanRows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (candidate : SourceAssertionCandidate) :
    (assertionPublicationPlanRows owner candidate).all isGroundAtom = true := by
  have payloadGround :
      (assertionPublicationPayloadRows owner candidate).all isGroundAtom = true :=
    assertionExecutionRowsFor_all_ground owner ownerGround
      candidate.assertionPosition candidate.assertion
  have linkedGround :
      (assertionPublicationLinkedRows owner candidate).all isGroundAtom = true := by
    apply linkedRows_all_ground
    · simp [assertionPublicationOwnerAtom, isGroundAtom,
        isGroundAtom.isGroundList, ownerGround]
    · simpa using payloadGround
  have successorGround :
      (assertionPublicationSuccessorRows owner candidate).all
        isGroundAtom = true := by
    apply indexSuccessorRows_all_ground
    simp [assertionPublicationOwnerAtom, isGroundAtom,
      isGroundAtom.isGroundList, ownerGround]
  simp [assertionPublicationPlanRows, assertionPublicationHeaderAtom,
    sourceAssertionAtom_ground, rawStatementAtom_ground,
    isGroundAtom, isGroundAtom.isGroundList, ownerGround,
    linkedGround, successorGround]

private theorem nativeAssertionPublicationRows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (candidates : List SourceAssertionCandidate) :
    (nativeAssertionPublicationRows owner candidates).all isGroundAtom = true := by
  apply List.all_eq_true.mpr
  intro row member
  obtain ⟨candidate, _, _, rowMember⟩ :=
    mem_nativeAssertionPublicationRows member
  exact (List.all_eq_true.mp
    (assertionPublicationPlanRows_all_ground owner ownerGround candidate)) row
      rowMember

private theorem essentialCandidateRow?_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (plan : StatementActionPlan)
    (actionsGround : plan.actions.all
      (fun action => isGroundAtom action.payload) = true)
    (row : Atom) (derived : essentialCandidateRow? owner plan = some row) :
    isGroundAtom row = true := by
  unfold essentialCandidateRow? at derived
  split at derived <;> simp_all
  rename_i statement label candidateFormula actualOwner actualLabel
  obtain ⟨_, rfl⟩ := derived
  have formulaGround : isGroundAtom candidateFormula = true := by
    simpa [RuntimeAction.payload, isGroundAtom, isGroundAtom.isGroundList,
      ownerGround] using actionsGround
  simp [essentialCandidateAtom, rawStatementAtom_ground,
    formulaGround, isGroundAtom, isGroundAtom.isGroundList, ownerGround]

private theorem essentialCandidateRows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (plans : List StatementActionPlan)
    (plansGround : plans.all (fun plan => plan.actions.all
      (fun action => isGroundAtom action.payload)) = true) :
    (essentialCandidateRows owner plans).all isGroundAtom = true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [essentialCandidateRows, List.mem_filterMap] at member
  obtain ⟨plan, planMember, derived⟩ := member
  exact essentialCandidateRow?_ground owner ownerGround plan
    ((List.all_eq_true.mp plansGround) plan planMember) row derived

private theorem sourcePreparedTheoremRow_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (position nextPosition : Nat) (statement : RawStatement)
    (obligation : TheoremObligation) :
    isGroundAtom
      (sourcePreparedTheoremRow owner position nextPosition statement
        obligation) = true := by
  simp [sourcePreparedTheoremRow, sourcePreparedTheoremFact,
    sourceProofOwnerAtom_ground, rawStatementAtom_ground,
    formulaAtom_ground, isGroundAtom, isGroundAtom.isGroundList,
    ownerGround]

private theorem sourcePreparedAssertionHeaderRow_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (position : Nat)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (obligation : TheoremObligation) :
    isGroundAtom
      (sourcePreparedAssertionHeaderRow owner position state obligation) =
        true := by
  let assertion := sourceAssertion state obligation.label.name
    obligation.formula
  have headerGround :
      isGroundAtom
        (assertionHeaderRow owner state.assertions.length assertion) = true :=
    (List.all_eq_true.mp
      (assertionExecutionRowsFor_ground owner ownerGround
        state.assertions.length assertion)) _ (by
          simp [assertionExecutionRowsFor])
  simp [sourcePreparedAssertionHeaderRow,
    sourcePreparedAssertionHeaderFact, assertion, headerGround,
    sourceProofOwnerAtom_ground, isGroundAtom, isGroundAtom.isGroundList,
    ownerGround]

private theorem sourcePreparedAssertionSupportRows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (position : Nat)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (obligation : TheoremObligation) :
    (sourcePreparedAssertionSupportRows owner position state obligation).all
      isGroundAtom = true := by
  let assertion := sourceAssertion state obligation.label.name
    obligation.formula
  apply List.all_eq_true.mpr
  intro row member
  have tailMember :
      row ∈ (assertionExecutionRowsFor owner state.assertions.length
        assertion).tail := by
    simpa [sourcePreparedAssertionSupportRows, assertion] using member
  exact (List.all_eq_true.mp
    (assertionExecutionRowsFor_ground owner ownerGround
      state.assertions.length assertion)) row
        (List.mem_of_mem_tail tailMember)

private theorem sourcePreparedProofRows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (position : Nat)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (obligation : TheoremObligation) :
    (sourcePreparedProofRows owner position state obligation).all
      isGroundAtom = true := by
  rcases obligation with ⟨site, label, formula, proof⟩
  have proofOwnerGround := sourceProofOwnerAtom_ground owner ownerGround position
  cases proof with
  | normal steps =>
      have inputGround := proofInputRows_all_ground owner
        (sourceProofOwnerAtom owner position) ownerGround proofOwnerGround
        (.normal label.name formula (steps.map (·.name)))
      have inventoryGround := normalLabelInventoryRows_all_ground
        (sourceProofOwnerAtom owner position) proofOwnerGround state
      simp [sourcePreparedProofRows, inputGround, inventoryGround]
  | compressed openParen header closeParen words =>
      simpa only [sourcePreparedProofRows] using
        transformedCompressedProofData_rows_all_ground owner
          (sourceProofOwnerAtom owner position) ownerGround proofOwnerGround state
          label.name formula (header.map (·.name)) (words.map (·.bytes))

private theorem sourcePreparedTheoremRows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (position nextPosition : Nat) (statement : RawStatement)
    (state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState)
    (obligation : TheoremObligation) :
    (sourcePreparedTheoremRows owner position nextPosition statement state
      obligation).all isGroundAtom = true := by
  simp [sourcePreparedTheoremRows,
    sourcePreparedTheoremRow_ground owner ownerGround,
    sourcePreparedProofRows_all_ground owner ownerGround,
    sourcePreparedAssertionHeaderRow_ground owner ownerGround,
    sourcePreparedAssertionSupportRows_all_ground owner ownerGround]

private theorem sourceDerivedProofRows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (statements : List RawStatement) (rows : List Atom)
    (derived : sourceDerivedProofRows owner statements = .ok rows) :
    rows.all isGroundAtom = true := by
  exact sourceDerivedProofRows_all_of owner isGroundAtom
    (sourcePreparedTheoremRows_all_ground owner ownerGround) statements rows
    derived

private theorem canonicalSourceEventRows_all_ground
    (owner : Atom) (ownerGround : isGroundAtom owner = true)
    (statements : List RawStatement) :
    (sourceEventStartRow owner :: sourceEventRows owner statements ++
      [sourceEventEndRow owner statements]).all isGroundAtom = true := by
  have payloadGround :
      statements.all (fun statement => isGroundAtom (rawStatementAtom statement)) =
        true := by simp
  have rowsGround := linkedRows_all_ground "source-statement" owner ownerGround
    rawStatementAtom statements payloadGround
  simp [sourceEventRows_eq_linkedRows, sourceEventStartRow,
    sourceEventEndRow, isGroundAtom, isGroundAtom.isGroundList,
    ownerGround, rowsGround]

/-- Canonical public source-event rows are ground whenever their owner is
ground. -/
theorem AdmittedSourceEventInput.rows_all_ground
    {owner : Atom} (ownerGround : isGroundAtom owner = true)
    (input : AdmittedSourceEventInput owner) :
    input.rows.all isGroundAtom = true := by
  rw [input.canonical]
  exact canonicalSourceEventRows_all_ground owner ownerGround input.statements

/-- Groundness of an admitted initial source artifact reduces exactly to its
recomputed theorem-proof rows; the public ordered event envelope is already
ground by construction. -/
theorem AdmittedSourceEventInput.initialRows_all_ground_iff_derivedRows
    {owner : Atom} (ownerGround : isGroundAtom owner = true)
    (input : AdmittedSourceEventInput owner) :
    input.initialRows.all isGroundAtom = true ↔
      input.derivedRows.all isGroundAtom = true := by
  simp [AdmittedSourceEventInput.initialRows,
    AdmittedSourceEventInput.rows_all_ground ownerGround input]

/-- Both the canonical event envelope and every proof-syntax packet recomputed
from it are ground. -/
theorem AdmittedSourceEventInput.initialRows_all_ground
    {owner : Atom} (ownerGround : isGroundAtom owner = true)
    (input : AdmittedSourceEventInput owner) :
    input.initialRows.all isGroundAtom = true := by
  exact (AdmittedSourceEventInput.initialRows_all_ground_iff_derivedRows
    ownerGround input).2 (sourceDerivedProofRows_all_ground owner ownerGround
      input.statements input.derivedRows input.derivedExact)

private theorem deferProofControlRow_ground (row : Atom)
    (ground : isGroundAtom row = true) :
    isGroundAtom (deferProofControlRow row) = true := by
  unfold deferProofControlRow
  split <;> simp_all [isGroundAtom, isGroundAtom.isGroundList]

private theorem deferProofControls_all_ground (rows : List Atom)
    (ground : rows.all isGroundAtom = true) :
    (deferProofControls rows).all isGroundAtom = true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [deferProofControls, List.mem_map] at member
  obtain ⟨source, sourceMember, rfl⟩ := member
  exact deferProofControlRow_ground source
    ((List.all_eq_true.mp ground) source sourceMember)

private theorem deferCompressedHeaderControlRow_ground (row : Atom)
    (ground : isGroundAtom row = true) :
    isGroundAtom (deferCompressedHeaderControlRow row) = true := by
  unfold deferCompressedHeaderControlRow
  split <;> simp_all [isGroundAtom, isGroundAtom.isGroundList]

private theorem deferCompressedHeaderControls_all_ground (rows : List Atom)
    (ground : rows.all isGroundAtom = true) :
    (deferCompressedHeaderControls rows).all isGroundAtom = true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [deferCompressedHeaderControls, List.mem_map] at member
  obtain ⟨source, sourceMember, rfl⟩ := member
  exact deferCompressedHeaderControlRow_ground source
    ((List.all_eq_true.mp ground) source sourceMember)

/-- Ground atoms cannot contain a variable-headed expression. -/
private theorem fixedExpressionHeads_of_ground :
    ∀ atom : Atom, isGroundAtom atom = true → fixedExpressionHeads atom = true
  | .var _, ground => by simp [isGroundAtom] at ground
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression children, ground => by
      cases children with
      | nil => rfl
      | cons head tail =>
          cases head with
          | var name => simp [isGroundAtom, isGroundAtom.isGroundList] at ground
          | symbol name =>
              simp only [fixedExpressionHeads]
              exact fixedExpressionHeadsList_of_ground (.symbol name :: tail)
                ground
          | grounded value =>
              simp only [fixedExpressionHeads]
              exact fixedExpressionHeadsList_of_ground (.grounded value :: tail)
                ground
          | expression inner =>
              simp only [fixedExpressionHeads]
              exact fixedExpressionHeadsList_of_ground (.expression inner :: tail)
                ground
where
  fixedExpressionHeadsList_of_ground : ∀ atoms : List Atom,
      isGroundAtom.isGroundList atoms = true →
        fixedExpressionHeadsList atoms = true
    | [], _ => rfl
    | atom :: atoms, ground => by
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp [fixedExpressionHeadsList,
          fixedExpressionHeads_of_ground atom ground.1,
          fixedExpressionHeadsList_of_ground atoms ground.2]

/-- If the admitted source-event encoder is ground, every additional row
derived by the source-data transform is ground as well.  The premise isolates
the raw-event encoder from the action, DV, assertion, and ledger encoders proved
in this module. -/
theorem sourceDataProgram_all_ground_of_initialRows_ground
    {owner : Atom} (ownerAuthorized : SourceOwnerLineageAuthorized owner)
    (input : AdmittedSourceEventInput owner)
    (initialRowsGround : input.initialRows.all isGroundAtom = true)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    (sourceDataProgram input actions).all isGroundAtom = true := by
  let dvPlans := admitSourceDVPairPlans actions
  let assertionCandidates := admitSourceAssertionCandidatesFromActions actions
  have deferredGround :
      (deferCompressedHeaderControls
        (deferProofControls input.initialRows)).all isGroundAtom = true :=
    deferCompressedHeaderControls_all_ground _
      (deferProofControls_all_ground _ initialRowsGround)
  have plansGround := admitted_actions_all_ground ownerAuthorized.1 actions
  have dvRowsGround := admittedDVPair_rows_all_ground ownerAuthorized.1 dvPlans
  have dvWitnessGround :=
    admittedDVPair_witnessRows_all_ground ownerAuthorized.1 dvPlans
  have candidateRowsGround :=
    admittedAssertionCandidates_rows_all_ground ownerAuthorized.1
      assertionCandidates
  have publicationRowsGround := nativeAssertionPublicationRows_all_ground owner
    ownerAuthorized.1 assertionCandidates.candidates
  have essentialRowsGround := essentialCandidateRows_all_ground owner
    ownerAuthorized.1 actions.plans plansGround
  have residualRowsGround :=
    residualSourceActionRows_all_ground ownerAuthorized.1 actions
  have residualKindsGround :=
    residualSourceActionKindRows_all_ground ownerAuthorized.1 actions
  simp [sourceDataProgram, dvPlans, assertionCandidates, deferredGround,
    dvRowsGround, dvWitnessGround, candidateRowsGround,
    publicationRowsGround, essentialRowsGround, residualRowsGround,
    residualKindsGround,
    objectInventoryRows, objectInventoryRowsFrom, objectFrontierAtom,
    objectRootKey,
    activeVariableRows, activeVariableLedgerOwner,
    variableTypecodeLedgerRows, variableTypecodeLedgerOwner,
    variableTypecodeInventoryRows,
    variableTypecodeBindingRows, emptyScopedActivityRows,
    activeHypothesisLedgerOwner, activeDistinctLedgerOwner,
    sourceActivityFrontierAtom, dvOccurrenceRows, dvOccurrenceRowsFrom,
    dvOccurrenceFrontierAtom, dvOccurrenceFrontierAtAtom,
    isGroundAtom, isGroundAtom.isGroundList, ownerAuthorized.1]

/-- The only remaining groundness premise for the complete source-data output
is the recomputed theorem-proof row list. -/
theorem sourceDataProgram_all_ground_of_derivedRows_ground
    {owner : Atom} (ownerAuthorized : SourceOwnerLineageAuthorized owner)
    (input : AdmittedSourceEventInput owner)
    (derivedRowsGround : input.derivedRows.all isGroundAtom = true)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    (sourceDataProgram input actions).all isGroundAtom = true := by
  exact sourceDataProgram_all_ground_of_initialRows_ground ownerAuthorized input
      ((AdmittedSourceEventInput.initialRows_all_ground_iff_derivedRows
        ownerAuthorized.1 input).2 derivedRowsGround) actions

/-- The complete source-data transformation is ground. -/
theorem sourceDataProgram_all_ground
    {owner : Atom} (ownerAuthorized : SourceOwnerLineageAuthorized owner)
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    (sourceDataProgram input actions).all isGroundAtom = true := by
  exact sourceDataProgram_all_ground_of_initialRows_ground ownerAuthorized input
    (AdmittedSourceEventInput.initialRows_all_ground ownerAuthorized.1 input)
    actions

/-- Under the same encoder premise, the source-data transform preserves fixed
expression heads. -/
theorem sourceDataProgram_fixedExpressionHeads_of_initialRows_ground
    {owner : Atom} (ownerAuthorized : SourceOwnerLineageAuthorized owner)
    (input : AdmittedSourceEventInput owner)
    (initialRowsGround : input.initialRows.all isGroundAtom = true)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    (sourceDataProgram input actions).all fixedExpressionHeads = true := by
  apply List.all_eq_true.mpr
  intro row member
  exact fixedExpressionHeads_of_ground row
    ((List.all_eq_true.mp
      (sourceDataProgram_all_ground_of_initialRows_ground ownerAuthorized input
        initialRowsGround actions)) row member)

/-- The complete source-data transformation contains no variable-headed
expression. -/
theorem sourceDataProgram_fixedExpressionHeads
    {owner : Atom} (ownerAuthorized : SourceOwnerLineageAuthorized owner)
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    (sourceDataProgram input actions).all fixedExpressionHeads = true := by
  exact sourceDataProgram_fixedExpressionHeads_of_initialRows_ground
    ownerAuthorized input
    (AdmittedSourceEventInput.initialRows_all_ground ownerAuthorized.1 input)
    actions

/-- The actual composition of the fixed verifier transform with an admitted
source-data transform contains no variable-headed expression. -/
theorem composeProgram_fixedExpressionHeads
    {owner : Atom} (ownerAuthorized : SourceOwnerLineageAuthorized owner)
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    (composeProgram authoredMetamathVerifierGSLT input actions).all
      fixedExpressionHeads = true := by
  simp [composeProgram, genericVerifierProgram_fixedExpressionHeads,
    sourceDataProgram_fixedExpressionHeads ownerAuthorized input actions]

/-! ## Controls and axiom audit -/

example : SourceOwnerLineageAuthorized (.symbol "mm-unit-owner") := by
  simp [SourceOwnerLineageAuthorized, isGroundAtom,
    executableSchemaTemplateSafe]

example : SourceOwnerLineageAuthorized (stringAtom "metamath-unit") := by
  simp [SourceOwnerLineageAuthorized]

example : ¬ SourceOwnerLineageAuthorized (.var "owner") := by
  intro authorized
  simp [SourceOwnerLineageAuthorized, isGroundAtom] at authorized

example :
    fixedExpressionHeads
      (.expression [.symbol "fixed-head", .var "payload"]) = true := by
  rfl

example :
    fixedExpressionHeads
      (.expression [.var "variable-head", .symbol "payload"]) = false := by
  rfl

section AxiomAudit

#print axioms AdmittedSourceEventInput.rows_all_ground
#print axioms AdmittedSourceEventInput.initialRows_all_ground
#print axioms AdmittedSourceEventInput.initialRows_all_schemaSafe
#print axioms sourceDataProgram_all_schemaSafe
#print axioms sourceDataProgram_executable_lineageAuthorized
#print axioms composeProgram_executable_lineageAuthorized
#print axioms composeProgram_runN_executable_lineageAuthorized
#print axioms sourceDataProgram_all_ground
#print axioms sourceDataProgram_fixedExpressionHeads
#print axioms composeProgram_fixedExpressionHeads

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2TwoTransformLineageClosure
