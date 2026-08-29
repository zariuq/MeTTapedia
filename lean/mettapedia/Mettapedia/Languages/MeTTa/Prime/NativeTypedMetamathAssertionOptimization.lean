import Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationImplementationModel
import Mettapedia.Languages.Metamath.InferenceGeneratedProvesReceipt
import Mettapedia.Languages.Metamath.InferencePreparedAssertionCompilation
import Mettapedia.Languages.Metamath.InferencePreparedAssertionStepReceipt

open Mettapedia.GSLT.LanguageDef

/-!
# Prime/NIK admission of prepared Metamath assertion records

The source-owned Metamath projection proves unique stored assertion labels;
the generic compiler turns that exact snapshot into an immutable record index;
and Prime/NIK admits the resulting observed refinement at the complete source
occurrence and revision key.

This is deliberately distinct from indexing the GSLT grammar's operation
records.  Here each value is a particular projected `AssertionView`, and the
downstream theorem selects that record before applying its independently
proved fused substitution semantics.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeTypedMetamathAssertionOptimization

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation
open Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationAdmission
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationNIKBridge
open Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceAssertionFusedCompilation
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
open Mettapedia.Languages.Metamath.InferencePreparedAssertionCompilation
open Mettapedia.Languages.Metamath.InferencePreparedAssertionStepReceipt

abbrev spec :=
  SingleValuedDispatch.spec (Key := String) (Value := AssertionView)

abbrev source (projection : PrefixProjection) (queries : List String) :=
  assertionRecordSource projection queries

private theorem recognitionSucceeded
    (projection : PrefixProjection) (queries : List String)
    (valid : prefixProjectionValid projection = true) :
    (SingleValuedDispatch.recognize (source projection queries)).isSome =
      true := by
  unfold SingleValuedDispatch.recognize
  split <;>
    simp_all [source, assertionRecordSource,
      assertionIndexShape_recognized,
      assertionRecordKeys_allDistinct projection valid]

/-- The common optimization witness is computed by the common recognizer from
the exact projected assertion table. -/
def evidence (projection : PrefixProjection) (queries : List String)
    (valid : prefixProjectionValid projection = true) :
    SingleValuedDispatch.Evidence (source projection queries) :=
  (SingleValuedDispatch.recognize (source projection queries)).get
    (recognitionSucceeded projection queries valid)

theorem recognized
    (projection : PrefixProjection) (queries : List String)
    (valid : prefixProjectionValid projection = true) :
    spec.recognize (source projection queries) =
      some (evidence projection queries valid) := by
  change SingleValuedDispatch.recognize (source projection queries) =
    some (evidence projection queries valid)
  exact (Option.some_get (recognitionSucceeded projection queries valid)).symm

/-- Exact authority binds the particular projected record table, its requested
label occurrences, and the logical source revision. -/
def nativeKey (projection : PrefixProjection) (queries : List String)
    (revision : Nat) : OptimizationKey (SourceProgram String AssertionView) :=
  { occurrence := (.singleValuedDispatch, source projection queries)
    revision := revision
    dialect := "metamath-inference"
    expected := .prim .sym
    authority := "prime-native-projected-assertion-records" }

def nativeAuthority (projection : PrefixProjection) (queries : List String)
    (revision : Nat) : ExactAuthority spec
      (source projection queries) where
  key := nativeKey projection queries revision
  occurrence_eq := rfl
  judgment := SingleValuedDispatch.nativeJudgment
    (source projection queries) (nativeKey projection queries revision)
      (by simp [nativeKey,
        Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Seam.exactTy])

def candidate (projection : PrefixProjection) (queries : List String)
    (revision : Nat) : KeyedCandidate spec :=
  KeyedCandidate.ofAuthority spec
    (nativeAuthority projection queries revision)

def authority (projection : PrefixProjection) (queries : List String)
    (revision : Nat) : AlignedAuthority
      (candidate projection queries revision) :=
  AlignedAuthority.ofAuthority spec
    (nativeAuthority projection queries revision)

/-- Prepared assertion-record selection is an ordinary member of the common
NIK optimization family.  Native and generic preparation select the same
projection-derived evidence. -/
theorem enters_common_nik_family
    (projection : PrefixProjection) (queries : List String)
    (revision : Nat) (valid : prefixProjectionValid projection = true) :
    prepareAtKey spec (candidate projection queries revision)
        (some (authority projection queries revision)) =
          .optimized (authority projection queries revision)
            (evidence projection queries valid) ∧
      NativeTypedOptimizationAdmission.prepare spec
          (source projection queries)
          (some (nativeAuthority projection queries revision)) =
        ExecutionPlan.optimized
          (nativeAuthority projection queries revision)
          (evidence projection queries valid) :=
  recognized_preparations_agree spec
    (candidate projection queries revision)
    (authority projection queries revision)
    (evidence projection queries valid)
    (recognized projection queries valid)

/-- The admitted artifact has exactly the source scan's ordered optional
record observations, including repeated queries and absent labels. -/
theorem admitted_records_observe_source
    (projection : PrefixProjection) (queries : List String)
    (valid : prefixProjectionValid projection = true) :
    spec.observeArtifact (source projection queries)
        (spec.compile (source projection queries)
          (evidence projection queries valid)) =
      spec.observeSource (source projection queries) :=
  spec.adequate (source projection queries) (evidence projection queries valid)

/-- End-to-end live-prefix theorem: the same projection gate both admits the
NIK record-selection refinement and licenses fused application of the exact
selected record.  No independent assertion-index or substitution certificate
is assumed. -/
theorem projected_admission_and_fused_application
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (projected : projectPrefix? db = some projection)
    (member : assertion ∈ projection.assertions)
    (queries : List String) (revision : Nat)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) :
    ∃ valid : prefixProjectionValid projection = true,
      (prepareAtKey spec (candidate projection queries revision)
            (some (authority projection queries revision)) =
          .optimized (authority projection queries revision)
            (evidence projection queries valid) ∧
        NativeTypedOptimizationAdmission.prepare spec
              (source projection queries)
              (some (nativeAuthority projection queries revision)) =
          ExecutionPlan.optimized
            (nativeAuthority projection queries revision)
            (evidence projection queries valid)) ∧
      compiledAssertionRecord? projection assertion.label = some assertion ∧
        (AssertionApplicationSemantics projection.callerFrame assertion actuals
              result ↔
          FusedAssertionApplicationSemantics projection.callerFrame assertion
            actuals result) := by
  let valid :=
    prefixProjectionValid_of_projectPrefix?_eq_some db projection projected
  exact ⟨valid,
    enters_common_nik_family projection queries revision valid,
    projected_preparedAssertionApplication db projection assertion projected
      member actuals result⟩

/-- Profitability is a subsequent receipt, not part of the semantic authority
which admitted exact record selection. -/
def profitability
    (projection : PrefixProjection) (queries : List String)
    (revision : Nat) (valid : prefixProjectionValid projection = true) :
    ProfitabilityReceipt spec (source projection queries)
      (nativeAuthority projection queries revision)
      (evidence projection queries valid) where
  key := (nativeAuthority projection queries revision).key
  same_key := rfl
  baseline := spec.sourceWorkSpan (source projection queries)
  optimized := spec.artifactWorkSpan (source projection queries)
    (spec.compile (source projection queries) (evidence projection queries valid))
  baseline_eq := rfl
  optimized_eq := rfl
  improves :=
    SingleValuedDispatch.artifactWorkSpan_le_sourceWorkSpan
      (source projection queries) (evidence projection queries valid)

def pathProfitability
    (projection : PrefixProjection) (queries : List String)
    (revision : Nat) (valid : prefixProjectionValid projection = true) :=
  NativeTypedOptimizationNIKBridge.profitabilityReceipt spec
    (candidate projection queries revision)
    (authority projection queries revision)
    (evidence projection queries valid)
    (profitability projection queries revision valid)

/-! ## Abstract implementation-model instance -/

/-- The admitted prepared-record refinement inhabits the common Prime
implementation contract with exact raw fallback and exact artifact receipts. -/
def implementationModel
    (projection : PrefixProjection) (queries : List String)
    (revision : Nat) (valid : prefixProjectionValid projection = true) :=
  NativeTypedOptimizationImplementationModel.model spec
    (candidate projection queries revision)
    (authority projection queries revision)
    (evidence projection queries valid)

/-- The exact source occurrence retained by preparation. -/
def sourceOccurrence
    (projection : PrefixProjection) (queries : List String)
    (revision : Nat) : ExactOccurrence (candidate projection queries revision) :=
  ⟨source projection queries, rfl⟩

def preparedSourceTrace
    (projection : PrefixProjection) (queries : List String)
    (revision : Nat) (valid : prefixProjectionValid projection = true) :=
  (implementationModel projection queries revision valid).prepare
    ⟨sourceOccurrence projection queries revision,
      sourceOccurrence projection queries revision,
      .refl (sourceOccurrence projection queries revision)⟩

/-- Current hot execution maps the exact projected source occurrence directly
to the immutable assertion-record artifact retained by the specification. -/
theorem implementation_compiles_prepared_records
    (projection : PrefixProjection) (queries : List String)
    (revision : Nat) (valid : prefixProjectionValid projection = true) :
    (implementationModel projection queries revision valid).compileTrace
        (NativeTypedOptimizationImplementationModel.active spec
          (candidate projection queries revision)
          (authority projection queries revision)
          (evidence projection queries valid))
        ⟨sourceOccurrence projection queries revision,
          sourceOccurrence projection queries revision,
          .refl (sourceOccurrence projection queries revision)⟩ =
      ⟨spec.compile (source projection queries)
          (evidence projection queries valid),
        spec.compile (source projection queries)
          (evidence projection queries valid),
        .refl (spec.compile (source projection queries)
          (evidence projection queries valid))⟩ := by
  exact NativeTypedOptimizationImplementationModel.compile_occurrence spec
    (candidate projection queries revision)
    (authority projection queries revision)
    (evidence projection queries valid)
    (sourceOccurrence projection queries revision)

/-- The complete source record program is independently recoverable from the
prepared trace, regardless of whether native execution remains current. -/
theorem implementation_fallback_exact
    (projection : PrefixProjection) (queries : List String)
    (revision : Nat) (valid : prefixProjectionValid projection = true) :
    (implementationModel projection queries revision valid).rawCodec.decode
        (preparedSourceTrace projection queries revision valid).fallback =
      (preparedSourceTrace projection queries revision valid).sourceTrace := by
  exact (preparedSourceTrace projection queries revision valid).fallback_adequate

/-- A concrete revision change with every other key coordinate retained. -/
def nextRevisionKey
    (projection : PrefixProjection) (queries : List String)
    (revision : Nat) :=
  { (candidate projection queries revision).key with
    revision := revision + 1 }

theorem candidate_key_ne_nextRevisionKey
    (projection : PrefixProjection) (queries : List String)
    (revision : Nat) :
    (candidate projection queries revision).key ≠
      nextRevisionKey projection queries revision := by
  intro same
  have revisionEq := congrArg
    (fun key => key.revision) same
  simp [candidate, KeyedCandidate.ofAuthority, nativeAuthority,
    nativeKey, nextRevisionKey] at revisionEq

/-- Stale prepared records cannot activate, but the exact raw source trace
remains available for deoptimization. -/
theorem changed_revision_refuses_activation_and_preserves_fallback
    (projection : PrefixProjection) (queries : List String)
    (revision : Nat) (valid : prefixProjectionValid projection = true) :
    (¬ (implementationModel projection queries revision valid).admission.Active
        (nextRevisionKey projection queries revision)) ∧
      (implementationModel projection queries revision valid).rawCodec.decode
          (preparedSourceTrace projection queries revision valid).fallback =
        (preparedSourceTrace projection queries revision valid).sourceTrace := by
  exact
    NativeTypedOptimizationImplementationModel.changed_key_prevents_activation_and_preserves_fallback
      spec
      (candidate projection queries revision)
      (authority projection queries revision)
      (evidence projection queries valid)
      (nextRevisionKey projection queries revision)
      (candidate_key_ne_nextRevisionKey projection queries revision)
      (preparedSourceTrace projection queries revision valid)

/-! ## Current admitted execution and operational deoptimization -/

/-- Projection currentness already retained by an operational receipt supplies
the exact validity witness consumed by the optimization admission. -/
def receiptValidity
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedCalculusLanguageDef} {assertion : AssertionView}
    {pr : RuntimeProofState} {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula} {substitution : FiniteSubstitution}
    (receipt : PreparedAssertionStepReceipt db projection target assertion pr
      actuals result substitution) :
    prefixProjectionValid projection = true :=
  prefixProjectionValid_of_projectPrefix?_eq_some db projection
    receipt.projected

/-- One current native plan for the queried assertion occurrence together
with the complete proof-relevant operational receipt it realizes.  The query
is the exact assertion label rather than an unrelated table observation. -/
structure CurrentPreparedAssertionStep
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef) (assertion : AssertionView)
    (pr : RuntimeProofState) (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) (substitution : FiniteSubstitution)
    (revision : Nat) : Type where
  receipt : PreparedAssertionStepReceipt db projection target assertion pr
    actuals result substitution
  active :
    (implementationModel projection [assertion.label] revision
      (receiptValidity receipt)).admission.Active
        (candidate projection [assertion.label] revision).key

/-- Admission is constructed once from the exact projected occurrence.  The
operational receipt itself is preserved rather than replaced by a token. -/
def admitPreparedAssertionStep
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedCalculusLanguageDef} {assertion : AssertionView}
    {pr : RuntimeProofState} {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula} {substitution : FiniteSubstitution}
    (revision : Nat)
    (receipt : PreparedAssertionStepReceipt db projection target assertion pr
      actuals result substitution) :
    CurrentPreparedAssertionStep db projection target assertion pr actuals
      result substitution revision where
  receipt := receipt
  active := NativeTypedOptimizationImplementationModel.active spec
    (candidate projection [assertion.label] revision)
    (authority projection [assertion.label] revision)
    (evidence projection [assertion.label] (receiptValidity receipt))

/-- Revision staleness refuses the native activation while preserving both
fallback layers: the exact source record trace and the ordinary live verifier
step with the same complete proof-state result. -/
theorem changed_revision_deoptimizes_to_exact_live_step
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedCalculusLanguageDef} {assertion : AssertionView}
    {pr : RuntimeProofState} {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula} {substitution : FiniteSubstitution}
    (revision : Nat)
    (current : CurrentPreparedAssertionStep db projection target assertion pr
      actuals result substitution revision) :
    (¬ (implementationModel projection [assertion.label] revision
          (receiptValidity current.receipt)).admission.Active
        (nextRevisionKey projection [assertion.label] revision)) ∧
      db.stepNormal pr assertion.label =
        .ok (assertionStepResult pr assertion result) ∧
      (implementationModel projection [assertion.label] revision
          (receiptValidity current.receipt)).rawCodec.decode
          (preparedSourceTrace projection [assertion.label] revision
            (receiptValidity current.receipt)).fallback =
        (preparedSourceTrace projection [assertion.label] revision
          (receiptValidity current.receipt)).sourceTrace := by
  have staleFallback :=
    changed_revision_refuses_activation_and_preserves_fallback projection
      [assertion.label] revision (receiptValidity current.receipt)
  exact ⟨staleFallback.1, current.receipt.stepNormal_ok, staleFallback.2⟩

/-! ## Whole-proof currentness and deoptimization -/

/-- Currentness for one assertion occurrence is tied to that exact operational
receipt, not merely another occurrence with the same label. -/
structure CurrentAssertionReceiptAdmission
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedCalculusLanguageDef} {assertion : AssertionView}
    {pr : RuntimeProofState} {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula} {substitution : FiniteSubstitution}
    (receipt : PreparedAssertionStepReceipt db projection target assertion pr
      actuals result substitution)
    (revision : Nat) : Type where
  current : CurrentPreparedAssertionStep db projection target assertion pr
    actuals result substitution revision
  receipt_eq : current.receipt = receipt

def admitAssertionReceipt
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedCalculusLanguageDef} {assertion : AssertionView}
    {pr : RuntimeProofState} {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula} {substitution : FiniteSubstitution}
    (revision : Nat)
    (receipt : PreparedAssertionStepReceipt db projection target assertion pr
      actuals result substitution) :
    CurrentAssertionReceiptAdmission receipt revision where
  current := admitPreparedAssertionStep revision receipt
  receipt_eq := rfl

mutual

/-- Add current NIK admission exactly at assertion occurrences of a retained
proof receipt.  Active-hypothesis leaves require no assertion optimization. -/
def admittedTreeReceiptShape
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    {db : RuntimeDB} {pr : RuntimeProofState}
    (receipts : tree.receiptShape db pr) (revision : Nat) : Type :=
  match tree with
  | .active _ _ => PUnit
  | .assertion _ _ children =>
      admittedForestReceiptShape children receipts.1 revision ×
        CurrentAssertionReceiptAdmission receipts.2 revision

/-- Preserve exact premise order while admitting every nested assertion
occurrence. -/
def admittedForestReceiptShape
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas)
    {db : RuntimeDB} {pr : RuntimeProofState}
    (receipts : forest.receiptShape db pr) (revision : Nat) : Type :=
  match forest with
  | .nil => PUnit
  | .cons head tail =>
      admittedTreeReceiptShape head receipts.1 revision ×
        admittedForestReceiptShape tail receipts.2 revision

end

mutual

def admitTreeReceipts
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    {db : RuntimeDB} {pr : RuntimeProofState}
    (receipts : tree.receiptShape db pr) (revision : Nat) :
    admittedTreeReceiptShape tree receipts revision := by
  cases tree with
  | active => exact PUnit.unit
  | assertion member node children =>
      exact ⟨admitForestReceipts children receipts.1 revision,
        admitAssertionReceipt revision receipts.2⟩

def admitForestReceipts
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas)
    {db : RuntimeDB} {pr : RuntimeProofState}
    (receipts : forest.receiptShape db pr) (revision : Nat) :
    admittedForestReceiptShape forest receipts revision := by
  cases forest with
  | nil => exact PUnit.unit
  | cons head tail =>
      exact ⟨admitTreeReceipts head receipts.1 revision,
        admitForestReceipts tail receipts.2 revision⟩

end

mutual

/-- Every assertion occurrence in the admitted receipt has become stale at
the successor revision.  This is structural: duplicate labels remain separate
conjuncts because they remain separate tree occurrences. -/
def allAssertionsStaleAtNext
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    {db : RuntimeDB} {pr : RuntimeProofState}
    (receipts : tree.receiptShape db pr) (revision : Nat)
    (admitted : admittedTreeReceiptShape tree receipts revision) : Prop :=
  match tree with
  | .active _ _ => True
  | .assertion (assertion := assertion) _ _ children =>
      allForestAssertionsStaleAtNext children receipts.1 revision admitted.1 ∧
        ¬ (implementationModel projection [assertion.label] revision
            (receiptValidity admitted.2.current.receipt)).admission.Active
          (nextRevisionKey projection [assertion.label] revision)

def allForestAssertionsStaleAtNext
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas)
    {db : RuntimeDB} {pr : RuntimeProofState}
    (receipts : forest.receiptShape db pr) (revision : Nat)
    (admitted : admittedForestReceiptShape forest receipts revision) : Prop :=
  match forest with
  | .nil => True
  | .cons head tail =>
      allAssertionsStaleAtNext head receipts.1 revision admitted.1 ∧
        allForestAssertionsStaleAtNext tail receipts.2 revision admitted.2

end

mutual

theorem admittedTreeReceiptShape_all_stale_at_next
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    {db : RuntimeDB} {pr : RuntimeProofState}
    (receipts : tree.receiptShape db pr) (revision : Nat)
    (admitted : admittedTreeReceiptShape tree receipts revision) :
    allAssertionsStaleAtNext tree receipts revision admitted := by
  cases tree with
  | active => trivial
  | assertion member node children =>
      constructor
      · exact admittedForestReceiptShape_all_stale_at_next children receipts.1
          revision admitted.1
      · exact (changed_revision_deoptimizes_to_exact_live_step revision
          admitted.2.current).1

theorem admittedForestReceiptShape_all_stale_at_next
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas)
    {db : RuntimeDB} {pr : RuntimeProofState}
    (receipts : forest.receiptShape db pr) (revision : Nat)
    (admitted : admittedForestReceiptShape forest receipts revision) :
    allForestAssertionsStaleAtNext forest receipts revision admitted := by
  cases forest with
  | nil => trivial
  | cons head tail =>
      exact ⟨admittedTreeReceiptShape_all_stale_at_next head receipts.1
          revision admitted.1,
        admittedForestReceiptShape_all_stale_at_next tail receipts.2 revision
          admitted.2⟩

end


/-- A complete generated proof receipt together with current admission for
every assertion occurrence in its exact recursive shape. -/
structure CurrentGeneratedProvesExecutionReceipt
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    (db : RuntimeDB) (pr finalState : RuntimeProofState)
    (revision : Nat) : Type where
  operational : GeneratedProvesExecutionReceipt tree db pr finalState
  admissions : admittedTreeReceiptShape tree operational.occurrences revision

def admitGeneratedProofReceipt
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    {tree : GeneratedProvesTree projection target formula}
    {db : RuntimeDB} {pr finalState : RuntimeProofState}
    (revision : Nat)
    (operational : GeneratedProvesExecutionReceipt tree db pr finalState) :
    CurrentGeneratedProvesExecutionReceipt tree db pr finalState revision where
  operational := operational
  admissions := admitTreeReceipts tree operational.occurrences revision

/-- One revision change disables every assertion-native occurrence, while the
retained ordinary proof execution still reaches the identical complete final
state.  Deoptimization therefore occurs at the whole proof, not only at an
isolated assertion. -/
theorem changed_revision_deoptimizes_complete_generated_proof
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    {tree : GeneratedProvesTree projection target formula}
    {db : RuntimeDB} {pr finalState : RuntimeProofState}
    (revision : Nat)
    (current : CurrentGeneratedProvesExecutionReceipt tree db pr finalState
      revision) :
    allAssertionsStaleAtNext tree current.operational.occurrences revision
        current.admissions ∧
      tree.labels.foldlM (fun state label => db.stepNormal state label) pr =
        .ok finalState := by
  constructor
  · exact admittedTreeReceiptShape_all_stale_at_next tree
      current.operational.occurrences revision current.admissions
  · exact current.operational.execution

/-! ## Refusing malformed record tables -/

namespace Examples

open Mettapedia.Languages.Metamath.InferencePreparedAssertionCompilation.Examples

abbrev duplicateSource : SourceProgram String AssertionView :=
  source duplicateProjection ["dup"]

/-- A malformed table with two stored assertions at one label receives no
optimization witness, even though its ordinary first-occurrence source scan
remains defined. -/
theorem duplicate_assertion_label_refused :
    spec.recognize duplicateSource = none := by
  change SingleValuedDispatch.recognize duplicateSource = none
  simp [SingleValuedDispatch.recognize, duplicateSource, source,
    assertionRecordSource, duplicate_index_refused]
  rw [assertionIndexShape_recognized]

end Examples

#print axioms enters_common_nik_family
#print axioms admitted_records_observe_source
#print axioms projected_admission_and_fused_application
#print axioms implementation_compiles_prepared_records
#print axioms implementation_fallback_exact
#print axioms changed_revision_refuses_activation_and_preserves_fallback
#print axioms changed_revision_deoptimizes_to_exact_live_step
#print axioms changed_revision_deoptimizes_complete_generated_proof
#print axioms Examples.duplicate_assertion_label_refused

end Mettapedia.Languages.MeTTa.Prime.NativeTypedMetamathAssertionOptimization
