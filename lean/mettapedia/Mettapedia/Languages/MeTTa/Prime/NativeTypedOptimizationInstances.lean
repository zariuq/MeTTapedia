import Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationNIKBridge
import Mettapedia.Languages.Metamath.SourceGSLTOperations

/-!
# Native typed optimization instances across language families

The generic Prime/NIK optimization bridge is exercised here by three
structurally different licenses:

* source-derived Metamath operation-record fusion, licensed by unique keys;
* reusable scratch storage, licensed by call-local nonescape and value
  publication; and
* immutable memo reuse, licensed by exact physical-snapshot stability.

Each instance enters the same NIK admission family, keeps profitability
separate from semantic adequacy, and supplies a refusing negative.  A final
cross-family theorem shows that dispatch-tagged authority cannot align with a
storage candidate even when both mention the same source value.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationInstances

open Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core
open Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Seam
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationAdmission
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationNIKBridge
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationAdmission.Examples

/-! ## A generic computed-recognition entry lemma -/

/-- Any exact keyed candidate whose own recognizer returns a witness selects
the same witness in the native plan and the common NIK family. -/
theorem entersCommonFamily_of_isSome {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (authority : AlignedAuthority candidate)
    (recognized : (spec.recognize candidate.source).isSome = true) :
    ∃ shape : spec.ShapeEvidence candidate.source,
      prepareAtKey spec candidate (some authority) =
          .optimized authority shape ∧
        NativeTypedOptimizationAdmission.prepare spec candidate.source
            (some authority.authority) =
          ExecutionPlan.optimized authority.authority shape := by
  cases observed : spec.recognize candidate.source with
  | none =>
      simp [observed] at recognized
  | some shape =>
      exact ⟨shape,
        recognized_preparations_agree spec candidate authority shape observed⟩

/-! ## coGSLT/Metamath: source-derived operation-record fusion -/

namespace MetamathOperationRecordFusion

open Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation
open Mettapedia.Languages.Metamath.SourceGSLTOperations
open Mettapedia.Util.LinearHash

/-- The accepted indexed effects: construct one fresh record per source key,
then perform lookups without mutation. -/
def shape : TableShape :=
  ⟨32, [.insertFresh, .lookup]⟩

def plan : Plan :=
  ⟨32, [.insertFresh, .lookup]⟩

/-- Each value is the complete source-derived binding: source production,
semantic operation, and ordered fold contract.  The query therefore selects
one record rather than joining those fields independently. -/
def entries : List (String × Option NodeBinding) :=
  nodeSpecs.map fun node =>
    (node.productionLabel, compileNodeSpec? node)

/-- The real authored Metamath source-operation table, plus one absent-label
query which remains an ordinary `none` observation. -/
def source : SourceProgram String (Option NodeBinding) where
  shape := shape
  entries := entries
  queries := nodeSpecs.map (·.productionLabel) ++ ["statement_invented"]

abbrev spec :=
  SingleValuedDispatch.spec (Key := String) (Value := Option NodeBinding)

/-- The authored production labels and supported table effects pass the
executable exact-shape recognizer. -/
private theorem recognitionSucceeded :
    (SingleValuedDispatch.recognize source).isSome = true := by
  simp [SingleValuedDispatch.recognize, source, entries, shape, nodeSpecs,
    Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.recognize,
    effectSupported, allDistinct_eq_eraseDupsLength]
  simp only [List.eraseDups_cons, List.filter]
  decide

/-- Exact source-label uniqueness licenses the record index.  The witness is
the recognizer's own proof-bearing result, not a parallel certificate. -/
def evidence : SingleValuedDispatch.Evidence source :=
  (SingleValuedDispatch.recognize source).get recognitionSucceeded

theorem recognized : spec.recognize source = some evidence := by
  change SingleValuedDispatch.recognize source = some evidence
  exact (Option.some_get recognitionSucceeded).symm

/-- The exact Prime authority key binds the Metamath dialect, this source
occurrence, and its logical revision. -/
def nativeKey : OptimizationKey
    (SourceProgram String (Option NodeBinding)) :=
  { occurrence := (.singleValuedDispatch, source)
    revision := 1
    dialect := "metamath-source-gslt"
    expected := .prim .sym
    authority := "prime-native-source-operation-records" }

def nativeAuthority : ExactAuthority spec source where
  key := nativeKey
  occurrence_eq := rfl
  judgment := SingleValuedDispatch.nativeJudgment source nativeKey
    (by simp [nativeKey, exactTy])

def candidate : KeyedCandidate spec :=
  KeyedCandidate.ofAuthority spec nativeAuthority

def authority : AlignedAuthority candidate :=
  AlignedAuthority.ofAuthority spec nativeAuthority

/-- The concrete Metamath authority carries deterministic dispatch evidence
bound to this exact key, rather than a free-standing generic license. -/
theorem native_authority_coordinates :
    nativeAuthority.judgment.license.actual = nativeKey.expected ∧
      nativeAuthority.judgment.license.expected = nativeKey.expected ∧
      nativeAuthority.judgment.license.card = .det ∧
      nativeAuthority.judgment.license.demand = .grade .det :=
  SingleValuedDispatch.nativeJudgment_coordinates nativeAuthority.judgment

/-- Metamath record fusion is an ordinary common NIK optimization, with the
same source-derived uniqueness witness on both preparation paths. -/
theorem enters_common_nik_family :
    prepareAtKey spec candidate (some authority) =
        .optimized authority evidence ∧
      NativeTypedOptimizationAdmission.prepare spec source
          (some nativeAuthority) =
        ExecutionPlan.optimized nativeAuthority evidence :=
  recognized_preparations_agree spec candidate authority evidence recognized

/-- The fused artifact returns exactly the same ordered optional record bag as
the source scans, including the absent-label result. -/
theorem fused_records_observe_source :
    spec.observeArtifact source (spec.compile source evidence) =
      spec.observeSource source :=
  spec.adequate source evidence

/-- Cost evidence is attached only after semantic admission. -/
def profitability : ProfitabilityReceipt spec source nativeAuthority evidence
    where
  key := nativeAuthority.key
  same_key := rfl
  baseline := spec.sourceWorkSpan source
  optimized := spec.artifactWorkSpan source (spec.compile source evidence)
  baseline_eq := rfl
  optimized_eq := rfl
  improves :=
    SingleValuedDispatch.artifactWorkSpan_le_sourceWorkSpan source evidence

def pathProfitability :=
  NativeTypedOptimizationNIKBridge.profitabilityReceipt spec candidate
    authority evidence profitability

private def constantSpec : NodeSpec :=
  { productionLabel := "statement_const"
    operation := .declareConstants }

private def variableSpec : NodeSpec :=
  { productionLabel := "statement_var"
    operation := .declareVariables }

private def duplicateSource : SourceProgram String (Option NodeBinding) where
  shape := shape
  entries :=
    [("statement_const", compileNodeSpec? constantSpec),
     ("statement_const", compileNodeSpec? variableSpec)]
  queries := ["statement_const"]

/-- A duplicated source label is refused rather than assigned an arbitrary
record.  Ordinary source lookup remains available outside admission. -/
theorem duplicate_label_refused :
    spec.recognize duplicateSource = none := by
  change SingleValuedDispatch.recognize duplicateSource = none
  simp [SingleValuedDispatch.recognize, duplicateSource, constantSpec,
    variableSpec, shape,
    Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.recognize,
    effectSupported, allDistinct_eq_eraseDupsLength]
  simp only [List.eraseDups_cons, List.filter]
  decide

end MetamathOperationRecordFusion

/-! ## Nonescaping reusable storage -/

namespace StorageReuse

open Mettapedia.GSLT.LanguageDef.ReusableSlotBufferCompilation

abbrev spec :=
  NonEscapingStorage.spec (width := 1) (Value := Nat) (Observation := Nat)

abbrev source := Storage.source

def evidence : NonEscapingStorage.Evidence source where
  artifact := compileObservable source.program
  accepted := rfl

def nativeKey : OptimizationKey
    (NonEscapingStorage.Source (width := 1) (Value := Nat)
      (Observation := Nat)) :=
  { occurrence := (.reusableStorage, source)
    revision := 2
    dialect := "prime"
    expected := .prim .num
    authority := "prime-native-call-local-storage" }

def nativeAuthority : ExactAuthority spec source where
  key := nativeKey
  occurrence_eq := rfl
  judgment := NonEscapingStorage.nativeJudgment source nativeKey
    (by simp [nativeKey, exactTy])

def candidate : KeyedCandidate spec :=
  KeyedCandidate.ofAuthority spec nativeAuthority

def authority : AlignedAuthority candidate :=
  AlignedAuthority.ofAuthority spec nativeAuthority

/-- The accepted storage authority records the actual call-local/value
classification before the recognizer licenses reuse. -/
theorem native_authority_records_call_local_value :
    nativeAuthority.judgment.plan =
      NonEscapingStorage.PlanJudgment.callLocalValue := by
  rfl

theorem recognized : spec.recognize source = some evidence := by
  rfl

/-- Lifetime and value-publication evidence enter the same common NIK family
as keyed dispatch; no storage-specific admission hierarchy is introduced. -/
theorem enters_common_nik_family :
    prepareAtKey spec candidate (some authority) =
        .optimized authority evidence ∧
      NativeTypedOptimizationAdmission.prepare spec source
          (some nativeAuthority) =
        ExecutionPlan.optimized nativeAuthority evidence :=
  recognized_preparations_agree spec candidate authority evidence recognized

def profitability : ProfitabilityReceipt spec source nativeAuthority evidence
    where
  key := nativeAuthority.key
  same_key := rfl
  baseline := spec.sourceWorkSpan source
  optimized := spec.artifactWorkSpan source (spec.compile source evidence)
  baseline_eq := rfl
  optimized_eq := rfl
  improves :=
    NonEscapingStorage.artifactWorkSpan_le_sourceWorkSpan source evidence

def pathProfitability :=
  NativeTypedOptimizationNIKBridge.profitabilityReceipt spec candidate
    authority evidence profitability

abbrev retainedSource := Storage.retainedSource

def retainedNativeKey : OptimizationKey
    (NonEscapingStorage.Source (width := 1) (Value := Nat)
      (Observation := Nat)) :=
  { occurrence := (.reusableStorage, retainedSource)
    revision := 2
    dialect := "prime"
    expected := .prim .num
    authority := "prime-native-call-local-storage" }

def retainedNativeAuthority : ExactAuthority spec retainedSource
    where
  key := retainedNativeKey
  occurrence_eq := rfl
  judgment :=
    NonEscapingStorage.nativeJudgment retainedSource retainedNativeKey
      (by simp [retainedNativeKey, exactTy])

def retainedCandidate : KeyedCandidate spec :=
  KeyedCandidate.ofAuthority spec retainedNativeAuthority

def retainedAuthority : AlignedAuthority retainedCandidate :=
  AlignedAuthority.ofAuthority spec retainedNativeAuthority

/-- Exact typing does not disguise the refusing plan: the authority retains
the source's retained/reference classification. -/
theorem retained_authority_records_retained_reference :
    retainedNativeAuthority.judgment.plan =
      NonEscapingStorage.PlanJudgment.retainedReference := by
  rfl

/-- Retained scratch published by reference fails open on both preparation
paths; exact typing authority cannot repair missing lifetime evidence. -/
theorem retained_reference_falls_back :
    prepareAtKey spec retainedCandidate (some retainedAuthority) = .raw ∧
      NativeTypedOptimizationAdmission.prepare spec retainedSource
          (some retainedNativeAuthority) = .source :=
  unrecognized_preparations_agree spec retainedCandidate retainedAuthority
    Storage.retained_reference_rejected

/-- Even a hypothetical dispatch authority mentioning this exact storage
source cannot share the candidate's key. -/
theorem dispatch_authority_cannot_align
    (dispatchSpec : OptimizationSpec
      (NonEscapingStorage.Source (width := 1) (Value := Nat)
        (Observation := Nat)))
    (dispatchKind : dispatchSpec.kind = .singleValuedDispatch)
    (dispatch : ExactAuthority dispatchSpec source) :
    dispatch.key ≠ candidate.key :=
  foreign_authority_key_ne_of_kind_ne candidate dispatch (by
    rw [dispatchKind]
    decide)

end StorageReuse

/-! ## Revision-stable memo reuse -/

namespace StableMemo

abbrev spec :=
  RevisionStableMemo.spec (Row := Nat) (Key := Nat) (Value := Nat)

abbrev source := Memo.stableSource

def evidence : RevisionStableMemo.Evidence source where
  snapshot_eq := rfl

def nativeKey : OptimizationKey
    (RevisionStableMemo.Source (Row := Nat) (Key := Nat) (Value := Nat)) :=
  { occurrence := (.revisionStableMemo, source)
    revision := 12
    dialect := "prime"
    expected := .prim .num
    authority := "prime-native-stable-memo" }

def nativeAuthority : ExactAuthority spec source where
  key := nativeKey
  occurrence_eq := rfl
  judgment := RevisionStableMemo.nativeJudgment source nativeKey
    (by simp [nativeKey, exactTy])

def candidate : KeyedCandidate spec :=
  KeyedCandidate.ofAuthority spec nativeAuthority

def authority : AlignedAuthority candidate :=
  AlignedAuthority.ofAuthority spec nativeAuthority

/-- The stable authority retains equal physical snapshots; the recognizer
will separately turn that equality into memo-reuse shape evidence. -/
theorem native_authority_records_same_snapshot :
    nativeAuthority.judgment.beforeSnapshot =
      nativeAuthority.judgment.afterSnapshot := by
  rfl

theorem recognized : spec.recognize source = some evidence := by
  rfl

/-- Snapshot equality licenses reuse through the same common NIK family. -/
theorem enters_common_nik_family :
    prepareAtKey spec candidate (some authority) =
        .optimized authority evidence ∧
      NativeTypedOptimizationAdmission.prepare spec source
          (some nativeAuthority) =
        ExecutionPlan.optimized nativeAuthority evidence :=
  recognized_preparations_agree spec candidate authority evidence recognized

/-- This instance is a must-not-hurt control: its abstract WorkSpan is equal,
not claimed strictly faster. -/
def profitability : ProfitabilityReceipt spec source nativeAuthority evidence
    where
  key := nativeAuthority.key
  same_key := rfl
  baseline := spec.sourceWorkSpan source
  optimized := spec.artifactWorkSpan source (spec.compile source evidence)
  baseline_eq := rfl
  optimized_eq := rfl
  improves := by rfl

def pathProfitability :=
  NativeTypedOptimizationNIKBridge.profitabilityReceipt spec candidate
    authority evidence profitability

abbrev changedSource := Memo.changedSource

def changedNativeKey : OptimizationKey
    (RevisionStableMemo.Source (Row := Nat) (Key := Nat) (Value := Nat)) :=
  { occurrence := (.revisionStableMemo, changedSource)
    revision := 13
    dialect := "prime"
    expected := .prim .num
    authority := "prime-native-stable-memo" }

def changedNativeAuthority : ExactAuthority spec changedSource
    where
  key := changedNativeKey
  occurrence_eq := rfl
  judgment :=
    RevisionStableMemo.nativeJudgment changedSource changedNativeKey
      (by simp [changedNativeKey, exactTy])

def changedCandidate : KeyedCandidate spec :=
  KeyedCandidate.ofAuthority spec changedNativeAuthority

def changedAuthority : AlignedAuthority changedCandidate :=
  AlignedAuthority.ofAuthority spec changedNativeAuthority

/-- The changed authority preserves the physical difference instead of
laundering append-only history into reuse authority. -/
theorem changed_authority_records_different_snapshots :
    changedNativeAuthority.judgment.beforeSnapshot ≠
      changedNativeAuthority.judgment.afterSnapshot := by
  decide

/-- Append-only storage is insufficient when the physical snapshot differs.
Both paths decline reuse and preserve ordinary lookup semantics. -/
theorem changed_snapshot_falls_back :
    prepareAtKey spec changedCandidate (some changedAuthority) = .raw ∧
      NativeTypedOptimizationAdmission.prepare spec changedSource
          (some changedNativeAuthority) = .source :=
  unrecognized_preparations_agree spec changedCandidate changedAuthority
    Memo.changed_revision_rejected

end StableMemo

#print axioms entersCommonFamily_of_isSome
#print axioms MetamathOperationRecordFusion.enters_common_nik_family
#print axioms MetamathOperationRecordFusion.native_authority_coordinates
#print axioms MetamathOperationRecordFusion.fused_records_observe_source
#print axioms MetamathOperationRecordFusion.pathProfitability
#print axioms MetamathOperationRecordFusion.duplicate_label_refused
#print axioms StorageReuse.enters_common_nik_family
#print axioms StorageReuse.pathProfitability
#print axioms StorageReuse.retained_reference_falls_back
#print axioms StorageReuse.native_authority_records_call_local_value
#print axioms StorageReuse.retained_authority_records_retained_reference
#print axioms StorageReuse.dispatch_authority_cannot_align
#print axioms StableMemo.enters_common_nik_family
#print axioms StableMemo.pathProfitability
#print axioms StableMemo.changed_snapshot_falls_back
#print axioms StableMemo.native_authority_records_same_snapshot
#print axioms StableMemo.changed_authority_records_different_snapshots

end Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationInstances
