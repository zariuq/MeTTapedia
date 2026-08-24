import Mettapedia.Languages.MeTTa.Prime.NativeInteractionSeam
import Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation
import Mettapedia.GSLT.LanguageDef.ReusableSlotBufferCompilation
import Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCompilation

/-!
# Revision-bound typed optimization admission

Three ingredients have distinct jobs:

* each hosted calculus supplies a source/key-indexed native judgment;
* a local recognizer supplies evidence for one optimization class;
* an optional `ProfitabilityReceipt` compares work/span observations.

Deterministic dispatch uses an `OptLicense`; storage and memoization use their
own lifetime/publication and physical-revision judgments.  Native judgment and
shape evidence are both required for semantic admission.  Profitability is a
separate policy decision and cannot repair an inadequate transformation.  When
either authority or shape recognition is absent, preparation keeps the source
plan.  Both branches have the same named semantic observation.

The first instances reuse existing certified transformations: single-valued
keyed dispatch, non-escaping scratch reuse, and revision-stable memoization.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationAdmission

open Mettapedia.Algebra
open Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core
open Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Seam
open Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan

universe uSource uJudgment uEvidence uArtifact uObservation

/-- Closed inventory of the first optimization classes. -/
inductive OptimizationKind where
  | singleValuedDispatch
  | reusableStorage
  | revisionStableMemo
  deriving DecidableEq, Repr

/-- The full cache/admission identity.  The occurrence binds both the
optimization family and exact source; revision, dialect, expected type, and
authority are all retained.  A cache entry for one transformation class
therefore cannot be reused as authority for another class. -/
abbrev OptimizationKey (Source : Type uSource) :=
  CheckKey (OptimizationKind × Source) Nat String Ty String

/-- One semantics-preserving optimization family.  Shape evidence and
artifacts may depend on the exact source occurrence.  Crucially, the hosted
calculus supplies its own proof-relevant native judgment at the complete key;
the generic adapter does not pretend that PeTTa cardinality evidence is the
right authority for storage, memoization, or another guest calculus. -/
structure OptimizationSpec (Source : Type uSource) where
  kind : OptimizationKind
  NativeJudgment : (source : Source) → OptimizationKey Source → Type uJudgment
  nativeJudgment_expected_exact : ∀ source key,
    NativeJudgment source key → exactTy key.expected = true
  ShapeEvidence : Source → Type uEvidence
  Artifact : Source → Type uArtifact
  Observation : Source → Type uObservation
  recognize : ∀ source, Option (ShapeEvidence source)
  compile : ∀ source, ShapeEvidence source → Artifact source
  observeSource : ∀ source, Observation source
  observeArtifact : ∀ source, Artifact source → Observation source
  adequate : ∀ source evidence,
    observeArtifact source (compile source evidence) = observeSource source
  sourceWorkSpan : Source → WorkSpan
  artifactWorkSpan : ∀ source, Artifact source → WorkSpan

/-- Native judgment authority for one optimization specification and source
occurrence at one complete key.  The judgment is selected by the hosted
calculus and is indexed by both source and key, so an unrelated exact license
cannot be attached merely because it happens to be constructible. -/
structure ExactAuthority {Source : Type uSource}
    (spec : OptimizationSpec Source) (source : Source) where
  key : OptimizationKey Source
  occurrence_eq : key.occurrence = (spec.kind, source)
  judgment : spec.NativeJudgment source key

namespace ExactAuthority

/-- The optimization family is part of cache identity, not an external label
that may disagree with the proof object. -/
theorem key_kind {Source : Type uSource} {spec : OptimizationSpec Source}
    {source : Source} (authority : ExactAuthority spec source) :
    authority.key.occurrence.1 = spec.kind := by
  exact congrArg Prod.fst authority.occurrence_eq

/-- The exact source occurrence is the second cache-identity coordinate. -/
theorem key_source {Source : Type uSource} {spec : OptimizationSpec Source}
    {source : Source} (authority : ExactAuthority spec source) :
    authority.key.occurrence.2 = source := by
  exact congrArg Prod.snd authority.occurrence_eq

/-- Authorities for different optimization families cannot share an exact
cache key, even if their source types and values coincide. -/
theorem key_ne_of_kind_ne {Source : Type uSource}
    {leftSpec rightSpec : OptimizationSpec Source}
    {leftSource rightSource : Source}
    (left : ExactAuthority leftSpec leftSource)
    (right : ExactAuthority rightSpec rightSource)
    (different : leftSpec.kind ≠ rightSpec.kind) : left.key ≠ right.key := by
  intro sameKey
  apply different
  rw [← left.key_kind, ← right.key_kind, sameKey]

/-- Every admitted native judgment establishes exactness of the expected type
stored in its complete key. -/
theorem expected_exact {Source : Type uSource} {spec : OptimizationSpec Source}
    {source : Source} (authority : ExactAuthority spec source) :
    exactTy authority.key.expected = true :=
  spec.nativeJudgment_expected_exact source authority.key authority.judgment

/-- Gradual unknown can never hide in the expected type of native judgment
authority. -/
theorem expected_ne_unknown {Source : Type uSource}
    {spec : OptimizationSpec Source} {source : Source}
    (authority : ExactAuthority spec source) :
    authority.key.expected ≠ .unknown := by
  intro equal
  have exact := authority.expected_exact
  rw [equal] at exact
  simp [exactTy] at exact

end ExactAuthority

/-- Source execution is a first-class plan.  An optimized plan contains both
exact type authority and evidence produced by this specification's own
recognizer. -/
inductive ExecutionPlan {Source : Type uSource}
    (spec : OptimizationSpec Source) (source : Source) where
  | source
  | optimized (authority : ExactAuthority spec source)
      (shape : spec.ShapeEvidence source)

namespace ExecutionPlan

variable {Source : Type uSource} {spec : OptimizationSpec Source}
variable {source : Source}

/-- Execute the selected representation through the shared semantic
observation. -/
def observe (plan : ExecutionPlan spec source) : spec.Observation source :=
  match plan with
  | .source => spec.observeSource source
  | .optimized _ shape =>
      spec.observeArtifact source (spec.compile source shape)

/-- Admission can change representation, never the named observation. -/
theorem observe_eq_source (plan : ExecutionPlan spec source) :
    plan.observe = spec.observeSource source := by
  cases plan with
  | source => rfl
  | optimized _ shape => exact spec.adequate source shape

/-- Work/span is deliberately not part of semantic adequacy. -/
def workSpan (plan : ExecutionPlan spec source) : WorkSpan :=
  match plan with
  | .source => spec.sourceWorkSpan source
  | .optimized _ shape =>
      spec.artifactWorkSpan source (spec.compile source shape)

@[simp] theorem source_workSpan :
    (ExecutionPlan.source (spec := spec) (source := source)).workSpan =
      spec.sourceWorkSpan source := rfl

end ExecutionPlan

/-- Preparation is fail-open.  Missing exact authority or failed recognition
selects the source plan; neither result rejects the source computation. -/
def prepare {Source : Type uSource} (spec : OptimizationSpec Source)
    (source : Source) (authority : Option (ExactAuthority spec source)) :
    ExecutionPlan spec source :=
  match authority with
  | none => .source
  | some exact =>
      match spec.recognize source with
      | none => .source
      | some shape => .optimized exact shape

@[simp] theorem prepare_without_authority {Source : Type uSource}
    (spec : OptimizationSpec Source) (source : Source) :
    prepare spec source none = .source := rfl

theorem prepare_of_unrecognized {Source : Type uSource}
    (spec : OptimizationSpec Source) (source : Source)
    (authority : ExactAuthority spec source)
    (unrecognized : spec.recognize source = none) :
    prepare spec source (some authority) = .source := by
  simp [prepare, unrecognized]

/-- Raw observation survives every preparation outcome, including unknown
authority and shape rejection. -/
theorem observe_prepare {Source : Type uSource}
    (spec : OptimizationSpec Source) (source : Source)
    (authority : Option (ExactAuthority spec source)) :
    (prepare spec source authority).observe = spec.observeSource source :=
  (prepare spec source authority).observe_eq_source

/-- Profitability is a separately supplied, revision-bound receipt.  It is
not a field of `OptimizationSpec` and is never used to prove adequacy. -/
structure ProfitabilityReceipt {Source : Type uSource}
    (spec : OptimizationSpec Source) (source : Source)
    (authority : ExactAuthority spec source)
    (shape : spec.ShapeEvidence source) where
  key : OptimizationKey Source
  same_key : key = authority.key
  baseline : WorkSpan
  optimized : WorkSpan
  baseline_eq : baseline = spec.sourceWorkSpan source
  optimized_eq :
    optimized = spec.artifactWorkSpan source (spec.compile source shape)
  improves : optimized ≤ baseline

/-- A profitable plan adds a cost-policy receipt to an already adequate plan;
it cannot manufacture shape or type authority. -/
structure ProfitablePlan {Source : Type uSource}
    (spec : OptimizationSpec Source) (source : Source) where
  authority : ExactAuthority spec source
  shape : spec.ShapeEvidence source
  receipt : ProfitabilityReceipt spec source authority shape

def ProfitablePlan.toExecutionPlan {Source : Type uSource}
    {spec : OptimizationSpec Source} {source : Source}
    (plan : ProfitablePlan spec source) : ExecutionPlan spec source :=
  .optimized plan.authority plan.shape

theorem ProfitablePlan.workSpan_le_source {Source : Type uSource}
    {spec : OptimizationSpec Source} {source : Source}
    (plan : ProfitablePlan spec source) :
    plan.toExecutionPlan.workSpan ≤ spec.sourceWorkSpan source := by
  change spec.artifactWorkSpan source (spec.compile source plan.shape) ≤
    spec.sourceWorkSpan source
  rw [← plan.receipt.baseline_eq, ← plan.receipt.optimized_eq]
  exact plan.receipt.improves

/-! ## Instance 1: single-valued keyed dispatch -/

namespace SingleValuedDispatch

open Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation

variable {Key Value : Type} [BEq Key] [Hashable Key]
  [LawfulBEq Key] [LawfulHashable Key]

/-- The native typing face for deterministic dispatch.  Unlike the earlier
adapter, the `OptLicense` is indexed by this dispatch source and complete key,
and all of its type/cardinality coordinates are bound to that key. -/
structure NativeJudgment (source : SourceProgram Key Value)
    (key : OptimizationKey (SourceProgram Key Value)) where
  license : OptLicense
  actual_eq : license.actual = key.expected
  expected_eq : license.expected = key.expected
  card_eq : license.card = .det
  demand_eq : license.demand = .grade .det

/-- Construct the deterministic native judgment at any exact declared type.
The separately computed `Evidence` below still establishes that this concrete
table has the unique-key shape required by the implementation. -/
def nativeJudgment (source : SourceProgram Key Value)
    (key : OptimizationKey (SourceProgram Key Value))
    (expectedExact : exactTy key.expected = true) :
    NativeJudgment source key where
  license :=
    { actual := key.expected
      expected := key.expected
      card := .det
      demand := .grade .det
      actual_exact := expectedExact
      expected_exact := expectedExact
      flows := consistent?_refl key.expected
      fits := modeFits_refl (.grade .det) }
  actual_eq := rfl
  expected_eq := rfl
  card_eq := rfl
  demand_eq := rfl

omit [BEq Key] [Hashable Key] [LawfulBEq Key] [LawfulHashable Key] in
theorem nativeJudgment_expected_exact
    {source : SourceProgram Key Value}
    {key : OptimizationKey (SourceProgram Key Value)}
    (judgment : NativeJudgment source key) :
    exactTy key.expected = true := by
  rw [← judgment.expected_eq]
  exact judgment.license.expected_exact

omit [BEq Key] [Hashable Key] [LawfulBEq Key] [LawfulHashable Key] in
/-- The dispatch license cannot float free of the candidate key: both type
coordinates and both cardinality coordinates are fixed by the indexed native
judgment. -/
theorem nativeJudgment_coordinates
    {source : SourceProgram Key Value}
    {key : OptimizationKey (SourceProgram Key Value)}
    (judgment : NativeJudgment source key) :
    judgment.license.actual = key.expected ∧
      judgment.license.expected = key.expected ∧
      judgment.license.card = .det ∧
      judgment.license.demand = .grade .det :=
  ⟨judgment.actual_eq, judgment.expected_eq, judgment.card_eq,
    judgment.demand_eq⟩

/-- Evidence is the existing unique-key admission, indexed back to the exact
source occurrence. -/
structure Evidence (source : SourceProgram Key Value) where
  plan : Plan
  shapeAccepted :
    Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.recognize
      source.shape = some plan
  keysDistinct :
    Mettapedia.Util.LinearHash.allDistinct
      (source.entries.map fun entry => entry.1) = true

def recognize (source : SourceProgram Key Value) : Option (Evidence source) :=
  match shapeAccepted :
      Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.recognize
        source.shape with
  | none => none
  | some plan =>
      if keysDistinct : Mettapedia.Util.LinearHash.allDistinct
          (source.entries.map fun entry => entry.1) = true then
        some ⟨plan, shapeAccepted, keysDistinct⟩
      else none

def spec : OptimizationSpec (SourceProgram Key Value) where
  kind := .singleValuedDispatch
  NativeJudgment := NativeJudgment
  nativeJudgment_expected_exact := fun _ _ judgment =>
    nativeJudgment_expected_exact judgment
  ShapeEvidence := Evidence
  Artifact := fun _ => Artifact Key Value
  Observation := fun _ => List (Option Value)
  recognize := recognize
  compile := fun source evidence =>
    compile evidence.plan source
  observeSource := runSource
  observeArtifact := fun _ => runArtifact
  adequate := by
    intro source evidence
    exact runArtifact_compile evidence.plan source
  sourceWorkSpan := fun source =>
    let cost := sourceRunCost source
    ⟨cost, cost⟩
  artifactWorkSpan := fun source _ =>
    let cost := indexedRunOperationCost source
    ⟨cost, cost⟩

/-- Every admitted dispatch artifact has no greater abstract dictionary work
or span than the source scan. -/
theorem artifactWorkSpan_le_sourceWorkSpan
    (source : SourceProgram Key Value) (evidence : Evidence source) :
    (spec (Key := Key) (Value := Value)).artifactWorkSpan source
        ((spec (Key := Key) (Value := Value)).compile source evidence) ≤
      (spec (Key := Key) (Value := Value)).sourceWorkSpan source := by
  constructor <;> exact indexedRunOperationCost_le_sourceRunCost source

end SingleValuedDispatch

/-! ## Instance 2: non-escaping reusable storage -/

namespace NonEscapingStorage

open Mettapedia.GSLT.LanguageDef.ReusableSlotBufferCompilation

variable {width : Nat} {Value Observation : Type}
  [DecidableEq (Fin width)]

structure Source where
  plan : ReusePlan
  program : ObservableProgram width Value Observation

/-- Proof-relevant classification of every lifetime/publication plan.  This
is the native storage-effect judgment; only the call-local/value case is later
recognized as reusable. -/
inductive PlanJudgment : ReusePlan → Type
  | callLocalValue : PlanJudgment ⟨.callLocal, .value⟩
  | callLocalReference : PlanJudgment ⟨.callLocal, .reference⟩
  | retainedValue : PlanJudgment ⟨.retained, .value⟩
  | retainedReference : PlanJudgment ⟨.retained, .reference⟩

def classifyPlan (plan : ReusePlan) : PlanJudgment plan := by
  rcases plan with ⟨lifetime, boundary⟩
  cases lifetime <;> cases boundary
  · exact .callLocalValue
  · exact .callLocalReference
  · exact .retainedValue
  · exact .retainedReference

/-- An exact storage judgment retains both its exact result type and the
actual lifetime/publication classification of this source. -/
structure NativeJudgment
    (source : Source (width := width) (Value := Value)
      (Observation := Observation))
    (key : OptimizationKey
      (Source (width := width) (Value := Value)
        (Observation := Observation))) where
  expected_exact : exactTy key.expected = true
  plan : PlanJudgment source.plan

def nativeJudgment
    (source : Source (width := width) (Value := Value)
      (Observation := Observation))
    (key : OptimizationKey
      (Source (width := width) (Value := Value)
        (Observation := Observation)))
    (expectedExact : exactTy key.expected = true) :
    NativeJudgment source key where
  expected_exact := expectedExact
  plan := classifyPlan source.plan

structure Evidence (source : Source (width := width)
    (Value := Value) (Observation := Observation)) where
  artifact : ReusableObservableProgram width Value Observation
  accepted : compileObservable? source.plan source.program = some artifact

def recognize (source : Source (width := width)
    (Value := Value) (Observation := Observation)) :
    Option (Evidence source) :=
  match accepted : compileObservable? source.plan source.program with
  | none => none
  | some artifact => some ⟨artifact, accepted⟩

def spec : OptimizationSpec
    (Source (width := width) (Value := Value) (Observation := Observation)) where
  kind := .reusableStorage
  NativeJudgment := NativeJudgment
  nativeJudgment_expected_exact := fun _ _ judgment => judgment.expected_exact
  ShapeEvidence := Evidence
  Artifact := fun _ => ReusableObservableProgram width Value Observation
  Observation := fun _ => List Observation
  recognize := recognize
  compile := fun _ evidence => evidence.artifact
  observeSource := fun source => observeFreshCalls source.program
  observeArtifact := fun _ artifact => observeReusableCalls artifact
  adequate := by
    intro source evidence
    exact compileObservable?_exact source.plan source.program evidence.artifact
      evidence.accepted
  sourceWorkSpan := fun source =>
    let cost := freshAllocationCount source.program.transactions
    ⟨cost, cost⟩
  artifactWorkSpan := fun _ artifact =>
    let cost := reusableAllocationCount artifact.transactions
    ⟨cost, cost⟩

/-- The admitted reset-and-reuse artifact never increases the abstract
allocation work/span readout. -/
theorem artifactWorkSpan_le_sourceWorkSpan
    (source : Source (width := width) (Value := Value)
      (Observation := Observation))
    (evidence : Evidence source) :
    (spec (width := width) (Value := Value)
        (Observation := Observation)).artifactWorkSpan source
          evidence.artifact ≤
      (spec (width := width) (Value := Value)
        (Observation := Observation)).sourceWorkSpan source := by
  have allocationLe := compileObservable?_allocationCount_le source.plan
    source.program evidence.artifact evidence.accepted
  exact ⟨allocationLe, allocationLe⟩

end NonEscapingStorage

/-! ## Instance 3: revision-stable memoization -/

namespace RevisionStableMemo

open Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCompilation
open Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCompilation.PhysicalSnapshot

variable {Row Key Value : Type} [DecidableEq Key]

/-- A candidate cache reuse across two physical revisions.  Append-only is a
store contract; exact snapshot equality is still recognized separately. -/
structure Source where
  resolve : List Bool → List (List Row) → Key → Option Value
  before : Store Row
  after : Store Row
  appendOnly : AppendOnly before after
  keys : List Key

/-- The native physical-revision judgment retains the exact snapshots and
the append-only derivation.  Snapshot equality remains a separately checked
optimization shape, so append-only history alone cannot license reuse. -/
structure NativeJudgment
    (source : Source (Row := Row) (Key := Key) (Value := Value))
    (key : OptimizationKey
      (Source (Row := Row) (Key := Key) (Value := Value))) where
  expected_exact : exactTy key.expected = true
  beforeSnapshot : Snapshot
  afterSnapshot : Snapshot
  before_eq : beforeSnapshot = capture source.before
  after_eq : afterSnapshot = capture source.after
  appendOnly : AppendOnly source.before source.after

def nativeJudgment
    (source : Source (Row := Row) (Key := Key) (Value := Value))
    (key : OptimizationKey
      (Source (Row := Row) (Key := Key) (Value := Value)))
    (expectedExact : exactTy key.expected = true) :
    NativeJudgment source key where
  expected_exact := expectedExact
  beforeSnapshot := capture source.before
  afterSnapshot := capture source.after
  before_eq := rfl
  after_eq := rfl
  appendOnly := source.appendOnly

structure Evidence (source : Source (Row := Row) (Key := Key)
    (Value := Value)) : Type where
  snapshot_eq : capture source.before = capture source.after

def recognize (source : Source (Row := Row) (Key := Key)
    (Value := Value)) : Option (Evidence source) :=
  if stable : capture source.before = capture source.after then
    some ⟨stable⟩
  else none

def spec : OptimizationSpec
    (Source (Row := Row) (Key := Key) (Value := Value)) where
  kind := .revisionStableMemo
  NativeJudgment := NativeJudgment
  nativeJudgment_expected_exact := fun _ _ judgment => judgment.expected_exact
  ShapeEvidence := Evidence
  Artifact := fun _ => Environment Key Value
  Observation := fun _ => Option (List Value)
  recognize := recognize
  compile := fun source _ => environmentOf source.resolve source.before
  observeSource := fun source =>
    executeFresh (environmentOf source.resolve source.after) source.keys
  observeArtifact := fun source cached => executeFresh cached source.keys
  adequate := by
    intro source evidence
    exact executeFresh_eq_of_sameLookup
      (sameLookup_of_appendOnly_snapshot source.resolve source.appendOnly
        evidence.snapshot_eq) source.keys
  sourceWorkSpan := fun source => ⟨source.keys.length, source.keys.length⟩
  artifactWorkSpan := fun source _ => ⟨source.keys.length, source.keys.length⟩

end RevisionStableMemo

/-! ## Cross-instance barrier -/

/-- Runtime envelopes may be tagged before their dependent evidence is
decoded.  A mismatched class is rejected before any instance recognizer runs. -/
def classGate (expected actual : OptimizationKind) : Bool :=
  expected == actual

/-- Decode a runtime optimization envelope only under the specification's
own class tag.  A mismatched envelope falls back to the source plan before
its dependent evidence can be considered. -/
def prepareTagged {Source : Type uSource} (spec : OptimizationSpec Source)
    (actualKind : OptimizationKind) (source : Source)
    (authority : Option (ExactAuthority spec source)) :
    ExecutionPlan spec source :=
  if classGate spec.kind actualKind then
    prepare spec source authority
  else
    .source

theorem prepareTagged_of_class_mismatch {Source : Type uSource}
    (spec : OptimizationSpec Source) (actualKind : OptimizationKind)
    (source : Source)
    (authority : Option (ExactAuthority spec source))
    (mismatch : classGate spec.kind actualKind = false) :
    prepareTagged spec actualKind source authority = .source := by
  simp [prepareTagged, mismatch]

theorem storage_rejects_dispatch_class :
    classGate .reusableStorage .singleValuedDispatch = false := rfl

theorem memo_rejects_storage_class :
    classGate .revisionStableMemo .reusableStorage = false := rfl

/-- Cross-instance negative: a dispatch-tagged envelope cannot activate the
storage transformation, even when exact authority for the storage source is
available. -/
theorem dispatch_envelope_cannot_activate_storage {width : Nat}
    {Value Observation : Type} [DecidableEq (Fin width)]
    (source : NonEscapingStorage.Source (width := width)
      (Value := Value) (Observation := Observation))
    (authority : ExactAuthority
      (NonEscapingStorage.spec (width := width) (Value := Value)
        (Observation := Observation)) source) :
    prepareTagged
        (NonEscapingStorage.spec (width := width) (Value := Value)
          (Observation := Observation))
        .singleValuedDispatch source (some authority) = .source := by
  apply prepareTagged_of_class_mismatch
  rfl

/-- The stronger typed barrier: dispatch and storage authorities for the same
source carrier cannot share a cache key because the family is inside the
occurrence identity. -/
theorem dispatch_storage_authority_keys_differ {Source : Type}
    {dispatchSpec storageSpec : OptimizationSpec Source}
    {dispatchSource storageSource : Source}
    (dispatch : ExactAuthority dispatchSpec dispatchSource)
    (storage : ExactAuthority storageSpec storageSource)
    (dispatchKind : dispatchSpec.kind = .singleValuedDispatch)
    (storageKind : storageSpec.kind = .reusableStorage) :
    dispatch.key ≠ storage.key := by
  apply ExactAuthority.key_ne_of_kind_ne dispatch storage
  rw [dispatchKind, storageKind]
  decide

/-! ## Computed instance controls -/

namespace Examples

namespace Dispatch

open Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation

def shape : TableShape :=
  ⟨32, [.insertFresh, .lookup]⟩

def plan : Plan :=
  ⟨32, [.insertFresh, .lookup]⟩

def source : SourceProgram Nat String where
  shape := shape
  entries := [(7, "seven"), (9, "nine")]
  queries := [9, 3, 7]

def evidence : SingleValuedDispatch.Evidence source where
  plan := plan
  shapeAccepted := rfl
  keysDistinct := by
    simp [source,
      Mettapedia.Util.LinearHash.allDistinct_eq_eraseDupsLength]
    simp only [List.eraseDups_cons, List.filter]
    decide

def duplicateSource : SourceProgram Nat String where
  shape := shape
  entries := [(7, "first"), (7, "second")]
  queries := [7]

theorem positive_recognized :
    (SingleValuedDispatch.recognize source).isSome = true := by
  simp [SingleValuedDispatch.recognize, source, shape,
    Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.recognize,
    effectSupported,
    Mettapedia.Util.LinearHash.allDistinct_eq_eraseDupsLength]
  simp only [List.eraseDups_cons, List.filter]
  decide

theorem duplicate_rejected :
    SingleValuedDispatch.recognize duplicateSource = none := by
  simp [SingleValuedDispatch.recognize, duplicateSource, shape,
    Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.recognize,
    effectSupported,
    Mettapedia.Util.LinearHash.allDistinct_eq_eraseDupsLength]
  simp only [List.eraseDups_cons, List.filter]
  decide

def authority : ExactAuthority
    (SingleValuedDispatch.spec (Key := Nat) (Value := String)) source where
  key :=
    { occurrence := (.singleValuedDispatch, source)
      revision := 4
      dialect := "petta"
      expected := .prim .sym
      authority := "native-typecheck-v3" }
  occurrence_eq := rfl
  judgment := SingleValuedDispatch.nativeJudgment source _ (by simp [exactTy])

/-- A cost receipt is attached after semantic and type/shape admission. -/
def profitability : ProfitabilityReceipt
    (SingleValuedDispatch.spec (Key := Nat) (Value := String)) source
      authority evidence where
  key := authority.key
  same_key := rfl
  baseline :=
    (SingleValuedDispatch.spec (Key := Nat)
      (Value := String)).sourceWorkSpan source
  optimized :=
    (SingleValuedDispatch.spec (Key := Nat)
      (Value := String)).artifactWorkSpan source
        ((SingleValuedDispatch.spec (Key := Nat)
          (Value := String)).compile source evidence)
  baseline_eq := rfl
  optimized_eq := rfl
  improves :=
    SingleValuedDispatch.artifactWorkSpan_le_sourceWorkSpan source evidence

def profitablePlan : ProfitablePlan
    (SingleValuedDispatch.spec (Key := Nat) (Value := String)) source :=
  ⟨authority, evidence, profitability⟩

theorem profitable_plan_observes_source :
    profitablePlan.toExecutionPlan.observe =
      runSource source :=
  profitablePlan.toExecutionPlan.observe_eq_source

end Dispatch

namespace Storage

open Mettapedia.GSLT.LanguageDef.ReusableSlotBufferCompilation

def program : ObservableProgram 1 Nat Nat where
  transactions := [[(0, 7)], [(0, 9)]]
  observe := fun snapshot => snapshot.length

def source : NonEscapingStorage.Source (width := 1) (Value := Nat)
    (Observation := Nat) where
  plan := reusableCallPlan
  program := program

def retainedSource : NonEscapingStorage.Source (width := 1) (Value := Nat)
    (Observation := Nat) where
  plan := ⟨.retained, .reference⟩
  program := program

theorem positive_recognized :
    (NonEscapingStorage.recognize source).isSome = true := rfl

theorem retained_reference_rejected :
    NonEscapingStorage.recognize retainedSource = none := rfl

end Storage

namespace Memo

open Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCompilation
open Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCompilation.PhysicalSnapshot

def store : Store Nat where
  identity := 12
  present := [true]
  tables := [[40, 50]]

def appendedStore : Store Nat where
  identity := 12
  present := [true]
  tables := [[40, 50, 60]]

def resolve (_present : List Bool) (tables : List (List Nat))
    (key : Nat) : Option Nat :=
  tables[0]?.bind fun rows => rows[key]?

def stableSource : RevisionStableMemo.Source (Row := Nat) (Key := Nat)
    (Value := Nat) where
  resolve := resolve
  before := store
  after := store
  appendOnly := by
    exact .cons (List.prefix_refl _) .nil
  keys := [0, 1, 3]

def changedSource : RevisionStableMemo.Source (Row := Nat) (Key := Nat)
    (Value := Nat) where
  resolve := resolve
  before := store
  after := appendedStore
  appendOnly := by
    exact .cons (by simp) .nil
  keys := [0, 1, 2]

theorem stable_revision_recognized :
    (RevisionStableMemo.recognize stableSource).isSome = true := by
  decide

theorem changed_revision_rejected :
    RevisionStableMemo.recognize changedSource = none := by
  decide

end Memo

end Examples

#print axioms ExecutionPlan.observe_eq_source
#print axioms observe_prepare
#print axioms ProfitablePlan.workSpan_le_source
#print axioms SingleValuedDispatch.artifactWorkSpan_le_sourceWorkSpan
#print axioms NonEscapingStorage.artifactWorkSpan_le_sourceWorkSpan
#print axioms RevisionStableMemo.spec
#print axioms storage_rejects_dispatch_class
#print axioms dispatch_envelope_cannot_activate_storage
#print axioms dispatch_storage_authority_keys_differ
#print axioms Examples.Dispatch.profitable_plan_observes_source
#print axioms Examples.Storage.retained_reference_rejected
#print axioms Examples.Memo.changed_revision_rejected

end Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationAdmission
