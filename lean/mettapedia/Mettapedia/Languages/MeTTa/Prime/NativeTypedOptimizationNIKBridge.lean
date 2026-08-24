import Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission
import Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationAdmission

/-!
# Typed Prime optimization as ordinary NIK admission

The native typed-optimization calculus and the generic NIK optimization
doctrine describe the same admission boundary at different levels.  This
module proves the connection rather than installing a second authority.

A keyed typed candidate induces an extensional operational square:

* its source terms are exact occurrences of that candidate;
* its target terms are artifacts compiled by the candidate's own recognizer;
* target meaning is the independently stated adequacy equation; and
* both sides expose one common dependent observation value.

The resulting NIK family retains the complete typed key as its dependency
revision.  Currentness therefore covers the optimization class, source
occurrence, logical revision, dialect, expected type, and authority identity.
Native WorkSpan receipts descend to NIK path-profitability receipts only after
the semantic square exists.

This is deliberately an extensional whole-transformation model.  It does not
claim to recover internal instruction traces from an `OptimizationSpec` that
only specifies input/output observation equality.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationNIKBridge

open Mettapedia.Algebra
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationAdmission

/-! ## Exact keyed candidates -/

/-- A proposed optimization occurrence before its hosted calculus supplies
the source/key-indexed native judgment.  The key itself already binds the
optimization family and source. -/
structure KeyedCandidate {Source : Type}
    (spec : OptimizationSpec Source) where
  source : Source
  key : OptimizationKey Source
  occurrence_eq : key.occurrence = (spec.kind, source)

namespace KeyedCandidate

theorem key_kind {Source : Type} {spec : OptimizationSpec Source}
    (candidate : KeyedCandidate spec) :
    candidate.key.occurrence.1 = spec.kind := by
  exact congrArg Prod.fst candidate.occurrence_eq

theorem key_source {Source : Type} {spec : OptimizationSpec Source}
    (candidate : KeyedCandidate spec) :
    candidate.key.occurrence.2 = candidate.source := by
  exact congrArg Prod.snd candidate.occurrence_eq

/-- Every native exact authority determines its canonical keyed candidate. -/
def ofAuthority {Source : Type} (spec : OptimizationSpec Source)
    {source : Source} (authority : ExactAuthority spec source) :
    KeyedCandidate spec where
  source := source
  key := authority.key
  occurrence_eq := authority.occurrence_eq

end KeyedCandidate

/-- NIK authority for one keyed candidate is native exact authority together
with equality of the complete retained key. -/
structure AlignedAuthority {Source : Type}
    {spec : OptimizationSpec Source} (candidate : KeyedCandidate spec) where
  authority : ExactAuthority spec candidate.source
  key_eq : authority.key = candidate.key

namespace AlignedAuthority

def ofAuthority {Source : Type} (spec : OptimizationSpec Source)
    {source : Source} (authority : ExactAuthority spec source) :
    AlignedAuthority (KeyedCandidate.ofAuthority spec authority) where
  authority := authority
  key_eq := rfl

end AlignedAuthority

/-- A foreign optimization-family tag cannot share this candidate's complete
key.  No second specification is needed to state the obstruction. -/
theorem foreign_authority_key_ne_of_kind_ne {Source : Type}
    {spec : OptimizationSpec Source}
    (candidate : KeyedCandidate spec)
    {foreign : OptimizationSpec Source}
    (authority : ExactAuthority foreign candidate.source)
    (different : foreign.kind ≠ spec.kind) :
    authority.key ≠ candidate.key := by
  intro sameKey
  apply different
  calc
    foreign.kind = authority.key.occurrence.1 := authority.key_kind.symm
    _ = candidate.key.occurrence.1 :=
      congrArg (fun key : OptimizationKey Source => key.occurrence.1) sameKey
    _ = spec.kind := candidate.key_kind

/-- An authority from another optimization family cannot be aligned to this
candidate's key.  The obstruction is already visible in the occurrence tag. -/
theorem authority_key_ne_of_kind_ne {Source : Type}
    {left right : OptimizationSpec Source}
    (candidate : KeyedCandidate left)
    (authority : ExactAuthority right candidate.source)
    (different : right.kind ≠ left.kind) :
    authority.key ≠ candidate.key :=
  foreign_authority_key_ne_of_kind_ne candidate authority different

/-! ## Extensional source and artifact semantics -/

/-- The common observation retains the exact keyed candidate before exposing
its source-dependent observation fibre. -/
abbrev ObservationValue {Source : Type}
    (spec : OptimizationSpec Source) :=
  Sigma fun candidate : KeyedCandidate spec => spec.Observation candidate.source

/-- Source terms are occurrences propositionally equal to the candidate's
exact source object. -/
abbrev ExactOccurrence {Source : Type}
    {spec : OptimizationSpec Source} (candidate : KeyedCandidate spec) :=
  { actual : Source // actual = candidate.source }

@[reducible] def sourceTheory {Source : Type}
    {spec : OptimizationSpec Source} (candidate : KeyedCandidate spec) : GSLT :=
  GSLT.discrete (ExactOccurrence candidate)

@[reducible] def targetTheory {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec) : GSLT :=
  GSLT.discrete (spec.Artifact candidate.source)

/-- Every exact source occurrence is semantically available. -/
def sourceOperational {Source : Type}
    {spec : OptimizationSpec Source} (candidate : KeyedCandidate spec) :
    OperationalObject where
  theory := sourceTheory candidate
  Meaning := fun _ => True

/-- A target artifact is meaningful exactly when it satisfies the
specification's independently authored observation equation. -/
def targetOperational {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec) :
    OperationalObject where
  theory := targetTheory spec candidate
  Meaning := fun artifact =>
    spec.observeArtifact candidate.source artifact =
      spec.observeSource candidate.source

def sourceObserved {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec) :
    ObservedOperationalObject (ObservationValue spec) where
  operational := sourceOperational candidate
  observe := fun _ => some ⟨candidate, spec.observeSource candidate.source⟩

def targetObserved {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec) :
    ObservedOperationalObject (ObservationValue spec) where
  operational := targetOperational spec candidate
  observe := fun {_first last} _ =>
    some ⟨candidate, spec.observeArtifact candidate.source last⟩

/-- The recognized compiler is the direct map from the exact source
occurrence to its compiled artifact. -/
def realization {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (shape : spec.ShapeEvidence candidate.source) :
    OperationalRealization (sourceTheory candidate)
      (targetTheory spec candidate) where
  mapTerm := fun _ => spec.compile candidate.source shape
  mapEquiv := fun _ => rfl
  mapStep := fun impossible => impossible.elim

/-- The independent adequacy theorem, not definitional equality, proves that
the compiled artifact lands in the target semantic fibre. -/
def refinement {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (shape : spec.ShapeEvidence candidate.source) :
    Refinement (sourceOperational candidate)
      (targetOperational spec candidate) where
  realization := realization spec candidate shape
  preservesMeaning := fun _ _ => spec.adequate candidate.source shape

/-- The extensional compiler square commutes for every source path.  Since the
source theory is discrete, its only complete executions are reflexive paths;
the substantive step is exactly `OptimizationSpec.adequate`. -/
def observedRefinement {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (shape : spec.ShapeEvidence candidate.source) :
    ObservedRefinement (sourceObserved spec candidate)
      (targetObserved spec candidate) where
  refinement := refinement spec candidate shape
  commutes := by
    intro first last path
    induction path with
    | refl =>
        change
          some (⟨candidate,
            spec.observeArtifact candidate.source
              (spec.compile candidate.source shape)⟩ :
                ObservationValue spec) =
          some (⟨candidate, spec.observeSource candidate.source⟩ :
            ObservationValue spec)
        exact congrArg
          (fun observation =>
            some (⟨candidate, observation⟩ : ObservationValue spec))
          (spec.adequate candidate.source shape)
    | cons step rest inductionHypothesis =>
        rcases step with ⟨impossible⟩
        exact impossible.elim

theorem compiled_artifact_meaning {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (shape : spec.ShapeEvidence candidate.source) :
    (targetOperational spec candidate).Meaning
      (spec.compile candidate.source shape) :=
  spec.adequate candidate.source shape

/-! ## The common NIK optimization family -/

/-- Every native typed optimization specification is an ordinary generic NIK
optimization family over exact keyed candidates. -/
@[reducible] def nikFamily {Source : Type} (spec : OptimizationSpec Source) :
    Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission.OptimizationFamily
      (KeyedCandidate spec) (ObservationValue spec) where
  source := sourceObserved spec
  ExactAuthority := AlignedAuthority
  ShapeEvidence := fun candidate => spec.ShapeEvidence candidate.source
  recognize := fun candidate => spec.recognize candidate.source
  target := fun candidate _authority _shape => targetObserved spec candidate
  refinement := fun candidate _authority shape =>
    observedRefinement spec candidate shape

/-- The complete typed key is the dependency revision used by this bridge. -/
@[reducible] def keyDependencies (Source : Type) : DependencySystem where
  Revision := OptimizationKey Source
  Dependency := Unit
  Value := OptimizationKey Source
  read revision _ := revision

/-- Prepare exactly at the candidate's retained key. -/
def prepareAtKey {Source : Type} (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec)
    (authority : Option (AlignedAuthority candidate)) :=
  Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission.prepare
    (nikFamily spec) (keyDependencies Source) candidate.key candidate authority

@[simp] theorem prepareAtKey_without_authority {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec) :
    prepareAtKey spec candidate none =
      .raw :=
  rfl

/-- Native preparation and generic NIK preparation select the same witnesses
when the specification's own recognizer succeeds. -/
theorem recognized_preparations_agree {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (authority : AlignedAuthority candidate)
    (shape : spec.ShapeEvidence candidate.source)
    (recognized : spec.recognize candidate.source = some shape) :
    prepareAtKey spec candidate (some authority) = .optimized authority shape ∧
      NativeTypedOptimizationAdmission.prepare spec candidate.source
          (some authority.authority) =
        ExecutionPlan.optimized authority.authority shape := by
  constructor <;> simp [prepareAtKey,
    Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission.prepare,
    nikFamily, NativeTypedOptimizationAdmission.prepare, recognized]

/-- The two preparations also agree on fail-open behavior when recognition
declines the source. -/
theorem unrecognized_preparations_agree {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (authority : AlignedAuthority candidate)
    (unrecognized : spec.recognize candidate.source = none) :
    prepareAtKey spec candidate (some authority) = .raw ∧
      NativeTypedOptimizationAdmission.prepare spec candidate.source
          (some authority.authority) = .source := by
  constructor <;> simp [prepareAtKey,
    Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission.prepare,
    nikFamily, NativeTypedOptimizationAdmission.prepare, unrecognized]

/-! ## Exact currentness -/

/-- For an optimized plan, currentness is equality of the complete key. -/
theorem optimized_current_iff {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (authority : AlignedAuthority candidate)
    (shape : spec.ShapeEvidence candidate.source)
    (currentKey : OptimizationKey Source) :
    (Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission.Prepared.optimized
        (family := nikFamily spec) (dependencies := keyDependencies Source)
        (revision := candidate.key) (candidate := candidate)
        authority shape).Current currentKey ↔
      candidate.key = currentKey := by
  change (∀ _dependency : Unit, candidate.key = currentKey) ↔ _
  constructor
  · intro current
    exact current ()
  · intro same _dependency
    exact same

/-- Any change to the complete key prevents reuse of an optimized plan. -/
theorem changed_key_prevents_current {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (authority : AlignedAuthority candidate)
    (shape : spec.ShapeEvidence candidate.source)
    (currentKey : OptimizationKey Source)
    (changed : candidate.key ≠ currentKey) :
    ¬ (Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission.Prepared.optimized
        (family := nikFamily spec) (dependencies := keyDependencies Source)
        (revision := candidate.key) (candidate := candidate)
        authority shape).Current currentKey := by
  rw [optimized_current_iff]
  exact changed

/-- Raw preparation remains current at every key because it carries no
optimized artifact to reuse. -/
theorem raw_current_at_every_key {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (currentKey : OptimizationKey Source) :
    (Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission.Prepared.raw
        (family := nikFamily spec) (dependencies := keyDependencies Source)
        (revision := candidate.key) (candidate := candidate)).Current
      currentKey :=
  trivial

/-! ## Profitability descends only after admission -/

def sourcePathWorkSpan {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec) :
    Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission.PathCost
      (sourceTheory candidate) WorkSpan :=
  fun _path => spec.sourceWorkSpan candidate.source

def targetPathWorkSpan {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec) :
    Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission.PathCost
      (targetTheory spec candidate) WorkSpan :=
  fun {_first last} _path => spec.artifactWorkSpan candidate.source last

/-- A native profitability receipt is indexed by the same complete key as the
candidate admitted by the bridge. -/
theorem profitability_key_eq_candidate {Source : Type}
    {spec : OptimizationSpec Source} {candidate : KeyedCandidate spec}
    {authority : AlignedAuthority candidate}
    {shape : spec.ShapeEvidence candidate.source}
    (receipt : NativeTypedOptimizationAdmission.ProfitabilityReceipt spec
      candidate.source authority.authority shape) :
    receipt.key = candidate.key :=
  receipt.same_key.trans authority.key_eq

/-- A native WorkSpan receipt becomes a generic path receipt for the already
admitted extensional compiler square. -/
def profitabilityReceipt {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (authority : AlignedAuthority candidate)
    (shape : spec.ShapeEvidence candidate.source)
    (receipt : NativeTypedOptimizationAdmission.ProfitabilityReceipt spec
      candidate.source authority.authority shape) :
    Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission.PathProfitabilityReceipt
      (Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission.Prepared.optimized
        (family := nikFamily spec) (dependencies := keyDependencies Source)
        (revision := candidate.key) (candidate := candidate)
        authority shape)
      WorkSpan (sourcePathWorkSpan spec candidate)
      (targetPathWorkSpan spec candidate) where
  improves := by
    intro first last path
    change spec.artifactWorkSpan candidate.source
        (spec.compile candidate.source shape) ≤
      spec.sourceWorkSpan candidate.source
    rw [← receipt.baseline_eq, ← receipt.optimized_eq]
    exact receipt.improves

/-! ## Dispatch instance and adversarial controls -/

namespace DispatchCanary

open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationAdmission.Examples

abbrev spec := SingleValuedDispatch.spec (Key := Nat) (Value := String)

def candidate : KeyedCandidate spec :=
  KeyedCandidate.ofAuthority spec Dispatch.authority

def authority : AlignedAuthority candidate :=
  AlignedAuthority.ofAuthority spec Dispatch.authority

/-- The existing single-valued dispatch example selects the generic NIK
optimized branch with exactly the same recognizer witness as its native plan. -/
theorem native_dispatch_enters_common_nik_family :
    ∃ shape : spec.ShapeEvidence candidate.source,
      prepareAtKey spec candidate (some authority) =
          .optimized authority shape ∧
        NativeTypedOptimizationAdmission.prepare spec candidate.source
            (some authority.authority) =
          ExecutionPlan.optimized authority.authority shape := by
  cases recognized : spec.recognize candidate.source with
  | none =>
      have positive : (spec.recognize candidate.source).isSome = true := by
        change
          (SingleValuedDispatch.recognize Dispatch.source).isSome = true
        exact Dispatch.positive_recognized
      rw [recognized] at positive
      exact Bool.noConfusion positive
  | some shape =>
      exact ⟨shape,
        recognized_preparations_agree spec candidate authority shape recognized⟩

/-- The existing native profitability witness descends to the common NIK
path-policy layer without participating in semantic admission. -/
def pathProfitability :=
  profitabilityReceipt spec candidate authority Dispatch.evidence
    Dispatch.profitability

def changedKey : OptimizationKey
    (Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.SourceProgram
      Nat String) :=
  { candidate.key with revision := candidate.key.revision + 1 }

theorem changedKey_ne : candidate.key ≠ changedKey := by
  intro same
  have revisionSame := congrArg
    (fun key : OptimizationKey
      (Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.SourceProgram
        Nat String) => key.revision) same
  simp [changedKey] at revisionSame

/-- Reusing the optimized dispatch plan after its logical revision changes is
impossible even though the source occurrence itself is unchanged. -/
theorem changed_revision_prevents_dispatch_reuse :
    ¬ (Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission.Prepared.optimized
        (family := nikFamily spec)
        (dependencies := keyDependencies
          (Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.SourceProgram
            Nat String))
        (revision := candidate.key) (candidate := candidate)
        authority Dispatch.evidence).Current changedKey :=
  changed_key_prevents_current spec candidate authority Dispatch.evidence
    changedKey changedKey_ne

end DispatchCanary

#print axioms authority_key_ne_of_kind_ne
#print axioms foreign_authority_key_ne_of_kind_ne
#print axioms observedRefinement
#print axioms compiled_artifact_meaning
#print axioms recognized_preparations_agree
#print axioms unrecognized_preparations_agree
#print axioms optimized_current_iff
#print axioms changed_key_prevents_current
#print axioms profitability_key_eq_candidate
#print axioms profitabilityReceipt
#print axioms DispatchCanary.native_dispatch_enters_common_nik_family
#print axioms DispatchCanary.changed_revision_prevents_dispatch_reuse

end Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationNIKBridge
