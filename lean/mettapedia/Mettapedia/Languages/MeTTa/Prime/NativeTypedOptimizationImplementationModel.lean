import Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationNIKBridge
import Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel

/-!
# Abstract implementation models for native typed optimizations

Every native typed optimization already determines an ordinary
observation-preserving NIK refinement.  This module proves that the same
refinement supplies the abstract Prime implementation contract: exact raw
fallback, exact proof-relevant receipts, revision-current hot execution, and
stale deoptimization.

The codecs below exploit a fact specific to the extensional optimization
bridge: its source and artifact theories are discrete.  Consequently every
complete execution trace is a reflexive occurrence and can be represented
exactly by its retained source occurrence or artifact.  This is a semantic
reference codec, not a concrete ABI claim.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationImplementationModel

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission.PathSpecialization
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationAdmission
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationNIKBridge
open Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel

abbrev indexedSource {Source : Type}
    (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) :=
  PathSpecialization.observedObject (sourceObserved spec candidate)

abbrev indexedTarget {Source : Type}
    (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) :=
  PathSpecialization.observedObject (targetObserved spec candidate)

/-! ## Exact discrete trace codecs -/

/-- A complete trace in the exact-occurrence source theory contains no steps,
so its source occurrence is an exact representation of the whole trace. -/
def sourceTraceCodec {Source : Type}
    (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) :
    ExactCodec (ExecutionTrace (indexedSource spec candidate).operational) where
  Representation := ExactOccurrence candidate
  encode := fun trace => trace.1
  decode := fun occurrence => ⟨occurrence, occurrence, .refl occurrence⟩
  decode_encode := by
    rintro ⟨first, last, execution⟩
    induction execution with
    | refl => rfl
    | cons step rest inductionHypothesis =>
        rcases step with ⟨impossible⟩
        exact impossible.elim

/-- A complete trace in the compiled-artifact theory is represented exactly
by its artifact occurrence. -/
def targetTraceCodec {Source : Type}
    (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) :
    ExactCodec (ExecutionTrace (indexedTarget spec candidate).operational) where
  Representation := spec.Artifact candidate.source
  encode := fun trace => trace.1
  decode := fun artifact => ⟨artifact, artifact, .refl artifact⟩
  decode_encode := by
    rintro ⟨first, last, execution⟩
    induction execution with
    | refl => rfl
    | cons step rest inductionHypothesis =>
        rcases step with ⟨impossible⟩
        exact impossible.elim

/-! ## The common implementation model -/

/-- Exact typed authority and recognizer evidence retain the already-proved
optimization refinement at the complete candidate key. -/
def indexedAdmission {Source : Type}
    (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec)
    (_authority : AlignedAuthority candidate)
    (shape : spec.ShapeEvidence candidate.source) :
    IndexedObservedAdmittedAt (keyDependencies Source) candidate.key
      (indexedSource spec candidate) (indexedTarget spec candidate) where
  refinement := PathSpecialization.observedRefinement
    (observedRefinement spec candidate shape)

/-- Every admitted native typed optimization is a Prime abstract
implementation model.  The construction retains the source occurrence for
fallback and the complete artifact for its receipt. -/
def model {Source : Type}
    (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec)
    (authority : AlignedAuthority candidate)
    (shape : spec.ShapeEvidence candidate.source) :
    AdmittedExecutionModel (keyDependencies Source) candidate.key
      (indexedSource spec candidate) (indexedTarget spec candidate) where
  admission := indexedAdmission spec candidate authority shape
  rawCodec := sourceTraceCodec spec candidate
  receiptCodec := targetTraceCodec spec candidate

/-- The model activates at its complete retained key without rerunning a
recognizer or checker. -/
def active {Source : Type}
    (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec)
    (authority : AlignedAuthority candidate)
    (shape : spec.ShapeEvidence candidate.source) :
    (model spec candidate authority shape).admission.Active candidate.key :=
  (model spec candidate authority shape).admission.activate
    ((keyDependencies Source).sameDependencies_refl candidate.key)

/-- A reflexive exact source occurrence compiles directly to the recognized
artifact occurrence. -/
theorem compile_occurrence {Source : Type}
    (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec)
    (authority : AlignedAuthority candidate)
    (shape : spec.ShapeEvidence candidate.source)
    (occurrence : ExactOccurrence candidate) :
    (model spec candidate authority shape).compileTrace
        (active spec candidate authority shape)
        ⟨occurrence, occurrence, .refl occurrence⟩ =
      ⟨spec.compile candidate.source shape,
        spec.compile candidate.source shape,
        .refl (spec.compile candidate.source shape)⟩ := by
  rfl

/-- The exact source occurrence remains the decoded raw fallback even after a
native artifact has been prepared. -/
theorem fallback_occurrence {Source : Type}
    (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec)
    (authority : AlignedAuthority candidate)
    (shape : spec.ShapeEvidence candidate.source)
    (occurrence : ExactOccurrence candidate) :
    let prepared := (model spec candidate authority shape).prepare
      ⟨occurrence, occurrence, .refl occurrence⟩
    (model spec candidate authority shape).rawCodec.decode prepared.fallback =
      prepared.sourceTrace := by
  exact (model spec candidate authority shape).prepare
    ⟨occurrence, occurrence, .refl occurrence⟩ |>.fallback_adequate

/-- Equality of the complete optimization key is exactly currentness in the
implementation model's dependency system. -/
theorem sameDependencies_iff_key_eq {Source : Type}
    (first second : OptimizationKey Source) :
    (keyDependencies Source).SameDependencies first second ↔ first = second := by
  constructor
  · intro same
    exact same ()
  · rintro rfl
    exact (keyDependencies Source).sameDependencies_refl first

/-- Any changed coordinate of the complete key prevents activation, while the
independently retained raw fallback remains exact. -/
theorem changed_key_prevents_activation_and_preserves_fallback
    {Source : Type}
    (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec)
    (authority : AlignedAuthority candidate)
    (shape : spec.ShapeEvidence candidate.source)
    (currentKey : OptimizationKey Source)
    (changed : candidate.key ≠ currentKey)
    (prepared : (model spec candidate authority shape).PreparedTrace) :
    (¬ (model spec candidate authority shape).admission.Active currentKey) ∧
      (model spec candidate authority shape).rawCodec.decode
          prepared.fallback = prepared.sourceTrace := by
  have stale :
      (model spec candidate authority shape).StaleAt currentKey := by
    intro same
    exact changed ((sameDependencies_iff_key_eq candidate.key currentKey).1 same)
  exact ⟨(model spec candidate authority shape).stale_prevents_activation stale,
    (model spec candidate authority shape).stale_preserves_fallback stale prepared⟩

/-- The model's declared observation agreement is inherited from the admitted
typed optimization square. -/
theorem compile_occurrence_observationAgreement {Source : Type}
    (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec)
    (authority : AlignedAuthority candidate)
    (shape : spec.ShapeEvidence candidate.source)
    (occurrence : ExactOccurrence candidate) :
    (indexedTarget spec candidate).observe
        ((model spec candidate authority shape).compileTrace
          (active spec candidate authority shape)
          ⟨occurrence, occurrence, .refl occurrence⟩).2.2 =
      (indexedSource spec candidate).observe (.refl occurrence) := by
  exact (model spec candidate authority shape).compileTrace_observationAgreement
    (active spec candidate authority shape)
    ⟨occurrence, occurrence, .refl occurrence⟩

#print axioms sourceTraceCodec
#print axioms targetTraceCodec
#print axioms compile_occurrence
#print axioms fallback_occurrence
#print axioms changed_key_prevents_activation_and_preserves_fallback
#print axioms compile_occurrence_observationAgreement

end Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationImplementationModel
