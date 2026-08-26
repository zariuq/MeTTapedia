import Mettapedia.UniversalAI.IncrementalCompressionBridge
import Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationCapabilityNIKSelection

/-!
# Incremental-compression guidance for Prime optimization selection

Incremental compression can guide which already-admissible abstract-machine
representation to run.  It cannot establish semantic adequacy, native typing
authority, recognizer success, or revision currentness.

This module makes that boundary explicit.  A caller supplies a trace projection
from one exact source occurrence to a binary execution trace.  A genuine
`CompressionStep` for that trace gives the compiled face a strictly smaller
two-part code than the ordinary face.  The resulting cost policy is applied
only to the semantic maximal frontier already constructed by Prime's NIK
optimization theory.

The operational consequences are deliberately conservative:

* a compression signal may request preparation, but the existing native
  authority and recognizer still decide whether an optimized plan exists;
* every selected operation is one of the original admitted operations and
  therefore preserves the named observation;
* the complete optimization key still controls reuse across revisions; and
* a signal without authority, or with refusing shape recognition, falls back
  to ordinary source execution.

No runtime trace collector or online learner is constructed here.  This is the
proof-level contract such a collector must satisfy before its guidance may
affect Prime execution.
-/

namespace Mettapedia.Languages.MeTTa.Prime
namespace IncrementalCompressionOptimizationSelection

open KolmogorovComplexity
open Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationAdmission
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationNIKBridge
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationCapabilityNIKSelection
open Mettapedia.Languages.MeTTa.Prime.NIKProfitabilityFrontierSelection

universe uSource

/-! ## Source-scoped compression guidance -/

/-- The declared observable trace of one optimization source.  Keeping this
projection explicit prevents a compression result for one representation from
being silently reused as evidence about another representation. -/
abbrev TraceProjection (Source : Type uSource) := Source → BinString

/-- A strict executable compression witness for the trace projected from one
exact source occurrence.  This witness is controller guidance, not execution
authority. -/
structure CompressionGuidance {Source : Type uSource}
    (U : ConditionalAlgorithm) (trace : TraceProjection Source)
    (source : Source) where
  step : CompressionStep U (trace source)

namespace CompressionGuidance

variable {Source : Type uSource} {U : ConditionalAlgorithm}
variable {trace : TraceProjection Source} {source : Source}

/-- Cost of the uncompressed observed trace. -/
def ordinaryCost (_guidance : CompressionGuidance U trace source) : Nat :=
  (trace source).length

/-- Cost of the executable feature plus its residual. -/
def compiledCost (guidance : CompressionGuidance U trace source) : Nat :=
  guidance.step.featureProgram.length + guidance.step.residual.length

/-- A genuine compression witness strictly prefers its two-part form. -/
theorem compiledCost_lt_ordinaryCost
    (guidance : CompressionGuidance U trace source) :
    guidance.compiledCost < guidance.ordinaryCost :=
  guidance.step.compresses

end CompressionGuidance

/-! ## Guidance-gated native preparation -/

/-- A compression learner may ask Prime to prepare an optimized occurrence.
The actual preparation remains the existing authority-and-recognizer gate.
Without a signal, the source plan is retained. -/
def prepareWithGuidance {Source : Type uSource} {U : ConditionalAlgorithm}
    (spec : OptimizationSpec Source) (trace : TraceProjection Source)
    (source : Source)
    (guidance : Option (CompressionGuidance U trace source))
    (authority : Option (ExactAuthority spec source)) :
    ExecutionPlan spec source :=
  match guidance with
  | none => .source
  | some _ => NativeTypedOptimizationAdmission.prepare spec source authority

@[simp] theorem prepareWithGuidance_without_guidance
    {Source : Type uSource} {U : ConditionalAlgorithm}
    (spec : OptimizationSpec Source) (trace : TraceProjection Source)
    (source : Source) (authority : Option (ExactAuthority spec source)) :
    prepareWithGuidance (U := U) spec trace source none authority = .source :=
  rfl

@[simp] theorem prepareWithGuidance_without_authority
    {Source : Type uSource} {U : ConditionalAlgorithm}
    (spec : OptimizationSpec Source) (trace : TraceProjection Source)
    (source : Source) (guidance : CompressionGuidance U trace source) :
    prepareWithGuidance spec trace source (some guidance) none = .source :=
  rfl

/-- A signal activates the optimized plan only after the existing recognizer
returns shape evidence under exact native authority. -/
theorem prepareWithGuidance_of_recognized
    {Source : Type uSource} {U : ConditionalAlgorithm}
    (spec : OptimizationSpec Source) (trace : TraceProjection Source)
    (source : Source) (guidance : CompressionGuidance U trace source)
    (authority : ExactAuthority spec source)
    (shape : spec.ShapeEvidence source)
    (recognized : spec.recognize source = some shape) :
    prepareWithGuidance spec trace source (some guidance) (some authority) =
      .optimized authority shape := by
  simp [prepareWithGuidance, NativeTypedOptimizationAdmission.prepare,
    recognized]

/-- Compression evidence cannot override a refusing structural recognizer. -/
theorem prepareWithGuidance_of_unrecognized
    {Source : Type uSource} {U : ConditionalAlgorithm}
    (spec : OptimizationSpec Source) (trace : TraceProjection Source)
    (source : Source) (guidance : CompressionGuidance U trace source)
    (authority : ExactAuthority spec source)
    (unrecognized : spec.recognize source = none) :
    prepareWithGuidance spec trace source (some guidance) (some authority) =
      .source := by
  simp [prepareWithGuidance, NativeTypedOptimizationAdmission.prepare,
    unrecognized]

/-- Every outcome of guidance-gated preparation has the ordinary source
observation.  The proof comes from the optimization specification, not from
the compression score. -/
theorem observe_prepareWithGuidance
    {Source : Type uSource} {U : ConditionalAlgorithm}
    (spec : OptimizationSpec Source) (trace : TraceProjection Source)
    (source : Source)
    (guidance : Option (CompressionGuidance U trace source))
    (authority : Option (ExactAuthority spec source)) :
    (prepareWithGuidance spec trace source guidance authority).observe =
      spec.observeSource source :=
  ExecutionPlan.observe_eq_source _

/-! ## IC cost on the certified semantic frontier -/

/-- An explicitly declared description-length observation for one optimization
family.  The source and artifact fibres remain dependent on the exact source
occurrence. -/
structure DescriptionLengthModel {Source : Type}
    (spec : OptimizationSpec Source) where
  sourceLength : Source → Nat
  artifactLength : ∀ source, spec.Artifact source → Nat

/-- The receipt connecting a source-scoped compression witness to the actual
artifact produced by the eligible recognizer witness.  Without both equations,
trace compression is not evidence about the compiled representation's cost. -/
structure CompressionCostReceipt
    {Source : Type} {U : ConditionalAlgorithm}
    {spec : OptimizationSpec Source} {candidate : KeyedCandidate spec}
    (eligible : Eligibility spec candidate)
    {trace : TraceProjection Source}
    (guidance : CompressionGuidance U trace candidate.source)
    (model : DescriptionLengthModel spec) : Prop where
  source_eq :
    model.sourceLength candidate.source = guidance.ordinaryCost
  artifact_eq :
    model.artifactLength candidate.source
        (spec.compile candidate.source eligible.shape) = guidance.compiledCost

/-- The cost policy reads the declared source length and the length of the
actual artifact compiled from the eligible shape witness. -/
def compressionCost {Source : Type}
    {spec : OptimizationSpec Source} {candidate : KeyedCandidate spec}
    (eligible : Eligibility spec candidate)
    (model : DescriptionLengthModel spec) : Face → Nat
  | .ordinary => model.sourceLength candidate.source
  | .compiled => model.artifactLength candidate.source
      (spec.compile candidate.source eligible.shape)

theorem compressionCost_compiled_lt_ordinary
    {Source : Type} {U : ConditionalAlgorithm}
    {spec : OptimizationSpec Source} {candidate : KeyedCandidate spec}
    (eligible : Eligibility spec candidate)
    {trace : TraceProjection Source}
    (guidance : CompressionGuidance U trace candidate.source)
    (model : DescriptionLengthModel spec)
    (receipt : CompressionCostReceipt eligible guidance model) :
    compressionCost eligible model .compiled <
      compressionCost eligible model .ordinary := by
  change model.artifactLength candidate.source
      (spec.compile candidate.source eligible.shape) <
    model.sourceLength candidate.source
  rw [receipt.artifact_eq, receipt.source_eq]
  exact guidance.compiledCost_lt_ordinaryCost

/-- IC chooses the compiled member only after `Eligibility` has already
provided aligned native authority and recognizer evidence.  Both faces are
semantically maximal in the generic equivalence-only request; compression is
therefore a cost policy over that neutral frontier, not a strength theorem. -/
def compressionSelection
    {Source : Type} {U : ConditionalAlgorithm}
    {spec : OptimizationSpec Source} {candidate : KeyedCandidate spec}
    (eligible : Eligibility spec candidate)
    {trace : TraceProjection Source}
    (guidance : CompressionGuidance U trace candidate.source)
    (model : DescriptionLengthModel spec)
    (receipt : CompressionCostReceipt eligible guidance model) :
    RecognizedFamily.CapabilityRequest.ProfitabilitySelection
      (semanticRequest eligible) Nat (compressionCost eligible model) where
  chosen := .compiled
  semanticMaximal := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        semanticRequest]
    · intro other _ related
      exact related.symm
  costMinimal := by
    intro other _
    cases other with
    | ordinary =>
        exact (compressionCost_compiled_lt_ordinary eligible guidance model
          receipt).le
    | compiled => exact le_rfl

/-- The selected operation is an existing admitted operation and preserves
the target meaning. -/
theorem compressionSelection_operation_preserves
    {Source : Type} {U : ConditionalAlgorithm}
    {spec : OptimizationSpec Source} {candidate : KeyedCandidate spec}
    (eligible : Eligibility spec candidate)
    {trace : TraceProjection Source}
    (guidance : CompressionGuidance U trace candidate.source)
    (model : DescriptionLengthModel spec)
    (receipt : CompressionCostReceipt eligible guidance model)
    (input : (sourceObject candidate).Carrier)
    (meaningful : (sourceObject candidate).Meaning input) :
    (targetObject spec candidate).Meaning
      ((compressionSelection eligible guidance model receipt).operation.run
        input) :=
  (compressionSelection eligible guidance model receipt).operation_preserves
    input meaningful

/-- A strict compression policy selects a member of the exact semantic
frontier but still cannot turn either incomparable face into the globally
strongest realization. -/
theorem compression_selects_without_inventing_strength
    {Source : Type} {U : ConditionalAlgorithm}
    {spec : OptimizationSpec Source} {candidate : KeyedCandidate spec}
    (eligible : Eligibility spec candidate)
    {trace : TraceProjection Source}
    (guidance : CompressionGuidance U trace candidate.source)
    (model : DescriptionLengthModel spec)
    (receipt : CompressionCostReceipt eligible guidance model) :
    Nonempty
        (RecognizedFamily.CapabilityRequest.ProfitabilitySelection
          (semanticRequest eligible) Nat (compressionCost eligible model)) ∧
      ¬ ∃ chosen,
        (semanticRequest eligible).restrictedFamily.IsGreatestLicensed chosen :=
  ⟨⟨compressionSelection eligible guidance model receipt⟩,
    semanticRequest_has_no_strongest eligible⟩

/-- Dynamic reuse remains tied to the complete optimization key.  The IC
selection chooses the compiled face, while currentness is exactly equality
with the candidate's retained key. -/
theorem compressionSelection_current_iff
    {Source : Type} {U : ConditionalAlgorithm}
    {spec : OptimizationSpec Source} {candidate : KeyedCandidate spec}
    (eligible : Eligibility spec candidate)
    {trace : TraceProjection Source}
    (guidance : CompressionGuidance U trace candidate.source)
    (model : DescriptionLengthModel spec)
    (receipt : CompressionCostReceipt eligible guidance model)
    (currentKey : OptimizationKey Source) :
    (compressionSelection eligible guidance model receipt).chosen =
        Face.compiled ∧
      ((Prepared.optimized
          (family := nikFamily spec) (dependencies := keyDependencies Source)
          (revision := candidate.key) (candidate := candidate)
          eligible.authority eligible.shape).Current currentKey ↔
        candidate.key = currentKey) :=
  ⟨rfl, optimized_current_iff spec candidate eligible.authority
    eligible.shape currentKey⟩

/-! ## Finite controls -/

namespace Canary

open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationInstances

/-- A small explicit trace projection used only to exercise the admission
boundary.  Production integrations should replace it with an authored machine
trace projection. -/
def fourBitTrace {Source : Type} (_source : Source) : BinString := fourTrue

def finiteGuidance {Source : Type} (source : Source) :
    CompressionGuidance finiteCompressionAlgorithm
      (fourBitTrace (Source := Source)) source where
  step := finiteCompressionStep

/-- Description-length model for the finite control.  It assigns the full
four-bit trace to ordinary execution and the witnessed feature-plus-residual
length to the artifact. -/
def finiteDescriptionLengthModel {Source : Type}
    (spec : OptimizationSpec Source) : DescriptionLengthModel spec where
  sourceLength := fun _ => fourTrue.length
  artifactLength := fun _ _ =>
    finiteCompressionStep.featureProgram.length +
      finiteCompressionStep.residual.length

abbrev metamathEligible :=
  NativeTypedOptimizationCapabilityNIKSelection.MetamathCanary.eligible

def metamathGuidance : CompressionGuidance finiteCompressionAlgorithm
    (fourBitTrace (Source :=
      Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.SourceProgram
        String
        (Option Mettapedia.Languages.Metamath.SourceGSLTOperations.NodeBinding)))
    MetamathOperationRecordFusion.candidate.source :=
  finiteGuidance MetamathOperationRecordFusion.source

def metamathDescriptionLengthModel :
    DescriptionLengthModel MetamathOperationRecordFusion.spec :=
  finiteDescriptionLengthModel MetamathOperationRecordFusion.spec

def metamathCompressionCostReceipt :
    CompressionCostReceipt metamathEligible metamathGuidance
      metamathDescriptionLengthModel where
  source_eq := rfl
  artifact_eq := rfl

def finiteMetamathSelection :=
  compressionSelection metamathEligible metamathGuidance
    metamathDescriptionLengthModel metamathCompressionCostReceipt

/-- Positive control: a genuine strict compression witness selects the
compiled member of an already eligible Metamath optimization, and the selected
operation retains its exact source observation. -/
theorem finite_compression_selects_exact_compiled_face :
    finiteMetamathSelection.chosen = Face.compiled ∧
      (targetObject MetamathOperationRecordFusion.spec
        MetamathOperationRecordFusion.candidate).Meaning
        (finiteMetamathSelection.operation.run
          NativeTypedOptimizationCapabilityNIKSelection.MetamathCanary.input) := by
  constructor
  · rfl
  · apply compressionSelection_operation_preserves metamathEligible
      metamathGuidance metamathDescriptionLengthModel
      metamathCompressionCostReceipt
    rfl

/-- Negative control: even the same genuine compression witness leaves the
dispatch source plan untouched when native authority is absent. -/
theorem finite_compression_without_authority_is_source :
    prepareWithGuidance
        NativeTypedOptimizationNIKBridge.DispatchCanary.spec
        fourBitTrace
        NativeTypedOptimizationNIKBridge.DispatchCanary.candidate.source
        (some (finiteGuidance
          NativeTypedOptimizationNIKBridge.DispatchCanary.candidate.source))
        none = .source :=
  rfl

/-- Negative control: exact native storage authority and a strict compression
signal still cannot override the retained-reference recognizer rejection. -/
theorem finite_compression_cannot_override_lifetime_rejection :
    prepareWithGuidance StorageReuse.spec
        fourBitTrace
        StorageReuse.retainedSource
        (some (finiteGuidance StorageReuse.retainedSource))
        (some StorageReuse.retainedNativeAuthority) = .source := by
  apply prepareWithGuidance_of_unrecognized
  exact NativeTypedOptimizationAdmission.Examples.Storage.retained_reference_rejected

end Canary

#print axioms CompressionGuidance.compiledCost_lt_ordinaryCost
#print axioms observe_prepareWithGuidance
#print axioms compressionSelection_operation_preserves
#print axioms compression_selects_without_inventing_strength
#print axioms compressionSelection_current_iff
#print axioms Canary.finite_compression_selects_exact_compiled_face
#print axioms Canary.finite_compression_without_authority_is_source
#print axioms Canary.finite_compression_cannot_override_lifetime_rejection

end IncrementalCompressionOptimizationSelection
end Mettapedia.Languages.MeTTa.Prime
