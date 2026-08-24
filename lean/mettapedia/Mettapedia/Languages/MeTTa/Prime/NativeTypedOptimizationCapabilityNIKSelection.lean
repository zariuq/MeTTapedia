import Mettapedia.Languages.MeTTa.Prime.NIKProfitabilityFrontierSelection
import Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationInstances
import Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission

/-!
# Request-local native selection for typed optimizations

An `OptimizationSpec` proves observational adequacy, but that fact alone does
not impose a global strength order between ordinary execution and a compiled
artifact.  This module gives the conservative generic connection to the
maximal-native calculus:

* ordinary and compiled execution are incomparable in a semantics-only
  request, so an independent profitability policy may choose between them;
* an explicit compiled-artifact request has exactly the compiled face and
  therefore one unique strongest realization; and
* the compiled family can be constructed only from source/key-indexed native
  authority plus the specification's own recognized shape evidence.

A hosted calculus may prove a stronger order for a particular artifact, as
the prepared Metamath lookup client does.  The generic optimizer bridge does
not manufacture that theorem merely from observational equivalence.
-/

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeTypedOptimizationCapabilityNIKSelection

open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open NativeTypedOptimizationAdmission
open NativeTypedOptimizationNIKBridge

/-! ## Two honest execution faces -/

inductive Face where
  | ordinary
  | compiled
  deriving DecidableEq, Repr

/-- Observational equivalence alone does not order two implementations. -/
instance : PartialOrder Face where
  le := Eq
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ first second => first.trans second
  le_antisymm := fun _ _ forward _ => forward

inductive Capability where
  | exactObservation
  | compiledArtifact
  deriving DecidableEq, Repr

def supports : Face → Capability → Prop
  | _, .exactObservation => True
  | .ordinary, .compiledArtifact => False
  | .compiled, .compiledArtifact => True

/-- The common receipt retains either the exact ordinary face or the actual
compiled artifact. -/
inductive Receipt {Source : Type} (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) where
  | ordinary
  | compiled (artifact : spec.Artifact candidate.source)

namespace Receipt

def face {Source : Type} {spec : OptimizationSpec Source}
    {candidate : KeyedCandidate spec} :
    Receipt spec candidate → Face
  | .ordinary => .ordinary
  | .compiled _ => .compiled

def observe {Source : Type} {spec : OptimizationSpec Source}
    {candidate : KeyedCandidate spec} :
    Receipt spec candidate → spec.Observation candidate.source
  | .ordinary => spec.observeSource candidate.source
  | .compiled artifact =>
      spec.observeArtifact candidate.source artifact

end Receipt

/-- Eligibility is the exact conjunction used by typed preparation: native
authority at the complete key and a witness returned by this recognizer. -/
structure Eligibility {Source : Type} (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) where
  authority : AlignedAuthority candidate
  shape : spec.ShapeEvidence candidate.source
  recognized : spec.recognize candidate.source = some shape

def sourceObject {Source : Type} {spec : OptimizationSpec Source}
    (candidate : KeyedCandidate spec) : AdmissionObject where
  Carrier := ExactOccurrence candidate
  Meaning := fun occurrence => occurrence.1 = candidate.source

def targetObject {Source : Type} (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) : AdmissionObject where
  Carrier := Receipt spec candidate
  Meaning := fun receipt =>
    receipt.observe = spec.observeSource candidate.source

/-- Ordinary execution is the fail-open semantic face. -/
def ordinaryOperation {Source : Type} (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) :
    sourceObject candidate ⟶ targetObject spec candidate where
  run := fun _ => .ordinary
  preserves := fun _ _ => rfl

/-- The compiled operation retains the produced artifact, and independent
adequacy proves that its observation is the ordinary observation. -/
def compiledOperation {Source : Type} (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec)
    (shape : spec.ShapeEvidence candidate.source) :
    sourceObject candidate ⟶ targetObject spec candidate where
  run := fun _ => .compiled (spec.compile candidate.source shape)
  preserves := fun _ _ => spec.adequate candidate.source shape

/-- The generic family is deliberately discrete.  A particular hosted
calculus may later prove an additional strength relation, but adequacy alone
does not do so. -/
def family {Source : Type} (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) (eligible : Eligibility spec candidate) :
    RecognizedFamily Face (sourceObject candidate)
      (targetObject spec candidate) where
  package
    | .ordinary => ordinaryOperation spec candidate
    | .compiled => compiledOperation spec candidate eligible.shape
  Capability := Capability
  supports := supports
  supports_mono := by
    intro weaker stronger related capability supported
    subst stronger
    exact supported
  strict_support_gain := by
    intro weaker stronger strict
    exact False.elim (strict.2 strict.1.symm)
  recognized := {.ordinary, .compiled}
  licensed := {.ordinary, .compiled}
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := ⟨.ordinary, by simp⟩

theorem eligibility_prepares_compiled {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (eligible : Eligibility spec candidate) :
    prepareAtKey spec candidate (some eligible.authority) =
        .optimized eligible.authority eligible.shape ∧
      NativeTypedOptimizationAdmission.prepare spec candidate.source
          (some eligible.authority.authority) =
        ExecutionPlan.optimized eligible.authority.authority eligible.shape :=
  recognized_preparations_agree spec candidate eligible.authority
    eligible.shape eligible.recognized

/-! ## Semantics-only and artifact requests -/

/-- A semantics-only request retains both observationally exact faces. -/
def semanticRequest {Source : Type} {spec : OptimizationSpec Source}
    {candidate : KeyedCandidate spec} (eligible : Eligibility spec candidate) :
    (family spec candidate eligible).CapabilityRequest where
  required := fun capability => capability = .exactObservation
  candidates := {.ordinary, .compiled}
  candidates_exact := by
    intro face
    constructor
    · intro member
      refine ⟨?_, ?_⟩
      · simpa [family] using member
      · intro capability required
        subst capability
        trivial
    · intro data
      simpa [family] using data.1
  candidates_nonempty := ⟨.ordinary, by simp⟩

/-- Adequacy alone provides two incomparable maximal realizations, not a
canonical strongest implementation. -/
theorem semanticRequest_has_no_strongest {Source : Type}
    {spec : OptimizationSpec Source} {candidate : KeyedCandidate spec}
    (eligible : Eligibility spec candidate) :
    ¬ ∃ chosen,
      (semanticRequest eligible).restrictedFamily.IsGreatestLicensed chosen := by
  rintro ⟨chosen, strongest⟩
  cases chosen with
  | ordinary =>
      have impossible : Face.compiled ≤ Face.ordinary :=
        strongest.2 .compiled (by
          simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
            semanticRequest])
      cases impossible
  | compiled =>
      have impossible : Face.ordinary ≤ Face.compiled :=
        strongest.2 .ordinary (by
          simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
            semanticRequest])
      cases impossible

/-- Requesting the artifact itself cuts out precisely the compiled face. -/
def compiledRequest {Source : Type} {spec : OptimizationSpec Source}
    {candidate : KeyedCandidate spec} (eligible : Eligibility spec candidate) :
    (family spec candidate eligible).CapabilityRequest where
  required := fun capability =>
    capability = .exactObservation ∨ capability = .compiledArtifact
  candidates := {.compiled}
  candidates_exact := by
    intro face
    constructor
    · intro member
      have equal : face = .compiled := by
        simpa using member
      subst face
      refine ⟨by simp [family], ?_⟩
      intro capability required
      rcases required with rfl | rfl <;> trivial
    · intro data
      have artifactSupport :=
        data.2 .compiledArtifact (Or.inr rfl)
      cases face with
      | ordinary =>
          change False at artifactSupport
          exact artifactSupport.elim
      | compiled => simp
  candidates_nonempty := ⟨.compiled, by simp⟩

def compiledSelection {Source : Type} {spec : OptimizationSpec Source}
    {candidate : KeyedCandidate spec} (eligible : Eligibility spec candidate) :
    (compiledRequest eligible).StrongestNativeCalculusPrinciple where
  val := .compiled
  property := by
    constructor
    · change Face.compiled ∈ ({Face.compiled} : Finset Face)
      simp
    · intro face member
      change face ∈ ({Face.compiled} : Finset Face) at member
      have equal : face = .compiled := Finset.mem_singleton.mp member
      subst face
      rfl

theorem compiledRequest_uniqueStrongest {Source : Type}
    {spec : OptimizationSpec Source} {candidate : KeyedCandidate spec}
    (eligible : Eligibility spec candidate) :
    ∃! chosen,
      (compiledRequest eligible).restrictedFamily.IsGreatestLicensed chosen := by
  refine ⟨.compiled, (compiledSelection eligible).property, ?_⟩
  intro other otherStrongest
  exact RecognizedFamily.greatestLicensed_unique
    (compiledRequest eligible).restrictedFamily otherStrongest
      (compiledSelection eligible).property

/-! ## Profitability remains a policy over the neutral frontier -/

def workCost {Source : Type} {spec : OptimizationSpec Source}
    {candidate : KeyedCandidate spec} {eligible : Eligibility spec candidate}
    (receipt : ProfitabilityReceipt spec candidate.source
      eligible.authority.authority eligible.shape) : Face → Nat
  | .ordinary => receipt.baseline.work
  | .compiled => receipt.optimized.work

/-- The declared work-coordinate projection of a WorkSpan receipt may choose
the compiled member of the neutral semantic frontier, but does not
retroactively make it the strongest calculus. -/
def workProfitabilitySelection {Source : Type}
    {spec : OptimizationSpec Source} {candidate : KeyedCandidate spec}
    (eligible : Eligibility spec candidate)
    (receipt : ProfitabilityReceipt spec candidate.source
      eligible.authority.authority eligible.shape) :
    NIKProfitabilityFrontierSelection.RecognizedFamily.CapabilityRequest.ProfitabilitySelection
      (semanticRequest eligible) Nat (workCost receipt) where
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
    | ordinary => exact receipt.improves.1
    | compiled => exact le_rfl

theorem profitability_selects_without_inventing_strength {Source : Type}
    {spec : OptimizationSpec Source} {candidate : KeyedCandidate spec}
    (eligible : Eligibility spec candidate)
    (receipt : ProfitabilityReceipt spec candidate.source
      eligible.authority.authority eligible.shape) :
    Nonempty
        (NIKProfitabilityFrontierSelection.RecognizedFamily.CapabilityRequest.ProfitabilitySelection
          (semanticRequest eligible) Nat (workCost receipt)) ∧
      ¬ ∃ chosen,
        (semanticRequest eligible).restrictedFamily.IsGreatestLicensed chosen :=
  ⟨⟨workProfitabilitySelection eligible receipt⟩,
    semanticRequest_has_no_strongest eligible⟩

/-! ## Revision-current Metamath positive -/

namespace MetamathCanary

open NativeTypedOptimizationInstances.MetamathOperationRecordFusion

def eligible : Eligibility spec candidate where
  authority := authority
  shape := evidence
  recognized := recognized

abbrev dependencies := keyDependencies
  (Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.SourceProgram
    String
    (Option Mettapedia.Languages.Metamath.SourceGSLTOperations.NodeBinding))

noncomputable def admission :=
  admitStrongestAt (family spec candidate eligible)
    (compiledRequest eligible) (compiledSelection eligible)
    dependencies nativeKey

noncomputable def active : admission.Active nativeKey :=
  admission.activate (dependencies.sameDependencies_refl nativeKey)

def input : ExactOccurrence candidate := ⟨source, rfl⟩

/-- The active strongest artifact request runs the actual compiled Metamath
record table and retains its exact source observation. -/
theorem current_selection_compiles_exact_artifact :
    (active.run input).face = Face.compiled ∧
      (active.run input).observe = spec.observeSource source := by
  constructor
  · rfl
  · exact spec.adequate source evidence

def nextKey : OptimizationKey
    (Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.SourceProgram
      String
      (Option Mettapedia.Languages.Metamath.SourceGSLTOperations.NodeBinding)) :=
  { nativeKey with revision := nativeKey.revision + 1 }

/-- A complete-key revision change prevents activation; it does not silently
fall through to the ordinary face inside the selected admission. -/
theorem changed_revision_prevents_compiled_activation :
    ¬ Nonempty (admission.Active nextKey) := by
  rintro ⟨stale⟩
  have equal := stale.current ()
  change nativeKey = nextKey at equal
  have revisionEqual := congrArg
    (fun key : OptimizationKey
      (Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.SourceProgram
        String
        (Option Mettapedia.Languages.Metamath.SourceGSLTOperations.NodeBinding)) =>
      key.revision) equal
  simp [nextKey, nativeKey] at revisionEqual

end MetamathCanary

/-! ## Exact native judgment without optimization eligibility -/

namespace StorageCanary

open NativeTypedOptimizationInstances.StorageReuse

/-- A retained reference still has a native storage judgment, but its refusing
recognizer prevents it from entering any compiled-artifact request. -/
theorem retained_native_judgment_does_not_force_eligibility :
    Nonempty (ExactAuthority spec retainedSource) ∧
      ¬ Nonempty (Eligibility spec retainedCandidate) := by
  constructor
  · exact ⟨retainedNativeAuthority⟩
  · rintro ⟨eligible⟩
    have recognized := eligible.recognized
    change
      NonEscapingStorage.recognize retainedSource =
        some eligible.shape at recognized
    rw [NativeTypedOptimizationAdmission.Examples.Storage.retained_reference_rejected]
      at recognized
    cases recognized

end StorageCanary

/-! ## Axiom audit -/

#print axioms eligibility_prepares_compiled
#print axioms semanticRequest_has_no_strongest
#print axioms compiledRequest_uniqueStrongest
#print axioms profitability_selects_without_inventing_strength
#print axioms MetamathCanary.current_selection_compiles_exact_artifact
#print axioms MetamathCanary.changed_revision_prevents_compiled_activation
#print axioms StorageCanary.retained_native_judgment_does_not_force_eligibility

end NativeTypedOptimizationCapabilityNIKSelection
end Mettapedia.Languages.MeTTa.Prime
