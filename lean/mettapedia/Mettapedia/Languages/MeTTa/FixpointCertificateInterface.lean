import Mettapedia.Languages.MeTTa.FixpointKernelSpec
import Mettapedia.Languages.MeTTa.PureCertificateFragment
import Mettapedia.Languages.MeTTa.PureCheckingService
import Mettapedia.Languages.MeTTa.RuntimeExec
import Mettapedia.Languages.ProcessCalculi.MORK.MeTTaILBridge
import Mettapedia.Languages.ProcessCalculi.MORK.Space

/-!
# Structural Fixpoint Interface to the Current Pure Certificate Lane

This file packages the first theoremic bridge from the minimal structural
fixpoint contract to:

- the current restricted `MeTTa-Pure` certificate lane, and
- a narrow runtime-friendly artifact/query view.

It does **not** claim that fixpoints are implemented in `MeTTa-Pure`.
It only records the first honest overlap we can state now.
-/

namespace Mettapedia.Languages.MeTTa

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.RuntimeExec
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Proof-lane classification for one structural fixpoint interface. -/
structure FixpointCertificateInterface where
  kernelInterface : StructuralFixpointKernelInterface
  supportedJudgments : List PureJudgmentKind
  region : ElaboratedRegion
  overlapClass : OverlapClass

/-- Current starter structural fixpoints are proof-lane extensions first. -/
def starterFixpointInterface
    (iface : StructuralFixpointKernelInterface) : FixpointCertificateInterface :=
  { kernelInterface := iface
    supportedJudgments := [.closedTyping, .quotedArtifactAgreement]
    region := .pureKernelRegion
    overlapClass := .artifactOnly }

theorem starterFixpointInterface_region
    (iface : StructuralFixpointKernelInterface) :
    (starterFixpointInterface iface).region = ElaboratedRegion.pureKernelRegion := rfl

theorem starterFixpointInterface_overlap
    (iface : StructuralFixpointKernelInterface) :
    (starterFixpointInterface iface).overlapClass = OverlapClass.artifactOnly := rfl

theorem starterFixpointInterface_supports_closedTyping
    (iface : StructuralFixpointKernelInterface) :
    PureJudgmentKind.closedTyping ∈ (starterFixpointInterface iface).supportedJudgments := by
  simp [starterFixpointInterface]

theorem starterFixpointInterface_supports_artifactAgreement
    (iface : StructuralFixpointKernelInterface) :
    PureJudgmentKind.quotedArtifactAgreement ∈
      (starterFixpointInterface iface).supportedJudgments := by
  simp [starterFixpointInterface]

theorem starterFixpointInterface_refines_pureCheckingBoundary_region
    (iface : StructuralFixpointKernelInterface) :
    (starterFixpointInterface iface).region = pureCheckingBoundary.region := by
  rfl

theorem starterFixpointInterface_refines_pureCheckingBoundary_overlap
    (iface : StructuralFixpointKernelInterface) :
    (starterFixpointInterface iface).overlapClass = pureCheckingBoundary.overlapClass := by
  rfl

theorem starterFixpointInterface_refines_pureCheckingBoundary_closedTyping :
    PureJudgmentKind.closedTyping ∈ pureCheckingBoundary.supportedJudgments := by
  exact pureCheckingBoundary_supports_closedTyping

theorem starterFixpointInterface_refines_pureCheckingBoundary_artifactAgreement :
    PureJudgmentKind.quotedArtifactAgreement ∈ pureCheckingBoundary.supportedJudgments := by
  exact pureCheckingBoundary_supports_quotedArtifactAgreement

/-- Runtime-friendly artifact candidate for a structural fixpoint symbol. -/
structure FixpointRuntimeCandidate where
  kernelInterface : StructuralFixpointKernelInterface
  artifact : SharedArtifact
  runtimeTranslatable : morkTranslatable artifact.pattern = true

def structuralFixpointSymbolArtifact (iface : StructuralFixpointKernelInterface) : SharedArtifact :=
  ⟨.apply iface.hook.functionName []⟩

def natIsZeroRuntimeCandidate : FixpointRuntimeCandidate :=
  { kernelInterface := natIsZeroFixpointInterface
    artifact := structuralFixpointSymbolArtifact natIsZeroFixpointInterface
    runtimeTranslatable := by simp [structuralFixpointSymbolArtifact, morkTranslatable, morkTranslatableList] }

def natPredRuntimeCandidate : FixpointRuntimeCandidate :=
  { kernelInterface := natPredFixpointInterface
    artifact := structuralFixpointSymbolArtifact natPredFixpointInterface
    runtimeTranslatable := by simp [structuralFixpointSymbolArtifact, morkTranslatable, morkTranslatableList] }

/-- The first proof/runtime bridge object for starter structural fixpoints. -/
structure FixpointOverlapBridge where
  proofInterface : FixpointCertificateInterface
  runtimeCandidate : FixpointRuntimeCandidate
  sameInterface : runtimeCandidate.kernelInterface = proofInterface.kernelInterface

def natIsZeroFixpointOverlapBridge : FixpointOverlapBridge :=
  { proofInterface := starterFixpointInterface natIsZeroFixpointInterface
    runtimeCandidate := natIsZeroRuntimeCandidate
    sameInterface := rfl }

def natPredFixpointOverlapBridge : FixpointOverlapBridge :=
  { proofInterface := starterFixpointInterface natPredFixpointInterface
    runtimeCandidate := natPredRuntimeCandidate
    sameInterface := rfl }

theorem natIsZeroFixpointOverlap_is_artifactOnly :
    natIsZeroFixpointOverlapBridge.proofInterface.overlapClass = OverlapClass.artifactOnly := rfl

theorem natPredFixpointOverlap_is_artifactOnly :
    natPredFixpointOverlapBridge.proofInterface.overlapClass = OverlapClass.artifactOnly := rfl

theorem natIsZeroFixpoint_runtimeTranslatable :
    morkTranslatable natIsZeroFixpointOverlapBridge.runtimeCandidate.artifact.pattern = true :=
  natIsZeroFixpointOverlapBridge.runtimeCandidate.runtimeTranslatable

theorem natPredFixpoint_runtimeTranslatable :
    morkTranslatable natPredFixpointOverlapBridge.runtimeCandidate.artifact.pattern = true :=
  natPredFixpointOverlapBridge.runtimeCandidate.runtimeTranslatable

/-- Generic query-compatibility for a named symbol artifact. -/
theorem namedSymbolArtifact_queryCompatible (name : String) :
    let pat : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern := .apply name []
    let a := morkPatternToAtom pat
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  dsimp [morkRuntimeQueryExec0]
  simp [Mettapedia.Languages.ProcessCalculi.MORK.matchSourceFactor]
  apply Mettapedia.Languages.ProcessCalculi.MORK.matchOneInSpace_mem
  · simp
  · change
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom []
        (morkPatternToAtom (.apply name []))
        (morkPatternToAtom (.apply name [])) = some []
    simp [Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom]
    simp [Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
      Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom.morkPatternToAtomList,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom.matchAtomList]

theorem natIsZeroFixpoint_queryCompatible :
    let a := morkPatternToAtom natIsZeroFixpointOverlapBridge.runtimeCandidate.artifact.pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [natIsZeroFixpointOverlapBridge, natIsZeroRuntimeCandidate, structuralFixpointSymbolArtifact] using
    namedSymbolArtifact_queryCompatible "Nat.isZero"

theorem natPredFixpoint_queryCompatible :
    let a := morkPatternToAtom natPredFixpointOverlapBridge.runtimeCandidate.artifact.pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [natPredFixpointOverlapBridge, natPredRuntimeCandidate, structuralFixpointSymbolArtifact] using
    namedSymbolArtifact_queryCompatible "Nat.pred"

theorem starterStructuralFixpoints_currently_artifactOnly :
    ∀ iface ∈ starterStructuralFixpoints,
      (starterFixpointInterface iface).overlapClass = OverlapClass.artifactOnly := by
  intro iface hiface
  simp [starterStructuralFixpoints] at hiface
  rcases hiface with hiface | hiface
  · subst hiface
    rfl
  · subst hiface
    rfl

theorem starterStructuralFixpoints_refine_pureCheckingBoundary :
    ∀ iface ∈ starterStructuralFixpoints,
      (starterFixpointInterface iface).region = pureCheckingBoundary.region ∧
      (starterFixpointInterface iface).overlapClass = pureCheckingBoundary.overlapClass := by
  intro iface hiface
  simp [starterStructuralFixpoints] at hiface
  rcases hiface with hiface | hiface
  · subst hiface
    constructor <;> rfl
  · subst hiface
    constructor <;> rfl

end Mettapedia.Languages.MeTTa
