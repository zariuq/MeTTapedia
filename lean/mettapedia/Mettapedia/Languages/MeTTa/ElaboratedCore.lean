import Mettapedia.Languages.MeTTa.ElaboratedCoreBase
import Mettapedia.Languages.MeTTa.PureCertificateFragment
import Mettapedia.Languages.MeTTa.PureCheckingService
import Mettapedia.Languages.MeTTa.PureCheckingExtensions
import Mettapedia.Languages.MeTTa.RuntimeExec
import Mettapedia.Languages.MeTTa.Core.Bridge
import Mettapedia.Languages.MeTTa.InductiveCertificateInterface
import Mettapedia.Languages.MeTTa.InductiveKernelExtension
import Mettapedia.Languages.MeTTa.FixpointCertificateInterface
import Mettapedia.Languages.MeTTa.PureRuntimeFrontier

/-!
# Elaborated MeTTa-Core

Proof-of-concept classification layer sitting above `PureKernel` and
`RuntimeExec`.

The point of this module is not to redefine either branch. It makes explicit the
missing middle layer suggested by the current architecture:

- one surface MeTTa node
- one elaborated classification
- multiple certified downstream views

Current regions:

- `pureKernelRegion`: trusted typed fragment routed to `PureKernel`
- `runtimeExecRegion`: effectful/runtime fragment routed to `RuntimeSpec` and
  an execution/query seam
- `oracleRegion`: grounded/FFI/oracle boundary kept explicit
- `metaRegion`: proof/elaboration-time reflection layer
-/

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.DialectProfile
open Mettapedia.Languages.MeTTa.RuntimeSpec
open Mettapedia.Languages.MeTTa.RuntimeExec
open Mettapedia.Languages.MeTTa.Core.Bridge
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.OSLF.MeTTaIL.Syntax

abbrev CoreAtom := Mettapedia.Languages.MeTTa.Core.Atom
abbrev CoreAtomspace := Mettapedia.Languages.MeTTa.Core.Atomspace
abbrev CoreGroundedValue := Mettapedia.Languages.MeTTa.Core.GroundedValue

/-- Thin elaborated-core wrapper around the explicit Pure checking/conversion
service. This keeps the proof-side checking API visibly attached to the middle
layer rather than buried only inside the certificate fragment file. -/
noncomputable def elaborateCheckedPureConversion
    (cert : CheckedPureCertificate)
    (targetType : PureTm 0)
    (h : Conv cert.claimedType targetType) :
    CheckedPureConversion :=
  convertCheckedPureCertificate cert targetType h

theorem elaborateCheckedPureConversion_region
    (cert : CheckedPureCertificate)
    (targetType : PureTm 0)
    (h : Conv cert.claimedType targetType) :
    (elaborateCheckedPureConversion cert targetType h).region =
      ElaboratedRegion.pureKernelRegion := by
  rfl

theorem elaborateCheckedPureConversion_overlap
    (cert : CheckedPureCertificate)
    (targetType : PureTm 0)
    (h : Conv cert.claimedType targetType) :
    (elaborateCheckedPureConversion cert targetType h).overlapClass =
      cert.overlapClass := by
  rfl

theorem elaborateCheckedPureConversion_typing
    (cert : CheckedPureCertificate)
    (targetType : PureTm 0)
    (h : Conv cert.claimedType targetType) :
    HasType .nil
      (elaborateCheckedPureConversion cert targetType h).term
      targetType := by
  exact (elaborateCheckedPureConversion cert targetType h).typing

theorem elaborateCheckedPureConversion_quoteAgreement
    (cert : CheckedPureCertificate)
    (targetType : PureTm 0)
    (h : Conv cert.claimedType targetType) :
    (elaborateCheckedPureConversion cert targetType h).artifact.pattern =
      quoteClosedTm (elaborateCheckedPureConversion cert targetType h).term := by
  exact (elaborateCheckedPureConversion cert targetType h).quoteAgreement

/-- Small typed MeTTa-Core surface fragment whose atoms already have a shared
artifact view through `Core.Bridge.atomToPattern`.

This is intentionally weaker than a direct PureKernel compilation target:
- positive example: symbolic atoms, variables, and expression constructors that
  already admit a `Pattern` view
- negative example: grounded atoms do not currently admit such a view and are
  excluded from this fragment
-/
structure SurfaceCoreTypedAtom where
  space : CoreAtomspace
  atom : CoreAtom
  ty : CoreAtom
  typed : Mettapedia.Languages.MeTTa.Core.HasType space atom ty
  pattern : Pattern
  pattern_eq : atomToPattern atom = some pattern

namespace SurfaceCoreTypedAtom

def toArtifact (surface : SurfaceCoreTypedAtom) : SharedArtifact :=
  ⟨surface.pattern⟩

def ofSymbol (space : CoreAtomspace) (s : String) : SurfaceCoreTypedAtom :=
  { space := space
    atom := .symbol s
    ty := .symbol "Symbol"
    typed := Mettapedia.Languages.MeTTa.Core.HasType.intrinsicSymbol s
    pattern := .apply s []
    pattern_eq := by simp [atomToPattern] }

def ofVariable (space : CoreAtomspace) (v : String) : SurfaceCoreTypedAtom :=
  { space := space
    atom := .var v
    ty := .symbol "Variable"
    typed := Mettapedia.Languages.MeTTa.Core.HasType.intrinsicVariable v
    pattern := .fvar v
    pattern_eq := by simp [atomToPattern] }

def ofAnnotated
    (space : CoreAtomspace)
    (atom ty : CoreAtom)
    (pattern : Pattern)
    (hpattern : atomToPattern atom = some pattern)
    (hannot : Mettapedia.Languages.MeTTa.Core.typeAnnotation atom ty ∈ space.atoms) :
    SurfaceCoreTypedAtom :=
  { space := space
    atom := atom
    ty := ty
    typed := Mettapedia.Languages.MeTTa.Core.annotation_gives_type space atom ty hannot
    pattern := pattern
    pattern_eq := hpattern }

theorem grounded_atom_has_no_pattern (g : CoreGroundedValue) :
    atomToPattern (.grounded g : CoreAtom) = none := by
  simp [atomToPattern]

theorem symbol_pattern_example (space : CoreAtomspace) (s : String) :
    (ofSymbol space s).pattern = .apply s [] := rfl

theorem variable_pattern_example (space : CoreAtomspace) (v : String) :
    (ofVariable space v).pattern = .fvar v := rfl

/-- Soundness of the existing decidable type checker for the first elaborated
typed-atom fragment. This keeps the elaborator honest: checked typed atoms are
turned into proof-carrying typed atoms, not postulated ones. -/
theorem checkType_true_implies_hasType
    (space : CoreAtomspace) (atom ty : CoreAtom) :
    Mettapedia.Languages.MeTTa.Core.checkType space atom ty = true →
      Mettapedia.Languages.MeTTa.Core.HasType space atom ty := by
  intro h
  cases ty with
  | var v =>
      have hmem : Mettapedia.Languages.MeTTa.Core.typeAnnotation atom (.var v) ∈ space.atoms := by
        simpa [Mettapedia.Languages.MeTTa.Core.checkType, Mettapedia.Languages.MeTTa.Core.Atomspace.contains] using h
      exact Mettapedia.Languages.MeTTa.Core.HasType.annotated atom (.var v) hmem
  | grounded g =>
      have hmem : Mettapedia.Languages.MeTTa.Core.typeAnnotation atom (.grounded g) ∈ space.atoms := by
        simpa [Mettapedia.Languages.MeTTa.Core.checkType, Mettapedia.Languages.MeTTa.Core.Atomspace.contains] using h
      exact Mettapedia.Languages.MeTTa.Core.HasType.annotated atom (.grounded g) hmem
  | expression es =>
      have hmem : Mettapedia.Languages.MeTTa.Core.typeAnnotation atom (.expression es) ∈ space.atoms := by
        simpa [Mettapedia.Languages.MeTTa.Core.checkType, Mettapedia.Languages.MeTTa.Core.Atomspace.contains] using h
      exact Mettapedia.Languages.MeTTa.Core.HasType.annotated atom (.expression es) hmem
  | symbol s =>
      by_cases hSymbol : s = "Symbol"
      · subst hSymbol
        cases atom with
        | var v =>
            simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
        | symbol s =>
            exact Mettapedia.Languages.MeTTa.Core.HasType.intrinsicSymbol s
        | grounded g =>
            simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
        | expression es =>
            simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
      · by_cases hVariable : s = "Variable"
        · subst hVariable
          cases atom with
          | var v =>
              exact Mettapedia.Languages.MeTTa.Core.HasType.intrinsicVariable v
          | symbol s =>
              simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
          | grounded g =>
              simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
          | expression es =>
              simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
        · by_cases hGrounded : s = "Grounded"
          · subst hGrounded
            cases atom with
            | var v =>
                simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
            | symbol s =>
                simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
            | grounded g =>
                exact Mettapedia.Languages.MeTTa.Core.HasType.intrinsicGrounded g
            | expression es =>
                simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
          · by_cases hExpression : s = "Expression"
            · subst hExpression
              cases atom with
              | var v =>
                  simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
              | symbol s =>
                  simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
              | grounded g =>
                  simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
              | expression es =>
                  exact Mettapedia.Languages.MeTTa.Core.HasType.intrinsicExpression es
            · by_cases hAtom : s = "Atom"
              · subst hAtom
                exact Mettapedia.Languages.MeTTa.Core.hasTypeAtom space atom
              · by_cases hInt : s = "Int"
                · subst hInt
                  cases atom with
                  | var v =>
                      simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                  | symbol s =>
                      simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                  | grounded g =>
                      cases g with
                      | int n =>
                          exact Mettapedia.Languages.MeTTa.Core.HasType.groundedInt n
                      | string s =>
                          simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                      | bool b =>
                          simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                      | custom typeName data =>
                          simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                  | expression es =>
                      simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                · by_cases hString : s = "String"
                  · subst hString
                    cases atom with
                    | var v =>
                        simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                    | symbol s =>
                        simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                    | grounded g =>
                        cases g with
                        | int n =>
                            simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                        | string s =>
                            exact Mettapedia.Languages.MeTTa.Core.HasType.groundedString s
                        | bool b =>
                            simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                        | custom typeName data =>
                            simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                    | expression es =>
                        simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                  · by_cases hBool : s = "Bool"
                    · subst hBool
                      cases atom with
                      | var v =>
                          simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                      | symbol s =>
                          simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                      | grounded g =>
                          cases g with
                          | int n =>
                              simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                          | string s =>
                              simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                          | bool b =>
                              exact Mettapedia.Languages.MeTTa.Core.HasType.groundedBool b
                          | custom typeName data =>
                              simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                      | expression es =>
                          simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                    · have hmem : Mettapedia.Languages.MeTTa.Core.typeAnnotation atom (.symbol s) ∈ space.atoms := by
                        simpa [Mettapedia.Languages.MeTTa.Core.checkType, hSymbol, hVariable, hGrounded,
                          hExpression, hAtom, hInt, hString, hBool,
                          Mettapedia.Languages.MeTTa.Core.Atomspace.contains] using h
                      exact Mettapedia.Languages.MeTTa.Core.HasType.annotated atom (.symbol s) hmem

end SurfaceCoreTypedAtom

/-- Certificate for the first typed MeTTa-Core fragment above both the proof and
runtime branches.

This still records an `artifactOnly` overlap: the fragment has a typed
proof-oriented contract and a shared MeTTa artifact view, but it is not yet a
direct `R_exec₀` execution certificate. -/
structure CoreTypedCertificate where
  surface : SurfaceCoreTypedAtom
  overlapClass : OverlapClass
  artifact : SharedArtifact
  artifact_eq : artifact.pattern = surface.pattern

def CoreTypedCertificate.backendName (_ : CoreTypedCertificate) : String :=
  "CoreTypes+Artifact"

def certifySurfaceCoreTypedAtom (surface : SurfaceCoreTypedAtom) : CoreTypedCertificate :=
  { surface := surface
    overlapClass := OverlapClass.artifactOnly
    artifact := surface.toArtifact
    artifact_eq := rfl }

namespace SurfaceCoreTypedAtom

/-- First real elaborator for typed MeTTa-Core atoms:

- it checks the type with `checkType`
- it reuses the existing `atomToPattern` bridge for the shared artifact
- it produces an honest certificate only when both views exist -/
def elaborateCheckedCoreTypedAtom?
    (space : CoreAtomspace) (atom ty : CoreAtom) : Option CoreTypedCertificate := do
  match hct : Mettapedia.Languages.MeTTa.Core.checkType space atom ty with
  | false => none
  | true =>
      match hpat : atomToPattern atom with
      | none => none
      | some pattern =>
          let surface : SurfaceCoreTypedAtom :=
            { space := space
              atom := atom
              ty := ty
              typed := checkType_true_implies_hasType space atom ty hct
              pattern := pattern
              pattern_eq := hpat }
          pure (certifySurfaceCoreTypedAtom surface)

end SurfaceCoreTypedAtom

/-- Certificate for the runtime branch. -/
structure RuntimeCertificate where
  dialect : MeTTaDialectProfile
  spec : MeTTaRuntimeSpec
  lowering : RuntimeLowering
  artifact : SharedArtifact
  dialect_eq : spec.dialect = dialect

/-- Certificate for grounded / FFI / oracle calls. -/
structure OracleCertificate where
  dialect : MeTTaDialectProfile
  opName : String
  resultDescriptor : String
  args : List Pattern
  artifact : SharedArtifact

/-- Certificate for elaboration-time / proof-time metaprogramming nodes. -/
structure MetaCertificate where
  description : String
  artifact : SharedArtifact

/-- Certificate for the first inductive-family objects admitted into the
elaborated middle layer.

This stays intentionally modest: it packages the already-built bridge between
the proof-side inductive interface, the future Pure-kernel hook, and the
current runtime-friendly constructor artifact candidate. -/
structure InductiveElaborationCertificate where
  bridge : Mettapedia.Languages.MeTTa.InductiveOverlapBridge
  overlapClass : OverlapClass
  overlap_eq : overlapClass = bridge.proofKernel.proofInterface.overlapClass

def InductiveElaborationCertificate.artifact
    (cert : InductiveElaborationCertificate) : SharedArtifact :=
  cert.bridge.runtimeCandidate.artifact

def InductiveElaborationCertificate.kernelInterface
    (cert : InductiveElaborationCertificate) :
    Mettapedia.Languages.MeTTa.PureInductiveKernelInterface :=
  cert.bridge.proofKernel.kernelInterface

def InductiveElaborationCertificate.kernelBoundary
    (cert : InductiveElaborationCertificate) :
    Mettapedia.Languages.MeTTa.InductiveKernelBoundary :=
  cert.bridge.proofKernel.kernelBoundary

def InductiveElaborationCertificate.familyName
    (cert : InductiveElaborationCertificate) : String :=
  cert.bridge.familyName

theorem InductiveElaborationCertificate.familyName_eq
    (cert : InductiveElaborationCertificate) :
    cert.familyName = cert.bridge.runtimeCandidate.family.name := by
  simpa [InductiveElaborationCertificate.familyName] using
    cert.bridge.familyName_eq

theorem InductiveElaborationCertificate.kernelBoundary_region
    (cert : InductiveElaborationCertificate) :
    cert.kernelBoundary.region = ElaboratedRegion.pureKernelRegion := by
  exact cert.bridge.proofKernel.kernelBoundary_region

theorem InductiveElaborationCertificate.kernelBoundary_overlap
    (cert : InductiveElaborationCertificate) :
    cert.kernelBoundary.overlapClass = OverlapClass.artifactOnly := by
  exact cert.bridge.proofKernel.kernelBoundary_overlap

theorem InductiveElaborationCertificate.kernelBoundary_supports_familyDeclaration
    (cert : InductiveElaborationCertificate) :
    Mettapedia.Languages.MeTTa.InductiveKernelJudgmentKind.familyDeclaration ∈
      cert.kernelBoundary.supportedJudgments := by
  exact cert.bridge.proofKernel.kernelBoundary_supports_familyDeclaration

theorem InductiveElaborationCertificate.kernelBoundary_supports_generatedRecursor
    (cert : InductiveElaborationCertificate) :
    Mettapedia.Languages.MeTTa.InductiveKernelJudgmentKind.generatedRecursor ∈
      cert.kernelBoundary.supportedJudgments := by
  exact cert.bridge.proofKernel.kernelBoundary_supports_generatedRecursor

theorem InductiveElaborationCertificate.kernelBoundary_supports_structuralRecursion
    (cert : InductiveElaborationCertificate) :
    Mettapedia.Languages.MeTTa.InductiveKernelJudgmentKind.structuralRecursion ∈
      cert.kernelBoundary.supportedJudgments := by
  exact cert.bridge.proofKernel.kernelBoundary_supports_structuralRecursion

theorem InductiveElaborationCertificate.kernelBoundary_positivity_holds
    (cert : InductiveElaborationCertificate) :
    cert.kernelInterface.hookInterface.family.strictlyPositive = true := by
  exact cert.bridge.proofKernel.kernelBoundary_positivity_holds

def certifyInductiveOverlap
    (bridge : Mettapedia.Languages.MeTTa.InductiveOverlapBridge) :
    InductiveElaborationCertificate :=
  { bridge := bridge
    overlapClass := bridge.proofKernel.proofInterface.overlapClass
    overlap_eq := rfl }

/-- Certificate for the first structural-fixpoint objects admitted into the
elaborated middle layer.

As with starter inductives, this remains deliberately modest:
- proof-side overlap is currently `artifactOnly`
- runtime-side compatibility is currently only at the artifact/query level
- no actual fixpoint implementation in `MeTTa-Pure` is claimed here
-/
structure FixpointElaborationCertificate where
  bridge : Mettapedia.Languages.MeTTa.FixpointOverlapBridge
  overlapClass : OverlapClass
  overlap_eq : overlapClass = bridge.proofInterface.overlapClass

def FixpointElaborationCertificate.artifact
    (cert : FixpointElaborationCertificate) : SharedArtifact :=
  cert.bridge.runtimeCandidate.artifact

def FixpointElaborationCertificate.kernelInterface
    (cert : FixpointElaborationCertificate) :
    Mettapedia.Languages.MeTTa.StructuralFixpointKernelInterface :=
  cert.bridge.runtimeCandidate.kernelInterface

def FixpointElaborationCertificate.functionName
    (cert : FixpointElaborationCertificate) : String :=
  cert.bridge.runtimeCandidate.kernelInterface.hook.functionName

theorem FixpointElaborationCertificate.functionName_eq
    (cert : FixpointElaborationCertificate) :
    cert.functionName = cert.bridge.runtimeCandidate.kernelInterface.hook.functionName := rfl

def certifyFixpointOverlap
    (bridge : Mettapedia.Languages.MeTTa.FixpointOverlapBridge) :
    FixpointElaborationCertificate :=
  { bridge := bridge
    overlapClass := bridge.proofInterface.overlapClass
    overlap_eq := rfl }

/-- The first explicit elaborated-core object. -/
inductive ElaboratedNode where
  | pureNode (cert : PureCertificate)
  | coreTypedNode (cert : CoreTypedCertificate)
  | inductiveNode (cert : InductiveElaborationCertificate)
  | fixpointNode (cert : FixpointElaborationCertificate)
  | runtimeNode (cert : RuntimeCertificate)
  | oracleNode (cert : OracleCertificate)
  | metaNode (cert : MetaCertificate)

def ElaboratedNode.region : ElaboratedNode → ElaboratedRegion
  | ElaboratedNode.pureNode _ => ElaboratedRegion.pureKernelRegion
  | ElaboratedNode.coreTypedNode _ => ElaboratedRegion.pureKernelRegion
  | ElaboratedNode.inductiveNode _ => ElaboratedRegion.pureKernelRegion
  | ElaboratedNode.fixpointNode _ => ElaboratedRegion.pureKernelRegion
  | ElaboratedNode.runtimeNode _ => ElaboratedRegion.runtimeExecRegion
  | ElaboratedNode.oracleNode _ => ElaboratedRegion.oracleRegion
  | ElaboratedNode.metaNode _ => ElaboratedRegion.metaRegion

def ElaboratedNode.artifact : ElaboratedNode → SharedArtifact
  | ElaboratedNode.pureNode cert => cert.artifact
  | ElaboratedNode.coreTypedNode cert => cert.artifact
  | ElaboratedNode.inductiveNode cert => cert.artifact
  | ElaboratedNode.fixpointNode cert => cert.artifact
  | ElaboratedNode.runtimeNode cert => cert.artifact
  | ElaboratedNode.oracleNode cert => cert.artifact
  | ElaboratedNode.metaNode cert => cert.artifact

/-- Tiny surface language for the first elaboration proof-of-concept.

This is deliberately smaller than full MeTTa. The purpose is to make the
downstream split explicit before committing to a richer elaborator.
-/
inductive SurfaceNode where
  | surfacePureClosed (term : SurfacePureTm 0)
  | coreTypedAtom (surface : SurfaceCoreTypedAtom)
  | starterInductive (bridge : Mettapedia.Languages.MeTTa.InductiveOverlapBridge)
  | starterFixpoint (bridge : Mettapedia.Languages.MeTTa.FixpointOverlapBridge)
  | heRuntimeRule (pattern : Pattern)
  | heRuntimeQuery (pattern : Pattern)
  | pettaRuntimeRule (pattern : Pattern)
  | pettaRuntimeQuery (pattern : Pattern)
  | fullLegacyRuntime (pattern : Pattern)
  | oracleCall
      (dialect : MeTTaDialectProfile)
      (opName : String)
      (resultDescriptor : String)
      (args : List Pattern)
  | metaQuoted (description : String) (pattern : Pattern)

/-- Proof-of-concept elaborator from a tiny surface language into the first
explicit elaborated MeTTa-Core. -/
noncomputable def elaborate : SurfaceNode → ElaboratedNode
  | SurfaceNode.surfacePureClosed term =>
      ElaboratedNode.pureNode (certifySurfacePure term).pure
  | SurfaceNode.coreTypedAtom surface =>
      ElaboratedNode.coreTypedNode (certifySurfaceCoreTypedAtom surface)
  | SurfaceNode.starterInductive bridge =>
      ElaboratedNode.inductiveNode (certifyInductiveOverlap bridge)
  | SurfaceNode.starterFixpoint bridge =>
      ElaboratedNode.fixpointNode (certifyFixpointOverlap bridge)
  | SurfaceNode.heRuntimeRule pattern =>
      ElaboratedNode.runtimeNode {
        dialect := heDialectProfile
        spec := heRuntimeSpec
        lowering := RuntimeLowering.exec morkRuntimeExec0
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SurfaceNode.heRuntimeQuery pattern =>
      ElaboratedNode.runtimeNode {
        dialect := heDialectProfile
        spec := heRuntimeSpec
        lowering := RuntimeLowering.query morkRuntimeQueryExec0
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SurfaceNode.pettaRuntimeRule pattern =>
      ElaboratedNode.runtimeNode {
        dialect := pettaDialectProfile
        spec := pettaRuntimeSpec
        lowering := RuntimeLowering.exec morkRuntimeExec0
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SurfaceNode.pettaRuntimeQuery pattern =>
      ElaboratedNode.runtimeNode {
        dialect := pettaDialectProfile
        spec := pettaRuntimeSpec
        lowering := RuntimeLowering.query morkRuntimeQueryExec0
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SurfaceNode.fullLegacyRuntime pattern =>
      ElaboratedNode.runtimeNode {
        dialect := fullLegacyDialectProfile
        spec := fullLegacyRuntimeSpec
        lowering := RuntimeLowering.auditOnly
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SurfaceNode.oracleCall dialect opName resultDescriptor args =>
      ElaboratedNode.oracleNode {
        dialect := dialect
        opName := opName
        resultDescriptor := resultDescriptor
        args := args
        artifact := ⟨Pattern.apply opName args⟩
      }
  | SurfaceNode.metaQuoted description pattern =>
      ElaboratedNode.metaNode {
        description := description
        artifact := ⟨pattern⟩
      }

theorem elaborate_surfacePureClosed_region (term : SurfacePureTm 0) :
    ElaboratedNode.region (elaborate (SurfaceNode.surfacePureClosed term)) =
      ElaboratedRegion.pureKernelRegion := rfl

theorem elaborate_coreTypedAtom_region (surface : SurfaceCoreTypedAtom) :
    ElaboratedNode.region (elaborate (SurfaceNode.coreTypedAtom surface)) =
      ElaboratedRegion.pureKernelRegion := rfl

theorem elaborate_starterInductive_region
    (bridge : Mettapedia.Languages.MeTTa.InductiveOverlapBridge) :
    ElaboratedNode.region (elaborate (SurfaceNode.starterInductive bridge)) =
      ElaboratedRegion.pureKernelRegion := rfl

theorem elaborate_starterFixpoint_region
    (bridge : Mettapedia.Languages.MeTTa.FixpointOverlapBridge) :
    ElaboratedNode.region (elaborate (SurfaceNode.starterFixpoint bridge)) =
      ElaboratedRegion.pureKernelRegion := rfl

theorem elaborate_heRuntimeRule_region (pattern : Pattern) :
    ElaboratedNode.region (elaborate (SurfaceNode.heRuntimeRule pattern)) =
      ElaboratedRegion.runtimeExecRegion := rfl

theorem elaborate_pettaRuntimeQuery_region (pattern : Pattern) :
    ElaboratedNode.region (elaborate (SurfaceNode.pettaRuntimeQuery pattern)) =
      ElaboratedRegion.runtimeExecRegion := rfl

theorem elaborate_oracleCall_region
    (dialect : MeTTaDialectProfile) (opName resultDescriptor : String)
    (args : List Pattern) :
    ElaboratedNode.region
        (elaborate (SurfaceNode.oracleCall dialect opName resultDescriptor args)) =
      ElaboratedRegion.oracleRegion := rfl

theorem elaborate_metaQuoted_region
    (description : String) (pattern : Pattern) :
    ElaboratedNode.region (elaborate (SurfaceNode.metaQuoted description pattern)) =
      ElaboratedRegion.metaRegion := rfl

theorem elaborate_surfacePureClosed_artifact
    (term : SurfacePureTm 0) :
    (ElaboratedNode.artifact (elaborate (SurfaceNode.surfacePureClosed term))).pattern =
      term.toClosedPattern := rfl

theorem elaborate_coreTypedAtom_artifact
    (surface : SurfaceCoreTypedAtom) :
    (ElaboratedNode.artifact (elaborate (SurfaceNode.coreTypedAtom surface))).pattern =
      surface.pattern := rfl

theorem elaborate_starterInductive_artifact
    (bridge : Mettapedia.Languages.MeTTa.InductiveOverlapBridge) :
    ElaboratedNode.artifact (elaborate (SurfaceNode.starterInductive bridge)) =
      bridge.runtimeCandidate.artifact := rfl

theorem elaborate_starterFixpoint_artifact
    (bridge : Mettapedia.Languages.MeTTa.FixpointOverlapBridge) :
    ElaboratedNode.artifact (elaborate (SurfaceNode.starterFixpoint bridge)) =
      bridge.runtimeCandidate.artifact := rfl

theorem elaborate_starterInductive_familyName
    (bridge : Mettapedia.Languages.MeTTa.InductiveOverlapBridge) :
    match elaborate (SurfaceNode.starterInductive bridge) with
    | ElaboratedNode.inductiveNode cert => cert.familyName = bridge.runtimeCandidate.family.name
    | _ => False := by
  simpa [elaborate, certifyInductiveOverlap] using
    (certifyInductiveOverlap bridge).familyName_eq

theorem elaborate_starterFixpoint_functionName
    (bridge : Mettapedia.Languages.MeTTa.FixpointOverlapBridge) :
    match elaborate (SurfaceNode.starterFixpoint bridge) with
    | ElaboratedNode.fixpointNode cert =>
        cert.functionName = bridge.runtimeCandidate.kernelInterface.hook.functionName
    | _ => False := by
  simp [elaborate, certifyFixpointOverlap, FixpointElaborationCertificate.functionName]

theorem elaborate_surfacePureClosed_term
    (term : SurfacePureTm 0) :
    match elaborate (SurfaceNode.surfacePureClosed term) with
    | ElaboratedNode.pureNode cert => cert.term = term.toPureTm
    | _ => False := by
  simp [elaborate, certifySurfacePure]

theorem elaborate_surfacePureClosed_quoteAgreement
    (term : SurfacePureTm 0) :
    (ElaboratedNode.artifact (elaborate (SurfaceNode.surfacePureClosed term))).pattern =
      Mettapedia.Languages.MeTTa.PureKernel.PatternBridge.quoteClosedTm term.toPureTm := by
  simpa [elaborate, certifySurfacePure] using term.toClosedPattern_eq_quoteClosedTm

theorem elaborate_surfacePureClosed_abcSurface
    (term : SurfacePureTm 0) :
    match elaborate (SurfaceNode.surfacePureClosed term) with
    | ElaboratedNode.pureNode cert => cert.abcSurface = defaultPureClosedABCSurface
    | _ => False := by
  simp [elaborate]

theorem elaborate_heRuntimeRule_backend
    (pattern : Pattern) :
    match elaborate (SurfaceNode.heRuntimeRule pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering = "MORK/MM2"
    | _ => False := by
  simp [elaborate, RuntimeLowering.backendName, morkRuntimeExec0_backendName]

theorem elaborate_pettaRuntimeRule_backend
    (pattern : Pattern) :
    match elaborate (SurfaceNode.pettaRuntimeRule pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering = "MORK/MM2"
    | _ => False := by
  simp [elaborate, RuntimeLowering.backendName, morkRuntimeExec0_backendName]

theorem elaborate_fullLegacyRuntime_auditOnly
    (pattern : Pattern) :
    match elaborate (SurfaceNode.fullLegacyRuntime pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering = "audit-only"
    | _ => False := by
  simp [elaborate, RuntimeLowering.backendName]

/-- Proof-of-concept certificate that a closed Pure term already has a shared
artifact view at the MeTTaIL substrate. -/
noncomputable def pureArtifactCertificate (term : SurfacePureTm 0) : SharedArtifact :=
  ElaboratedNode.artifact (elaborate (SurfaceNode.surfacePureClosed term))

theorem certifySurfaceCoreTypedAtom_overlapClass (surface : SurfaceCoreTypedAtom) :
    (certifySurfaceCoreTypedAtom surface).overlapClass = OverlapClass.artifactOnly := rfl

theorem certifySurfaceCoreTypedAtom_overlapName (surface : SurfaceCoreTypedAtom) :
    OverlapClass.name (certifySurfaceCoreTypedAtom surface).overlapClass = "artifact-only" := rfl

theorem surfaceCoreTypedAtom_overlap_is_not_directExec
    (surface : SurfaceCoreTypedAtom) :
    (certifySurfaceCoreTypedAtom surface).overlapClass ≠
      OverlapClass.directExec morkRuntimeExec0 := by
  simp [certifySurfaceCoreTypedAtom]

theorem starterInductive_overlap_eq_proofOverlap
    (bridge : Mettapedia.Languages.MeTTa.InductiveOverlapBridge) :
    (certifyInductiveOverlap bridge).overlapClass =
      bridge.proofKernel.proofInterface.overlapClass := rfl

theorem starterFixpoint_overlap_eq_proofOverlap
    (bridge : Mettapedia.Languages.MeTTa.FixpointOverlapBridge) :
    (certifyFixpointOverlap bridge).overlapClass =
      bridge.proofInterface.overlapClass := rfl

theorem unitStarterInductive_overlap_is_artifactOnly :
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.unitOverlapBridge).overlapClass =
      OverlapClass.artifactOnly := rfl

theorem boolTrueStarterInductive_overlap_is_artifactOnly :
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.boolTrueOverlapBridge).overlapClass =
      OverlapClass.artifactOnly := rfl

theorem natZeroStarterInductive_overlap_is_artifactOnly :
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.natZeroOverlapBridge).overlapClass =
      OverlapClass.artifactOnly := rfl

theorem unitStarterInductive_supports_familyDeclaration :
    Mettapedia.Languages.MeTTa.InductiveKernelJudgmentKind.familyDeclaration ∈
      (certifyInductiveOverlap Mettapedia.Languages.MeTTa.unitOverlapBridge).kernelBoundary.supportedJudgments := by
  exact
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.unitOverlapBridge).kernelBoundary_supports_familyDeclaration

theorem boolTrueStarterInductive_supports_familyDeclaration :
    Mettapedia.Languages.MeTTa.InductiveKernelJudgmentKind.familyDeclaration ∈
      (certifyInductiveOverlap Mettapedia.Languages.MeTTa.boolTrueOverlapBridge).kernelBoundary.supportedJudgments := by
  exact
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.boolTrueOverlapBridge).kernelBoundary_supports_familyDeclaration

theorem natZeroStarterInductive_supports_familyDeclaration :
    Mettapedia.Languages.MeTTa.InductiveKernelJudgmentKind.familyDeclaration ∈
      (certifyInductiveOverlap Mettapedia.Languages.MeTTa.natZeroOverlapBridge).kernelBoundary.supportedJudgments := by
  exact
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.natZeroOverlapBridge).kernelBoundary_supports_familyDeclaration

theorem unitStarterInductive_supports_generatedRecursor :
    Mettapedia.Languages.MeTTa.InductiveKernelJudgmentKind.generatedRecursor ∈
      (certifyInductiveOverlap Mettapedia.Languages.MeTTa.unitOverlapBridge).kernelBoundary.supportedJudgments := by
  exact
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.unitOverlapBridge).kernelBoundary_supports_generatedRecursor

theorem boolTrueStarterInductive_supports_generatedRecursor :
    Mettapedia.Languages.MeTTa.InductiveKernelJudgmentKind.generatedRecursor ∈
      (certifyInductiveOverlap Mettapedia.Languages.MeTTa.boolTrueOverlapBridge).kernelBoundary.supportedJudgments := by
  exact
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.boolTrueOverlapBridge).kernelBoundary_supports_generatedRecursor

theorem natZeroStarterInductive_supports_generatedRecursor :
    Mettapedia.Languages.MeTTa.InductiveKernelJudgmentKind.generatedRecursor ∈
      (certifyInductiveOverlap Mettapedia.Languages.MeTTa.natZeroOverlapBridge).kernelBoundary.supportedJudgments := by
  exact
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.natZeroOverlapBridge).kernelBoundary_supports_generatedRecursor

theorem natIsZeroStarterFixpoint_overlap_is_artifactOnly :
    (certifyFixpointOverlap Mettapedia.Languages.MeTTa.natIsZeroFixpointOverlapBridge).overlapClass =
      OverlapClass.artifactOnly := rfl

theorem natPredStarterFixpoint_overlap_is_artifactOnly :
    (certifyFixpointOverlap Mettapedia.Languages.MeTTa.natPredFixpointOverlapBridge).overlapClass =
      OverlapClass.artifactOnly := rfl

theorem unitStarterInductive_queryCompatible :
    let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
      (ElaboratedNode.artifact
        (elaborate (SurfaceNode.starterInductive Mettapedia.Languages.MeTTa.unitOverlapBridge))).pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [elaborate_starterInductive_artifact] using
    Mettapedia.Languages.MeTTa.unitDualTargetCandidate_queryCompatible

theorem boolTrueStarterInductive_queryCompatible :
    let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
      (ElaboratedNode.artifact
        (elaborate (SurfaceNode.starterInductive Mettapedia.Languages.MeTTa.boolTrueOverlapBridge))).pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [elaborate_starterInductive_artifact] using
    Mettapedia.Languages.MeTTa.boolTrueDualTargetCandidate_queryCompatible

theorem natZeroStarterInductive_queryCompatible :
    let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
      (ElaboratedNode.artifact
        (elaborate (SurfaceNode.starterInductive Mettapedia.Languages.MeTTa.natZeroOverlapBridge))).pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [elaborate_starterInductive_artifact] using
    Mettapedia.Languages.MeTTa.natZeroDualTargetCandidate_queryCompatible

theorem natIsZeroStarterFixpoint_queryCompatible :
    let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
      (ElaboratedNode.artifact
        (elaborate (SurfaceNode.starterFixpoint Mettapedia.Languages.MeTTa.natIsZeroFixpointOverlapBridge))).pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [elaborate_starterFixpoint_artifact] using
    Mettapedia.Languages.MeTTa.natIsZeroFixpoint_queryCompatible

theorem natPredStarterFixpoint_queryCompatible :
    let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
      (ElaboratedNode.artifact
        (elaborate (SurfaceNode.starterFixpoint Mettapedia.Languages.MeTTa.natPredFixpointOverlapBridge))).pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [elaborate_starterFixpoint_artifact] using
    Mettapedia.Languages.MeTTa.natPredFixpoint_queryCompatible

theorem unitStarterInductive_refines_pureCheckingBoundary :
    (ElaboratedNode.inductiveNode
      (certifyInductiveOverlap Mettapedia.Languages.MeTTa.unitOverlapBridge)).region =
      pureCheckingBoundary.region ∧
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.unitOverlapBridge).overlapClass =
      pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

theorem boolTrueStarterInductive_refines_pureCheckingBoundary :
    (ElaboratedNode.inductiveNode
      (certifyInductiveOverlap Mettapedia.Languages.MeTTa.boolTrueOverlapBridge)).region =
      pureCheckingBoundary.region ∧
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.boolTrueOverlapBridge).overlapClass =
      pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

theorem natZeroStarterInductive_refines_pureCheckingBoundary :
    (ElaboratedNode.inductiveNode
      (certifyInductiveOverlap Mettapedia.Languages.MeTTa.natZeroOverlapBridge)).region =
      pureCheckingBoundary.region ∧
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.natZeroOverlapBridge).overlapClass =
      pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

theorem natIsZeroStarterFixpoint_refines_pureCheckingBoundary :
    (ElaboratedNode.fixpointNode
      (certifyFixpointOverlap Mettapedia.Languages.MeTTa.natIsZeroFixpointOverlapBridge)).region =
      pureCheckingBoundary.region ∧
    (certifyFixpointOverlap Mettapedia.Languages.MeTTa.natIsZeroFixpointOverlapBridge).overlapClass =
      pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

theorem natPredStarterFixpoint_refines_pureCheckingBoundary :
    (ElaboratedNode.fixpointNode
      (certifyFixpointOverlap Mettapedia.Languages.MeTTa.natPredFixpointOverlapBridge)).region =
      pureCheckingBoundary.region ∧
    (certifyFixpointOverlap Mettapedia.Languages.MeTTa.natPredFixpointOverlapBridge).overlapClass =
      pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

theorem unitStarterInductive_overlap_is_artifactOnly_but_queryCompatible :
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.unitOverlapBridge).overlapClass =
      OverlapClass.artifactOnly ∧
    (let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
      (ElaboratedNode.artifact
        (elaborate (SurfaceNode.starterInductive Mettapedia.Languages.MeTTa.unitOverlapBridge))).pattern;
      ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) := by
  constructor
  · rfl
  · simpa [elaborate_starterInductive_artifact] using
      Mettapedia.Languages.MeTTa.unitDualTargetCandidate_queryCompatible

theorem boolTrueStarterInductive_overlap_is_artifactOnly_but_queryCompatible :
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.boolTrueOverlapBridge).overlapClass =
      OverlapClass.artifactOnly ∧
    (let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
      (ElaboratedNode.artifact
        (elaborate (SurfaceNode.starterInductive Mettapedia.Languages.MeTTa.boolTrueOverlapBridge))).pattern;
      ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) := by
  constructor
  · rfl
  · simpa [elaborate_starterInductive_artifact] using
      Mettapedia.Languages.MeTTa.boolTrueDualTargetCandidate_queryCompatible

theorem natZeroStarterInductive_overlap_is_artifactOnly_but_queryCompatible :
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.natZeroOverlapBridge).overlapClass =
      OverlapClass.artifactOnly ∧
    (let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
      (ElaboratedNode.artifact
        (elaborate (SurfaceNode.starterInductive Mettapedia.Languages.MeTTa.natZeroOverlapBridge))).pattern;
      ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) := by
  constructor
  · rfl
  · simpa [elaborate_starterInductive_artifact] using
      Mettapedia.Languages.MeTTa.natZeroDualTargetCandidate_queryCompatible

theorem unitStarterInductive_refines_kernelExtension :
    let ext := Mettapedia.Languages.MeTTa.unitKernelExtension
    (ElaboratedNode.inductiveNode
      (certifyInductiveOverlap Mettapedia.Languages.MeTTa.unitOverlapBridge)).region =
      ext.checkingBoundary.region ∧
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.unitOverlapBridge).overlapClass =
      ext.checkingBoundary.overlapClass := by
  constructor <;> rfl

theorem boolTrueStarterInductive_refines_kernelExtension :
    let ext := Mettapedia.Languages.MeTTa.boolKernelExtension
    (ElaboratedNode.inductiveNode
      (certifyInductiveOverlap Mettapedia.Languages.MeTTa.boolTrueOverlapBridge)).region =
      ext.checkingBoundary.region ∧
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.boolTrueOverlapBridge).overlapClass =
      ext.checkingBoundary.overlapClass := by
  constructor <;> rfl

theorem natZeroStarterInductive_refines_kernelExtension :
    let ext := Mettapedia.Languages.MeTTa.natKernelExtension
    (ElaboratedNode.inductiveNode
      (certifyInductiveOverlap Mettapedia.Languages.MeTTa.natZeroOverlapBridge)).region =
      ext.checkingBoundary.region ∧
    (certifyInductiveOverlap Mettapedia.Languages.MeTTa.natZeroOverlapBridge).overlapClass =
      ext.checkingBoundary.overlapClass := by
  constructor <;> rfl

theorem unitStarterInductive_extension_has_queryCompatibleCtor :
    ∃ ctor, ctor ∈ Mettapedia.Languages.MeTTa.unitKernelExtension.declaration.ctors ∧
      ctor.name = "unit" ∧ ctor.argCount = 0 ∧
      (let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
        (ElaboratedNode.artifact
          (elaborate (SurfaceNode.starterInductive Mettapedia.Languages.MeTTa.unitOverlapBridge))).pattern
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) := by
  simpa [elaborate_starterInductive_artifact] using
    Mettapedia.Languages.MeTTa.unitKernelExtension_has_queryCompatibleCtor

theorem boolTrueStarterInductive_extension_has_queryCompatibleCtor :
    ∃ ctor, ctor ∈ Mettapedia.Languages.MeTTa.boolKernelExtension.declaration.ctors ∧
      ctor.name = "true" ∧ ctor.argCount = 0 ∧
      (let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
        (ElaboratedNode.artifact
          (elaborate (SurfaceNode.starterInductive Mettapedia.Languages.MeTTa.boolTrueOverlapBridge))).pattern
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) := by
  simpa [elaborate_starterInductive_artifact] using
    Mettapedia.Languages.MeTTa.boolKernelExtension_has_queryCompatibleCtor

theorem natZeroStarterInductive_extension_has_queryCompatibleCtor :
    ∃ ctor, ctor ∈ Mettapedia.Languages.MeTTa.natKernelExtension.declaration.ctors ∧
      ctor.name = "zero" ∧ ctor.argCount = 0 ∧
      (let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
        (ElaboratedNode.artifact
          (elaborate (SurfaceNode.starterInductive Mettapedia.Languages.MeTTa.natZeroOverlapBridge))).pattern
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) := by
  simpa [elaborate_starterInductive_artifact] using
    Mettapedia.Languages.MeTTa.natKernelExtension_has_queryCompatibleCtor

theorem checkedUnitFamily_refines_kernelExtension :
    Mettapedia.Languages.MeTTa.checkedUnitFamily.extension.declaration.familyName =
      Mettapedia.Languages.MeTTa.unitKernelExtension.declaration.familyName ∧
    Mettapedia.Languages.MeTTa.checkedUnitFamily.extension.declaration.recursorName =
      Mettapedia.Languages.MeTTa.unitKernelExtension.declaration.recursorName := by
  constructor <;> rfl

theorem checkedBoolFamily_refines_kernelExtension :
    Mettapedia.Languages.MeTTa.checkedBoolFamily.extension.declaration.familyName =
      Mettapedia.Languages.MeTTa.boolKernelExtension.declaration.familyName ∧
    Mettapedia.Languages.MeTTa.checkedBoolFamily.extension.declaration.recursorName =
      Mettapedia.Languages.MeTTa.boolKernelExtension.declaration.recursorName := by
  constructor <;> rfl

theorem checkedNatFamily_refines_kernelExtension :
    Mettapedia.Languages.MeTTa.checkedNatFamily.extension.declaration.familyName =
      Mettapedia.Languages.MeTTa.natKernelExtension.declaration.familyName ∧
    Mettapedia.Languages.MeTTa.checkedNatFamily.extension.declaration.recursorName =
      Mettapedia.Languages.MeTTa.natKernelExtension.declaration.recursorName := by
  constructor <;> rfl

theorem checkedUnitFamily_overlap_is_artifactOnly :
    Mettapedia.Languages.MeTTa.checkedUnitFamily.service.overlapClass =
      OverlapClass.artifactOnly := by
  simp [Mettapedia.Languages.MeTTa.checkedUnitFamily,
    Mettapedia.Languages.MeTTa.checkOrdinaryFamilyCanonical,
    Mettapedia.Languages.MeTTa.PureCheckingBoundary.checkOrdinaryFamily,
    pureCheckingBoundary]

theorem checkedBoolFamily_overlap_is_artifactOnly :
    Mettapedia.Languages.MeTTa.checkedBoolFamily.service.overlapClass =
      OverlapClass.artifactOnly := by
  simp [Mettapedia.Languages.MeTTa.checkedBoolFamily,
    Mettapedia.Languages.MeTTa.checkOrdinaryFamilyCanonical,
    Mettapedia.Languages.MeTTa.PureCheckingBoundary.checkOrdinaryFamily,
    pureCheckingBoundary]

theorem checkedNatFamily_overlap_is_artifactOnly :
    Mettapedia.Languages.MeTTa.checkedNatFamily.service.overlapClass =
      OverlapClass.artifactOnly := by
  simp [Mettapedia.Languages.MeTTa.checkedNatFamily,
    Mettapedia.Languages.MeTTa.checkOrdinaryFamilyCanonical,
    Mettapedia.Languages.MeTTa.PureCheckingBoundary.checkOrdinaryFamily,
    pureCheckingBoundary]

theorem checkedNatIsZeroFixpoint_refines_pureCheckingBoundary :
    Mettapedia.Languages.MeTTa.checkedNatIsZeroFixpoint.region =
      pureCheckingBoundary.region ∧
    Mettapedia.Languages.MeTTa.checkedNatIsZeroFixpoint.overlapClass =
      pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

theorem checkedNatPredFixpoint_refines_pureCheckingBoundary :
    Mettapedia.Languages.MeTTa.checkedNatPredFixpoint.region =
      pureCheckingBoundary.region ∧
    Mettapedia.Languages.MeTTa.checkedNatPredFixpoint.overlapClass =
      pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

theorem checkedNatIsZeroFixpoint_recursorName :
    Mettapedia.Languages.MeTTa.checkedNatIsZeroFixpoint.iface.hook.recursorContractStub =
      "Nat.rec" := by
  exact Mettapedia.Languages.MeTTa.checkedNatIsZeroFixpoint_recursor

theorem checkedNatPredFixpoint_recursorName :
    Mettapedia.Languages.MeTTa.checkedNatPredFixpoint.iface.hook.recursorContractStub =
      "Nat.rec" := by
  exact Mettapedia.Languages.MeTTa.checkedNatPredFixpoint_recursor

/-- Language-level summary imported from `PureRuntimeFrontier`: the current
`mettaPure` rewrite system still does not satisfy the direct `R_exec₀`
source-rule bridge hypotheses. -/
theorem mettaPure_language_frontier_is_not_directExec0
    (r : RewriteRule)
    (hr : r ∈ Mettapedia.Languages.MeTTa.Pure.Core.mettaPure.rewrites) :
    ¬ ∃ x, r.left = .fvar x ∧
      Mettapedia.Languages.ProcessCalculi.MORK.morkTranslatable r.right = true :=
  PureRuntimeFrontier.no_mettaPure_rewrite_fits_direct_runtimeExec0_source_bridge r hr

/-- Proof-of-concept certificate that HE runtime rules and PeTTa runtime rules
already target the same theoremic backend seam, even though they remain
different dialects. -/
theorem runtimeBackendAgreement
    (hePattern pettaPattern : Pattern) :
    match elaborate (SurfaceNode.heRuntimeRule hePattern),
          elaborate (SurfaceNode.pettaRuntimeRule pettaPattern) with
    | ElaboratedNode.runtimeNode heCert, ElaboratedNode.runtimeNode pettaCert =>
        RuntimeLowering.backendName heCert.lowering =
          RuntimeLowering.backendName pettaCert.lowering
    | _, _ => False := by
  simp [elaborate, RuntimeLowering.backendName]

end Mettapedia.Languages.MeTTa.ElaboratedCore
