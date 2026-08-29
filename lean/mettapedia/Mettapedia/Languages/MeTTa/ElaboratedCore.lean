import Mettapedia.Languages.MeTTa.ElaboratedCoreBase
import Mettapedia.Languages.MeTTa.PureCertificateFragment
import Mettapedia.Languages.MeTTa.PureCheckingService
import Mettapedia.Languages.MeTTa.RuntimeExec
import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mettapedia.Languages.MeTTa.PureRuntimeFrontier

/-!
# Elaborated MeTTa-Core

Classification layer sitting above `IntrinsicPure` and `RuntimeExec`.

Current regions:

- `pureKernelRegion`: trusted typed fragment routed to `IntrinsicPure`
- `runtimeExecRegion`: effectful/runtime fragment routed to `RuntimeSpec` and
  an execution/query seam
- `oracleRegion`: grounded/FFI/oracle boundary kept explicit
- `metaRegion`: proof/elaboration-time reflection layer

In the live default path, the trusted `IntrinsicPure` is only the small
Pi/Sigma/Id/universe waist plus ordinary families admitted through the general
`DeclSpec`/`DeclEnv` mechanism.
-/

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.DialectProfile
open Mettapedia.Languages.MeTTa.RuntimeSpec
open Mettapedia.Languages.MeTTa.RuntimeExec
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.PatternBridge
open Mettapedia.OSLF.MeTTaIL.Syntax

abbrev CoreAtom := Mettapedia.Languages.MeTTa.OSLFCore.Atom
abbrev CoreAtomspace := Mettapedia.Languages.MeTTa.OSLFCore.Atomspace
abbrev CoreGroundedValue := Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue

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

/-- Small typed MeTTa-Core source fragment whose atoms already have a shared
artifact view through `Core.Bridge.atomToPattern`.

This is intentionally weaker than a direct IntrinsicPure compilation target:
- positive example: symbolic atoms, variables, and expression constructors that
  already admit a `Pattern` view
- negative example: grounded atoms do not currently admit such a view and are
  excluded from this fragment
-/
structure CoreTypedSyntaxAtom where
  space : CoreAtomspace
  atom : CoreAtom
  ty : CoreAtom
  typed : Mettapedia.Languages.MeTTa.OSLFCore.HasType space atom ty
  pattern : Pattern
  pattern_eq : atomToPattern atom = some pattern

namespace CoreTypedSyntaxAtom

def toArtifact (sourceAtom : CoreTypedSyntaxAtom) : SharedArtifact :=
  ⟨sourceAtom.pattern⟩

def ofSymbol (space : CoreAtomspace) (s : String) : CoreTypedSyntaxAtom :=
  { space := space
    atom := .symbol s
    ty := .symbol "Symbol"
    typed := Mettapedia.Languages.MeTTa.OSLFCore.HasType.intrinsicSymbol s
    pattern := .apply s []
    pattern_eq := by simp [atomToPattern] }

def ofVariable (space : CoreAtomspace) (v : String) : CoreTypedSyntaxAtom :=
  { space := space
    atom := .var v
    ty := .symbol "Variable"
    typed := Mettapedia.Languages.MeTTa.OSLFCore.HasType.intrinsicVariable v
    pattern := .fvar v
    pattern_eq := by simp [atomToPattern] }

def ofAnnotated
    (space : CoreAtomspace)
    (atom ty : CoreAtom) (pattern : Pattern)
    (hpattern : atomToPattern atom = some pattern)
    (hannot : Mettapedia.Languages.MeTTa.OSLFCore.typeAnnotation atom ty ∈ space.atoms) :
    CoreTypedSyntaxAtom :=
  { space := space
    atom := atom
    ty := ty
    typed := Mettapedia.Languages.MeTTa.OSLFCore.annotation_gives_type space atom ty hannot
    pattern := pattern
    pattern_eq := hpattern }

theorem ofSymbol_pattern (space : CoreAtomspace) (s : String) :
    (ofSymbol space s).pattern = .apply s [] := rfl

theorem ofVariable_pattern (space : CoreAtomspace) (v : String) :
    (ofVariable space v).pattern = .fvar v := rfl

theorem ofSymbol_ty (space : CoreAtomspace) (s : String) :
    (ofSymbol space s).ty = .symbol "Symbol" := rfl

theorem ofVariable_ty (space : CoreAtomspace) (v : String) :
    (ofVariable space v).ty = .symbol "Variable" := rfl

theorem ofAnnotated_atom (space : CoreAtomspace) (a ty : CoreAtom)
    (p : Pattern) (hp : atomToPattern a = some p)
    (ha : Mettapedia.Languages.MeTTa.OSLFCore.typeAnnotation a ty ∈ space.atoms) :
    (ofAnnotated space a ty p hp ha).atom = a := rfl

/-- The bridge from every `CoreTypedSyntaxAtom` to a `Pattern` is always
determined by `Core.Bridge.atomToPattern`. -/
theorem pattern_from_bridge (sourceAtom : CoreTypedSyntaxAtom) :
    atomToPattern sourceAtom.atom = some sourceAtom.pattern :=
  sourceAtom.pattern_eq

theorem toArtifact_pattern (sourceAtom : CoreTypedSyntaxAtom) :
    sourceAtom.toArtifact.pattern = sourceAtom.pattern := rfl

end CoreTypedSyntaxAtom

/-- Certificate for a typed MeTTa-Core atom that already has both a type
judgment and a shared artifact view. -/
structure CoreTypedCertificate where
  sourceAtom : CoreTypedSyntaxAtom
  overlapClass : OverlapClass
  artifact : SharedArtifact
  artifact_eq : artifact.pattern = sourceAtom.pattern

def CoreTypedCertificate.backendName (_ : CoreTypedCertificate) : String :=
  "CoreTypes+Artifact"

def certifyCoreTypedSyntaxAtom (sourceAtom : CoreTypedSyntaxAtom) : CoreTypedCertificate :=
  { sourceAtom := sourceAtom
    overlapClass := OverlapClass.artifactOnly
    artifact := sourceAtom.toArtifact
    artifact_eq := rfl }

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

/-- The explicit elaborated-core object. -/
inductive ElaboratedNode where
  | pureNode (cert : PureCertificate)
  | coreTypedNode (cert : CoreTypedCertificate)
  | runtimeNode (cert : RuntimeCertificate)
  | oracleNode (cert : OracleCertificate)
  | metaNode (cert : MetaCertificate)

def ElaboratedNode.region : ElaboratedNode → ElaboratedRegion
  | ElaboratedNode.pureNode _ => ElaboratedRegion.pureKernelRegion
  | ElaboratedNode.coreTypedNode _ => ElaboratedRegion.pureKernelRegion
  | ElaboratedNode.runtimeNode _ => ElaboratedRegion.runtimeExecRegion
  | ElaboratedNode.oracleNode _ => ElaboratedRegion.oracleRegion
  | ElaboratedNode.metaNode _ => ElaboratedRegion.metaRegion

def ElaboratedNode.artifact : ElaboratedNode → SharedArtifact
  | ElaboratedNode.pureNode cert => cert.artifact
  | ElaboratedNode.coreTypedNode cert => cert.artifact
  | ElaboratedNode.runtimeNode cert => cert.artifact
  | ElaboratedNode.oracleNode cert => cert.artifact
  | ElaboratedNode.metaNode cert => cert.artifact

/-- Source language for elaboration. -/
inductive SyntaxNode where
  | pureClosedSyntax (term : PureSyntaxTerm 0)
  | coreTypedAtom (sourceAtom : CoreTypedSyntaxAtom)
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

/-- Elaborator from source language into the elaborated MeTTa-Core. -/
noncomputable def elaborate : SyntaxNode → ElaboratedNode
  | SyntaxNode.pureClosedSyntax term =>
      ElaboratedNode.pureNode (certifyPureSyntax term).pure
  | SyntaxNode.coreTypedAtom sourceAtom =>
      ElaboratedNode.coreTypedNode (certifyCoreTypedSyntaxAtom sourceAtom)
  | SyntaxNode.heRuntimeRule pattern =>
      ElaboratedNode.runtimeNode {
        dialect := heDialectProfile
        spec := heRuntimeSpec
        lowering := RuntimeLowering.exec morkRuntimeExec0
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SyntaxNode.heRuntimeQuery pattern =>
      ElaboratedNode.runtimeNode {
        dialect := heDialectProfile
        spec := heRuntimeSpec
        lowering := RuntimeLowering.query morkRuntimeQueryExec0
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SyntaxNode.pettaRuntimeRule pattern =>
      ElaboratedNode.runtimeNode {
        dialect := pettaDialectProfile
        spec := pettaRuntimeSpec
        lowering := RuntimeLowering.exec morkRuntimeExec0
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SyntaxNode.pettaRuntimeQuery pattern =>
      ElaboratedNode.runtimeNode {
        dialect := pettaDialectProfile
        spec := pettaRuntimeSpec
        lowering := RuntimeLowering.query morkRuntimeQueryExec0
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SyntaxNode.fullLegacyRuntime pattern =>
      ElaboratedNode.runtimeNode {
        dialect := fullLegacyDialectProfile
        spec := fullLegacyRuntimeSpec
        lowering := RuntimeLowering.auditOnly
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SyntaxNode.oracleCall dialect opName resultDescriptor args =>
      ElaboratedNode.oracleNode {
        dialect := dialect
        opName := opName
        resultDescriptor := resultDescriptor
        args := args
        artifact := ⟨Pattern.apply opName args⟩
      }
  | SyntaxNode.metaQuoted description pattern =>
      ElaboratedNode.metaNode {
        description := description
        artifact := ⟨pattern⟩
      }

theorem elaborate_pureClosedSyntax_region (term : PureSyntaxTerm 0) :
    ElaboratedNode.region (elaborate (SyntaxNode.pureClosedSyntax term)) =
      ElaboratedRegion.pureKernelRegion := rfl

theorem elaborate_coreTypedAtom_region (sourceAtom : CoreTypedSyntaxAtom) :
    ElaboratedNode.region (elaborate (SyntaxNode.coreTypedAtom sourceAtom)) =
      ElaboratedRegion.pureKernelRegion := rfl

theorem elaborate_heRuntimeRule_region (pattern : Pattern) :
    ElaboratedNode.region (elaborate (SyntaxNode.heRuntimeRule pattern)) =
      ElaboratedRegion.runtimeExecRegion := rfl

theorem elaborate_pettaRuntimeQuery_region (pattern : Pattern) :
    ElaboratedNode.region (elaborate (SyntaxNode.pettaRuntimeQuery pattern)) =
      ElaboratedRegion.runtimeExecRegion := rfl

theorem elaborate_oracleCall_region
    (dialect : MeTTaDialectProfile) (opName resultDescriptor : String)
    (args : List Pattern) :
    ElaboratedNode.region
        (elaborate (SyntaxNode.oracleCall dialect opName resultDescriptor args)) =
      ElaboratedRegion.oracleRegion := rfl

theorem elaborate_metaQuoted_region
    (description : String) (pattern : Pattern) :
    ElaboratedNode.region (elaborate (SyntaxNode.metaQuoted description pattern)) =
      ElaboratedRegion.metaRegion := rfl

theorem elaborate_pureClosedSyntax_artifact
    (term : PureSyntaxTerm 0) :
    (ElaboratedNode.artifact (elaborate (SyntaxNode.pureClosedSyntax term))).pattern =
      term.toClosedPattern := rfl

theorem elaborate_coreTypedAtom_artifact
    (sourceAtom : CoreTypedSyntaxAtom) :
    (ElaboratedNode.artifact (elaborate (SyntaxNode.coreTypedAtom sourceAtom))).pattern =
      sourceAtom.pattern := rfl

theorem elaborate_pureClosedSyntax_term
    (term : PureSyntaxTerm 0) :
    match elaborate (SyntaxNode.pureClosedSyntax term) with
    | ElaboratedNode.pureNode cert => cert.term = term.toPureTm
    | _ => False := by
  simp [elaborate, certifyPureSyntax]

theorem elaborate_pureClosedSyntax_quoteAgreement
    (term : PureSyntaxTerm 0) :
    (ElaboratedNode.artifact (elaborate (SyntaxNode.pureClosedSyntax term))).pattern =
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.PatternBridge.quoteClosedTm term.toPureTm := by
  exact term.toClosedPattern_eq_quoteClosedTm

theorem elaborate_heRuntimeRule_backend
    (pattern : Pattern) :
    match elaborate (SyntaxNode.heRuntimeRule pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering = "MORK/MM2"
    | _ => False := by
  simp [elaborate, RuntimeLowering.backendName, morkRuntimeExec0_backendName]

theorem elaborate_pettaRuntimeRule_backend
    (pattern : Pattern) :
    match elaborate (SyntaxNode.pettaRuntimeRule pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering = "MORK/MM2"
    | _ => False := by
  simp [elaborate, RuntimeLowering.backendName, morkRuntimeExec0_backendName]

theorem elaborate_fullLegacyRuntime_auditOnly
    (pattern : Pattern) :
    match elaborate (SyntaxNode.fullLegacyRuntime pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering = "audit-only"
    | _ => False := by
  simp [elaborate, RuntimeLowering.backendName]

/-- Proof-of-concept certificate that a closed Pure term already has a shared
artifact view at the MeTTaIL substrate. -/
noncomputable def pureArtifactCertificate (term : PureSyntaxTerm 0) : SharedArtifact :=
  ElaboratedNode.artifact (elaborate (SyntaxNode.pureClosedSyntax term))

theorem certifyCoreTypedSyntaxAtom_overlapClass (sourceAtom : CoreTypedSyntaxAtom) :
    (certifyCoreTypedSyntaxAtom sourceAtom).overlapClass = OverlapClass.artifactOnly := rfl

theorem certifyCoreTypedSyntaxAtom_overlapName (sourceAtom : CoreTypedSyntaxAtom) :
    OverlapClass.name (certifyCoreTypedSyntaxAtom sourceAtom).overlapClass = "artifact-only" := rfl

theorem coreTypedSyntaxAtom_overlap_is_not_directExec
    (sourceAtom : CoreTypedSyntaxAtom) :
    (certifyCoreTypedSyntaxAtom sourceAtom).overlapClass ≠
      OverlapClass.directExec morkRuntimeExec0 := by
  simp [certifyCoreTypedSyntaxAtom]

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
    match elaborate (SyntaxNode.heRuntimeRule hePattern),
          elaborate (SyntaxNode.pettaRuntimeRule pettaPattern) with
    | ElaboratedNode.runtimeNode heCert, ElaboratedNode.runtimeNode pettaCert =>
        RuntimeLowering.backendName heCert.lowering =
          RuntimeLowering.backendName pettaCert.lowering
    | _, _ => False := by
  simp [elaborate, RuntimeLowering.backendName]

end Mettapedia.Languages.MeTTa.ElaboratedCore
