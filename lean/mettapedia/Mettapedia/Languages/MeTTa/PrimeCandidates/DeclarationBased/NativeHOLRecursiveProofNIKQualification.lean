import Mettapedia.GSLT.LanguageDef.NIK
import Mettapedia.Logic.HOL.Syntax.DecidableEq
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLRecursiveProofOperationalObservation

/-!
# NIK qualification of the recursive HOL-to-native proof route

The semantic target of this service is supported derivability of an exact
closed source HOL formula.  Its intrinsic proof objects retain the submitted
source proof tree and its recursive-compiler support evidence.  The native
kernel decides only whether that proof object is bound to the requested
formula; it does not pretend to validate serialized external evidence.

Acceptance has a separate consequence theorem.  The retained source proof is
compiled by the recursive compiler, and the resulting single native term has
both its formation-sensitive dependent type and its Aczel-trace denotation.
The map-fusion instance then connects that exact output to the independently
defined native execution and OSLF semantic observation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeHOLRecursiveProofNIKQualification

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.GSLT.LanguageDef NIKMetalogic
open NativeHOLTraceRecursiveExtensionalCompilerSemantics

local instance : DecidableEq BaseSort
  | .element, .element | .sequence, .sequence | .count, .count => .isTrue rfl
  | .element, .sequence | .element, .count | .sequence, .element
  | .sequence, .count | .count, .element | .count, .sequence =>
      .isFalse (by intro equal; cases equal)

local instance (type : HOL.Ty BaseSort) : DecidableEq (Symbol type) := by
  intro left right
  cases left <;> cases right <;> exact .isTrue rfl

universe u

abbrev ClosedClaim :=
  HOLLeibnizNativeQualifiedIntegration.Compiler.Formula []

/-- An intrinsic proof object keeps the exact source conclusion, proof tree,
and evidence that every node belongs to the recursive compiler's advertised
fragment. -/
structure IntrinsicProof where
  conclusion : ClosedClaim
  source : HOL.ProofSyntax Symbol [] conclusion
  supported :
    HOLLeibnizNativeQualifiedIntegration.Compiler.supported source = true

/-- Independently stated service meaning: the requested formula has a source
HOL proof that the recursive compiler supports throughout. -/
def sourceTarget : AdmissionObject where
  Carrier := ClosedClaim
  Meaning := fun claim =>
    ∃ source : HOL.ProofSyntax Symbol [] claim,
      HOLLeibnizNativeQualifiedIntegration.Compiler.supported source = true

def intrinsicProofSystem : NativeProofSystem ClosedClaim where
  ProofObject := IntrinsicProof
  Judges := fun proof claim => proof.conclusion = claim

/-- This is an intrinsic binding check, not an external certificate parser.
The recursive support proof is already retained inside `IntrinsicProof`. -/
def intrinsicKernel : NativeProofKernel intrinsicProofSystem where
  decide claim proof := decide (proof.conclusion = claim)
  correct _claim _proof := decide_eq_true_iff

theorem intrinsic_meaning_exact (claim : ClosedClaim) :
    sourceTarget.Meaning claim ↔
      Nonempty (intrinsicProofSystem.ProofFibre claim) := by
  constructor
  · rintro ⟨source, supported⟩
    exact ⟨⟨⟨claim, source, supported⟩, rfl⟩⟩
  · rintro ⟨⟨⟨conclusion, source, supported⟩, bound⟩⟩
    cases bound
    exact ⟨source, supported⟩

def nativeProofService : NIK.Service sourceTarget :=
  .nativeProof intrinsicProofSystem intrinsicKernel intrinsic_meaning_exact

theorem native_accepts_iff_supported_derivable (claim : ClosedClaim) :
    (∃ source : HOL.ProofSyntax Symbol [] claim,
      HOLLeibnizNativeQualifiedIntegration.Compiler.supported source = true) ↔
      ∃ proof, intrinsicKernel.decide claim proof = true :=
  NIK.Service.nativeProof_accepts_iff_meaning
    (target := sourceTarget) intrinsicProofSystem intrinsicKernel
      intrinsic_meaning_exact claim

/-- Accepted intrinsic evidence recovers an ordinary source HOL derivation.
Rejection, conversely, is only rejection of that submitted proof object. -/
theorem native_acceptance_derivation (claim : ClosedClaim)
    (proof : IntrinsicProof)
    (accepted : intrinsicKernel.decide claim proof = true) :
    HOL.ExtDerivation Symbol [] claim := by
  have bound : proof.conclusion = claim :=
    (intrinsicKernel.correct claim proof).mp accepted
  cases bound
  exact proof.source.erase

/-- Acceptance of a retained source proof exposes the connected compiler
theorem for that very proof: one emitted term carries both native dependent
typing and trace denotation of the requested source conclusion. -/
theorem native_acceptance_compiles_connected
    {a : ZFSet.{u}} (claim : ClosedClaim) (proof : IntrinsicProof)
    (accepted : intrinsicKernel.decide claim proof = true) :
    ∃ native code,
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile
          proof.source Fin.elim0 Fin.elim0 = some native ∧
      HOLLeibnizNativeQualifiedIntegration.Compiler.represent claim =
        some code ∧
      Presentation.FormationSensitive.Judgment
          FormationSensitiveHOLExtensionalProfile.rules .nil native
          (FormationSensitiveHOLProofFamily.proof code) ∧
      ProofDenotes a NativeHOLTraceDisplayedTerms.Controls.emptyContext native
        (formulaMeaning claim
          NativeHOLTraceDisplayedTerms.Controls.emptyContext
          (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation
            (a := a))) := by
  have bound : proof.conclusion = claim :=
    (intrinsicKernel.correct claim proof).mp accepted
  cases bound
  exact
    HOLLeibnizNativeQualifiedIntegration.Connected.compile_closed_preserves_typing_and_trace
      proof.source proof.supported

@[simp] theorem native_service_has_no_external_certificate_boundary :
    NIK.Service.hasExternalCertificateBoundary nativeProofService = false :=
  rfl

namespace Controls

open HOLLeibnizNativeQualifiedHOTGIntegration
open NativeHOLRecursiveProofOperationalObservation
open NativeHOLRecursiveProofOperationalObservation.Controls
open IntrinsicNativeListMapComputation
open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniformListTraceTypeInterpretation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- The exact retained induction proof used by the HOTG and operational
development, packaged as an intrinsic NIK proof object. -/
def retainedMapFusionProof : IntrinsicProof where
  conclusion := HOLLeibnizMapFusionNative.closedClaim
  source := HOLLeibnizMapFusionNative.closedProof
  supported :=
    CompilerAgreement.closed_map_fusion_recursively_supported

theorem retained_map_fusion_accepted :
    intrinsicKernel.decide HOLLeibnizMapFusionNative.closedClaim
      retainedMapFusionProof = true :=
  rfl

/-- A distinct, recursively supported closed theorem supplies a wrong-target
control without conflating rejection of one submission with falsehood. -/
def identityClaim : ClosedClaim :=
  .eq
    HOLLeibnizNativeExtensionalProofTranslation.Controls.propositionIdentityFunction
    HOLLeibnizNativeExtensionalProofTranslation.Controls.propositionIdentityFunction

def identityProof : IntrinsicProof where
  conclusion := identityClaim
  source :=
    HOLLeibnizNativeExtensionalProofTranslation.Controls.propositionIdentityFunctionExtensionality
  supported := rfl

theorem retained_map_fusion_rejected_for_identity :
    intrinsicKernel.decide identityClaim retainedMapFusionProof = false :=
  rfl

theorem identity_claim_remains_meaningful :
    sourceTarget.Meaning identityClaim :=
  ⟨HOLLeibnizNativeExtensionalProofTranslation.Controls.propositionIdentityFunctionExtensionality,
    rfl⟩

/-- Rejection of the map-fusion proof at a different conclusion does not
refute that conclusion: the identity theorem has its own accepted proof. -/
theorem wrong_target_rejection_does_not_refute :
    intrinsicKernel.decide identityClaim retainedMapFusionProof = false ∧
      intrinsicKernel.decide identityClaim identityProof = true ∧
      sourceTarget.Meaning identityClaim :=
  ⟨retained_map_fusion_rejected_for_identity, rfl,
    identity_claim_remains_meaningful⟩

/-- NIK acceptance of the retained object exposes the exact connected
compiler result, rather than a newly authored native proof. -/
theorem retained_acceptance_compiles_connected (a : ZFSet.{u}) :
    ∃ native code,
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile
          retainedMapFusionProof.source Fin.elim0 Fin.elim0 = some native ∧
      HOLLeibnizNativeQualifiedIntegration.Compiler.represent
          HOLLeibnizMapFusionNative.closedClaim = some code ∧
      Presentation.FormationSensitive.Judgment
          FormationSensitiveHOLExtensionalProfile.rules .nil native
          (FormationSensitiveHOLProofFamily.proof code) ∧
      ProofDenotes a NativeHOLTraceDisplayedTerms.Controls.emptyContext native
        (formulaMeaning HOLLeibnizMapFusionNative.closedClaim
          NativeHOLTraceDisplayedTerms.Controls.emptyContext
          (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation
            (a := a))) :=
  native_acceptance_compiles_connected
    HOLLeibnizMapFusionNative.closedClaim retainedMapFusionProof
      retained_map_fusion_accepted

/-- The operational observation furnished by the retained proof, separated
as a proposition so the same NIK qualification can be instantiated at any
trace carrier and two captured element values. -/
def NoncommutingOperationalSquare (level : LevelExpr) {a : ZFSet.{u}}
    (older newer : Value a element) : Prop :=
  semanticDiamond (reduction level 2).closure
      (semanticObservation level (twoElementEnvironment older newer)
        (fun output => output = ZFSetList.encodeValue [older]))
      (applyMap (elementCode 2) (elementCode 2) constantOlder
        (applyMap (elementCode 2) (elementCode 2) constantNewer
          (encode (elementCode 2) [olderHead]))) ∧
    semanticDiamond (reduction level 2).closure
      (semanticObservation level (twoElementEnvironment older newer)
        (fun output => output = ZFSetList.encodeValue [older]))
      (applyMap (elementCode 2) (elementCode 2)
        (compose constantOlder constantNewer)
        (encode (elementCode 2) [olderHead]))

/-- A single theorem package crosses every boundary of the present route.
The NIK service accepts the retained HOL induction proof; the recursive
compiler emits the already interpreted native proof; two captured native
functions demonstrably do not commute; and OSLF observes both programs at
the same Aczel endpoint with the source theorem's composition orientation. -/
theorem retained_map_fusion_qualifies_noncommuting_observation
    (level : LevelExpr) {a : ZFSet.{u}}
    (older newer : Value a element) (different : older ≠ newer) :
    intrinsicKernel.decide HOLLeibnizMapFusionNative.closedClaim
        retainedMapFusionProof = true ∧
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile
          retainedMapFusionProof.source Fin.elim0 Fin.elim0 =
        some HOLLeibnizMapFusionNative.nativeProof ∧
      app (constantOlderMeaning (twoElementEnvironment older newer))
          (app (constantNewerMeaning (twoElementEnvironment older newer)) older) ≠
        app (constantNewerMeaning (twoElementEnvironment older newer))
          (app (constantOlderMeaning (twoElementEnvironment older newer)) older) ∧
      NoncommutingOperationalSquare level older newer := by
  exact ⟨retained_map_fusion_accepted,
    CompilerAgreement.recursive_compiler_emits_closed_map_fusion,
    captured_constants_do_not_commute older newer different,
    noncommuting_fusion_semantic_observed level older newer⟩

end Controls

#print axioms intrinsic_meaning_exact
#print axioms native_accepts_iff_supported_derivable
#print axioms native_acceptance_derivation
#print axioms native_acceptance_compiles_connected
#print axioms native_service_has_no_external_certificate_boundary
#print axioms Controls.retained_map_fusion_accepted
#print axioms Controls.wrong_target_rejection_does_not_refute
#print axioms Controls.retained_acceptance_compiles_connected
#print axioms Controls.retained_map_fusion_qualifies_noncommuting_observation

end NativeHOLRecursiveProofNIKQualification
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
