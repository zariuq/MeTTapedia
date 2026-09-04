import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation
import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation

/-!
# Speculative lookup inside the ordered compressed-verifier presentation

The ordered verifier has two independently authored layers: source-bound
activation/header rules and the compact proof-machine body.  Speculative heap
lookup transforms only the supplied body and its persistent code rows.  This
module applies that pass first, then reattaches the unchanged header through an
explicit finite-presentation seam.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation

private theorem decoratedSpeculativeBody_buildable :
    (transformCompressedVerifierPresentation?
      compressedBodyRulesWithNormalBridgeAndSourceVerdictAndFaultReject
      compressedVerifierStaticRowsWithNormalBridgeAndSourceFaultReject).isSome =
        true := by
  decide +kernel

/-- The result of transforming the actual decorated body supplied to ordered
activation, rather than the undecorated calibration presentation. -/
def decoratedSpeculativeBody : CompiledPresentation :=
  (transformCompressedVerifierPresentation?
    compressedBodyRulesWithNormalBridgeAndSourceVerdictAndFaultReject
    compressedVerifierStaticRowsWithNormalBridgeAndSourceFaultReject).get
      (by simpa using decoratedSpeculativeBody_buildable)

theorem decoratedSpeculativeBody_build_exact :
    transformCompressedVerifierPresentation?
        compressedBodyRulesWithNormalBridgeAndSourceVerdictAndFaultReject
        compressedVerifierStaticRowsWithNormalBridgeAndSourceFaultReject =
      some decoratedSpeculativeBody := by
  unfold decoratedSpeculativeBody
  exact (Option.some_get
    (by simpa using decoratedSpeculativeBody_buildable)).symm

/-- The compiler consumes the exact decorated compact body used by the
ordered verifier. -/
theorem decoratedSpeculativeBody_source_exact :
    decoratedSpeculativeBody.sourceRules =
      compressedBodyRulesWithNormalBridgeAndSourceVerdictAndFaultReject := by
  exact transformCompressedVerifierPresentation?_sourceRules
    decoratedSpeculativeBody_build_exact

/-- The decorated compiler's remembered opaque occurrence is exactly the
normal-bridge assertion launcher at the selected source position. -/
theorem decoratedSpeculativeBody_sourceOpaque_exact :
    decoratedSpeculativeBody.selected.artifact.sourceOpaqueRule =
      compressedAssertionLaunchRuleWithNormalBridge := by
  have selected := transformCompressedVerifierPresentation?_sourceOpaqueRule
    decoratedSpeculativeBody_build_exact
  change
    compressedBodyRulesWithNormalBridgeAndSourceVerdictAndFaultReject[7]? =
      some decoratedSpeculativeBody.selected.artifact.sourceOpaqueRule at selected
  rw [
    compressedBodyRulesWithNormalBridgeAndSourceVerdictAndFaultReject_assertion_at]
    at selected
  exact (Option.some.inj selected).symm

/-- Header rules remain a distinct unchanged prefix while the target body is
the result of the input-sensitive speculative transformation. -/
def compressedSpeculativeVerifierRulePresentation :
    FiniteVerifierRulePresentation where
  family := compressedVerifierRulePresentation.family
  owner := compressedVerifierRulePresentation.owner
  endTag := compressedVerifierRulePresentation.endTag
  rules := compressedHeaderRulesWithReloadAndSourceFaultReject ++
    decoratedSpeculativeBody.targetRules

def compressedSpeculativeVerifierRuleRows : List Atom :=
  compressedSpeculativeVerifierRulePresentation.rows

def compressedSpeculativeVerifierRuleEnd : Atom :=
  compressedSpeculativeVerifierRulePresentation.endRow

def compressedSpeculativeVerifierStaticRows : List Atom :=
  decoratedSpeculativeBody.targetStaticRows

theorem compressedSpeculativeVerifier_header_exact :
    compressedSpeculativeVerifierRulePresentation.rules.take
        compressedHeaderRulesWithReloadAndSourceFaultReject.length =
      compressedHeaderRulesWithReloadAndSourceFaultReject := by
  simp [compressedSpeculativeVerifierRulePresentation]

theorem compressedSpeculativeVerifier_body_exact :
    compressedSpeculativeVerifierRulePresentation.rules.drop
        compressedHeaderRulesWithReloadAndSourceFaultReject.length =
      decoratedSpeculativeBody.targetRules := by
  simp [compressedSpeculativeVerifierRulePresentation]

/-- The pass adds exactly two direct-handler occurrences to the ordered
verifier while preserving every header occurrence. -/
theorem compressedSpeculativeVerifier_target_length :
    compressedSpeculativeVerifierRulePresentation.rules.length =
      compressedVerifierRulePresentation.rules.length + 2 := by
  have bodyLength := transformCompressedVerifierPresentation?_targetRules_length
    decoratedSpeculativeBody_build_exact
  rw [compressedSpeculativeVerifierRulePresentation,
    compressedVerifierRulePresentation]
  simp only [List.length_append]
  omega

/-- Persistent runtime code is the output of the same successful body
transformation, not an independently reconstructed row list. -/
theorem compressedSpeculativeVerifier_static_exact :
    compressedSpeculativeVerifierStaticRows =
      decoratedSpeculativeBody.targetStaticRows := by
  rfl

/-- The existing ordered loader can consume the transformed presentation
without a second loader dialect: family, owner, and terminal tag are retained
exactly, while only the occurrence-indexed body and its terminal position
change. -/
theorem compressedSpeculativeVerifier_loader_seam_exact :
    compressedSpeculativeVerifierRulePresentation.family =
        compressedVerifierRulePresentation.family ∧
      compressedSpeculativeVerifierRulePresentation.owner =
        compressedVerifierRulePresentation.owner ∧
      compressedSpeculativeVerifierRulePresentation.endTag =
        compressedVerifierRulePresentation.endTag := by
  exact ⟨rfl, rfl, rfl⟩

/-- Complete generated-input extension with the speculative body installed
behind the unchanged ordered activation layer. -/
def compressedSpeculativeOrderedVerifierExtensionProgram : List Atom :=
  compressedOrderedActivationRules ++ compressedSpeculativeVerifierRuleRows ++
    [compressedSpeculativeVerifierRuleEnd] ++
      compressedSpeculativeVerifierStaticRows ++
      compressedNormalHandoffRuleRows ++ [compressedNormalHandoffRuleEnd] ++
        compressedNormalDispatchBridgeRows ++
          [compressedDispatchReloadCaptureRow]

theorem compressedSpeculativeOrderedVerifierExtensionProgram_exact :
    compressedSpeculativeOrderedVerifierExtensionProgram =
      compressedOrderedActivationRules ++
        compressedSpeculativeVerifierRulePresentation.rows ++
        [compressedSpeculativeVerifierRulePresentation.endRow] ++
        decoratedSpeculativeBody.targetStaticRows ++
        compressedNormalHandoffRuleRows ++ [compressedNormalHandoffRuleEnd] ++
        compressedNormalDispatchBridgeRows ++
        [compressedDispatchReloadCaptureRow] := by
  rfl

#print axioms decoratedSpeculativeBody_build_exact
#print axioms decoratedSpeculativeBody_source_exact
#print axioms decoratedSpeculativeBody_sourceOpaque_exact
#print axioms compressedSpeculativeVerifier_header_exact
#print axioms compressedSpeculativeVerifier_body_exact
#print axioms compressedSpeculativeVerifier_target_length
#print axioms compressedSpeculativeVerifier_static_exact
#print axioms compressedSpeculativeVerifier_loader_seam_exact
#print axioms compressedSpeculativeOrderedVerifierExtensionProgram_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
