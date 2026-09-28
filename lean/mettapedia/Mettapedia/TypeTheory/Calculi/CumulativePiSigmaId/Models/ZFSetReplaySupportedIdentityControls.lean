import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySupportedIdentityCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySupportedApplicationIdentity
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplaySupportedLambdaControls

/-!
# Checked identity proofs after computed pair projection and application

The computed argument is a pair projection. The subsequent application is
not in the structural fragment because it contains a lambda. Nevertheless
two independently checked application certificates agree, and a checked
reflexivity proof enters an identity type whose two endpoint certificates
are those distinct applications. The structural endpoint result is tested
separately on the projection itself, including a retained cumulative wrapper.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplaySupportedIdentityControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetReplayApplicationComparisonControls (context)
open ZFSetReplayQualifiedLambdaApplicationControls
  (projectedBody projectedUpperFormation projectedUpperBodyCode projected_body_supported)
open ZFSetReplaySupportedLambdaControls
  (computedArgument computedArgumentCode computedProgram
    directApplicationCode liftedApplicationCode
    direct_application_checked lifted_application_checked
    computed_argument_supported)

universe u

private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev two : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev upperLevel : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))
private abbrev aboveUpperLevel : Tower.Head :=
  .sort (.succ (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero))))
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n

def wrappedArgumentCode : Replay 1 := .cumul one computedArgumentCode
def structuralIdentity : Tower.Tm 1 :=
  .id (.head one) computedArgument computedArgument
def structuralDirectCode : Replay 1 :=
  .idForm two .headType computedArgumentCode computedArgumentCode
def structuralWrappedCode : Replay 1 :=
  .idForm two .headType computedArgumentCode wrappedArgumentCode

theorem structural_direct_checked :
    check Tower.rules noConversionCheck context structuralIdentity (.head two)
      structuralDirectCode = true := by
  decide +kernel

theorem structural_wrapped_checked :
    check Tower.rules noConversionCheck context structuralIdentity (.head two)
      structuralWrappedCode = true := by
  decide +kernel

theorem structural_codes_differ : structuralDirectCode ≠ structuralWrappedCode := by
  intro equal
  cases equal

/-- The identity fibre of a computed pair projection is independent of a
retained cumulative wrapper on one of its checked endpoint certificates. -/
theorem checked_structural_identity_agrees
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    ∃ direct wrapped : Meaning.{u} 1,
      assemble heads constants structuralDirectCode structuralIdentity (.head two) =
        some direct ∧
      assemble heads constants structuralWrappedCode structuralIdentity (.head two) =
        some wrapped ∧
      direct = wrapped := by
  obtain ⟨direct, atDirect, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck structuralDirectCode structural_direct_checked
  obtain ⟨wrapped, atWrapped, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck structuralWrappedCode structural_wrapped_checked
  refine ⟨direct, wrapped, atDirect, atWrapped, ?_⟩
  exact checked_identity_structural_endpoints_coherent heads constants Tower.rules
    context (.head one) computedArgument computedArgument (.head two) (.head two)
    structuralDirectCode structuralWrappedCode direct wrapped
    structural_direct_checked structural_wrapped_checked atDirect atWrapped
    computed_argument_supported computed_argument_supported

def applicationIdentity : Tower.Tm 1 :=
  .id (.head one) computedProgram computedProgram
def applicationProof : Tower.Tm 1 := .refl computedProgram
def applicationProofCode : Replay 1 :=
  .reflIntro (.head one) directApplicationCode
def applicationIdentityCode : Replay 1 :=
  .idForm two .headType directApplicationCode liftedApplicationCode

theorem computed_program_not_structural :
    ZFSetTypeExpressionInterpretation.supported computedProgram = false := by
  decide +kernel

theorem application_proof_checked :
    check Tower.rules noConversionCheck context applicationProof applicationIdentity
      applicationProofCode = true := by
  decide +kernel

theorem application_identity_checked :
    check Tower.rules noConversionCheck context applicationIdentity (.head two)
      applicationIdentityCode = true := by
  decide +kernel

/-- The whole computed application is outside the structural fragment, yet
the retained proof is admitted by an identity formation comparing two
distinct checked application certificates. No erased-term certificate is
reconstructed and no endpoint equality is assumed. -/
theorem checked_nonstructural_application_proof_member
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    ∃ proof identity : Meaning.{u} 1,
      assemble heads constants applicationProofCode applicationProof
        applicationIdentity = some proof ∧
      assemble heads constants applicationIdentityCode applicationIdentity
        (.head two) = some identity ∧
      ∀ env, proof.value env ∈ identity.value env := by
  exact checked_structural_application_reflexivity_member heads constants
    Tower.rules context (.head one) (.head one) projectedBody computedArgument
    upperLevel aboveUpperLevel two projectedUpperFormation
    (.cumul upperLevel projectedUpperFormation) computedArgumentCode
    computedArgumentCode .headType projectedUpperBodyCode projectedUpperBodyCode
    application_proof_checked application_identity_checked rfl
    projected_body_supported computed_argument_supported

#print axioms structural_direct_checked
#print axioms structural_wrapped_checked
#print axioms structural_codes_differ
#print axioms checked_structural_identity_agrees
#print axioms computed_program_not_structural
#print axioms application_proof_checked
#print axioms application_identity_checked
#print axioms checked_nonstructural_application_proof_member

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplaySupportedIdentityControls
