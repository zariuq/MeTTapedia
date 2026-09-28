import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySupportedApplicationCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIdentityComparison

/-!
# Proof admission over independently checked computed applications

The raw endpoint of the identity below is an application of a lambda and
need not have a structural interpretation. Its two accepted certificates
still agree because their domain, body, and computed argument do. Identity
generation then exposes those exact endpoint certificates, and the checked
reflexivity token inhabits the independently assembled identity fibre.

This is not equality reflection or a general claim that accepted certificates
agree. The structural hypotheses apply to the *components* of the computed
endpoint, and both checked certificates remain explicit.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding (truthCode mem_truthCode)

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

/-- A retained reflexivity proof at a computed application is accepted by an
independently checked identity formation whose left and right endpoint
certificates are distinct. Their agreement is derived from the checked
application theorem, not supplied as an external semantic premise. -/
theorem checked_structural_application_reflexivity_member
    (context : Ctx Head n) (A : Tm Head n) (B body : Tm Head (n + 1))
    (argument : Tm Head n) (leftLevel rightLevel identityLevel : Head)
    (leftFormation rightFormation leftArgumentCode rightArgumentCode
      carrierFormation : Code Head NoConversion n)
    (leftBodyCode rightBodyCode : Code Head NoConversion (n + 1))
    (proofChecked : check R noConversionCheck context
      (.refl (.app (.lam body) argument))
      (.id (inst0 argument B) (.app (.lam body) argument)
        (.app (.lam body) argument))
      (.reflIntro (inst0 argument B)
        (.appElim A B (.lamIntro leftLevel leftFormation leftBodyCode)
          leftArgumentCode)) = true)
    (identityChecked : check R noConversionCheck context
      (.id (inst0 argument B) (.app (.lam body) argument)
        (.app (.lam body) argument)) (.head identityLevel)
      (.idForm identityLevel carrierFormation
        (.appElim A B (.lamIntro leftLevel leftFormation leftBodyCode)
          leftArgumentCode)
        (.appElim A B (.lamIntro rightLevel rightFormation rightBodyCode)
          rightArgumentCode)) = true)
    (supportedA : ZFSetTypeExpressionInterpretation.supported A = true)
    (supportedBody : ZFSetTypeExpressionInterpretation.supported body = true)
    (supportedArgument : ZFSetTypeExpressionInterpretation.supported argument = true) :
    ∃ proof identity : Meaning.{u} n,
      assemble heads constants
        (.reflIntro (inst0 argument B)
          (.appElim A B (.lamIntro leftLevel leftFormation leftBodyCode)
            leftArgumentCode))
        (.refl (.app (.lam body) argument))
        (.id (inst0 argument B) (.app (.lam body) argument)
          (.app (.lam body) argument)) = some proof ∧
      assemble heads constants
        (.idForm identityLevel carrierFormation
          (.appElim A B (.lamIntro leftLevel leftFormation leftBodyCode)
            leftArgumentCode)
          (.appElim A B (.lamIntro rightLevel rightFormation rightBodyCode)
            rightArgumentCode))
        (.id (inst0 argument B) (.app (.lam body) argument)
          (.app (.lam body) argument)) (.head identityLevel) = some identity ∧
      ∀ env, proof.value env ∈ identity.value env := by
  let term := Tm.app (.lam body) argument
  let leftCode : Code Head NoConversion n :=
    .appElim A B (.lamIntro leftLevel leftFormation leftBodyCode) leftArgumentCode
  let rightCode : Code Head NoConversion n :=
    .appElim A B (.lamIntro rightLevel rightFormation rightBodyCode) rightArgumentCode
  let identityCode : Code Head NoConversion n :=
    .idForm identityLevel carrierFormation leftCode rightCode
  obtain ⟨proof, atProof, _⟩ := accepted_assembles heads constants R
    noConversionCheck (.reflIntro (inst0 argument B) leftCode) proofChecked
  obtain ⟨identity, atIdentity, _⟩ := accepted_assembles heads constants R
    noConversionCheck identityCode identityChecked
  refine ⟨proof, identity, atProof, atIdentity, ?_⟩
  have principal : identityCode.principalView (.head identityLevel) =
      some ⟨.head identityLevel,
        .idForm identityLevel carrierFormation leftCode rightCode, .hole⟩ := rfl
  obtain ⟨leftChecked, rightChecked⟩ := identity_endpoint_checks R identityCode
    identityLevel carrierFormation leftCode rightCode .hole identityChecked principal
  obtain ⟨left, right, atLeft, atRight, identityValue⟩ :=
    assemble_identity_endpoints heads constants identityCode (inst0 argument B)
      term term (.head identityLevel) identityLevel carrierFormation
      leftCode rightCode .hole identity principal atIdentity
  have endpointAgreement := checked_structural_lambda_applications_agree
    heads constants R context A B body argument leftLevel rightLevel
    leftFormation rightFormation leftArgumentCode rightArgumentCode
    leftBodyCode rightBodyCode left right leftChecked rightChecked atLeft atRight
    supportedA supportedBody supportedArgument
  intro env
  have proofValue : proof.value env = ∅ := by
    simp only [assemble, Option.some.injEq] at atProof
    subst proof
    rfl
  rw [identityValue, proofValue]
  exact (mem_truthCode _ _).mpr ⟨rfl, congrFun endpointAgreement env⟩

#print axioms checked_structural_application_reflexivity_member

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
