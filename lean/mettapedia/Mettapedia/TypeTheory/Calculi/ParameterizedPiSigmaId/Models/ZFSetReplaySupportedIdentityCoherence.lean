import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIdentityGeneration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayCoherence

/-!
# Checked identity fibres with structural computed endpoints

An accepted identity certificate exposes its actual endpoint certificates,
even beneath a result wrapper. If the two raw endpoints have a structural
interpretation, independently accepted endpoint certificates have the same
values. The resulting identity truth code is therefore independent of the
identity certificates as well. This is a certificate-comparison theorem, not
an equality-reflection or general semantic-typing principle.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

/-- Two independently checked identity formations of the same raw identity
have the same complete replay meaning when both endpoints are structural.
The displayed universe levels and result wrappers may differ. Endpoint
certificates are obtained from the checked formation itself, not invented
afterwards. -/
theorem checked_identity_structural_endpoints_coherent
    (context : Ctx Head n) (A left right firstType secondType : Tm Head n)
    (firstCode secondCode : Code Head NoConversion n)
    (first second : Meaning.{u} n)
    (firstChecked : check R noConversionCheck context (.id A left right)
      firstType firstCode = true)
    (secondChecked : check R noConversionCheck context (.id A left right)
      secondType secondCode = true)
    (atFirst : assemble heads constants firstCode (.id A left right)
      firstType = some first)
    (atSecond : assemble heads constants secondCode (.id A left right)
      secondType = some second)
    (leftSupported : ZFSetTypeExpressionInterpretation.supported left = true)
    (rightSupported : ZFSetTypeExpressionInterpretation.supported right = true) :
    first = second := by
  obtain ⟨_, _, firstLeftCode, firstRightCode, _, a, b, _, _, _, _, _, _,
    atA, atB, firstValue⟩ :=
    checked_identity_generation heads constants R noConversionCheck firstCode first
      firstChecked atFirst
  obtain ⟨_, _, secondLeftCode, secondRightCode, _, c, d, _, _, _, _, _, _,
    atC, atD, secondValue⟩ :=
    checked_identity_generation heads constants R noConversionCheck secondCode second
      secondChecked atSecond
  have leftEqual := assemble_supported_values heads constants leftSupported atA atC
  have rightEqual := assemble_supported_values heads constants rightSupported atB atD
  rw [firstValue, secondValue, leftEqual, rightEqual]

#print axioms checked_identity_structural_endpoints_coherent

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
