import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayFunctionRelations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayFormation

/-!
# Whole-function agreement for checked lambdas with structural bodies

An accepted product formation retains the domain used by lambda assembly.
When the raw domain is in the structurally interpreted fragment, distinct
accepted formation certificates retain the same domain, even without a
neutral-elimination qualification. A structural lambda body then has one
value under independently accepted body certificates. Together these facts
identify the complete trace-coded function, not only its applications.

The result is restricted to the no-conversion checker and structural domain
and body expressions. In particular, it does not identify functions whose
distinct retained domains differ outside a valid environment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment extend)

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

/-- Two checked formations of one Π expression retain the same domain when
the raw domain has a certificate-independent structural interpretation.
No qualification is imposed on either formation tree. -/
theorem checked_pi_domains_eq_of_supported
    (context : Ctx Head n) (A : Tm Head n) (B : Tm Head (n + 1))
    (leftLevel rightLevel : Head)
    (leftCode rightCode : Code Head NoConversion n)
    (left right : Meaning.{u} n)
    (leftChecked : check R noConversionCheck context (.pi A B)
      (.head leftLevel) leftCode = true)
    (rightChecked : check R noConversionCheck context (.pi A B)
      (.head rightLevel) rightCode = true)
    (atLeft : assemble heads constants leftCode (.pi A B) (.head leftLevel) = some left)
    (atRight : assemble heads constants rightCode (.pi A B) (.head rightLevel) = some right)
    (supportedA : ZFSetTypeExpressionInterpretation.supported A = true) :
    left.productDomain? = right.productDomain? := by
  obtain ⟨_, _, leftDomainCode, leftBodyCode, leftParts, _, _, _, _⟩ :=
    leftCode.piFormation_checked R noConversionCheck leftChecked
  obtain ⟨_, _, rightDomainCode, rightBodyCode, rightParts, _, _, _, _⟩ :=
    rightCode.piFormation_checked R noConversionCheck rightChecked
  obtain ⟨leftDomain, _, atLeftDomain, _, _, leftProductDomain⟩ :=
    assemble_piFormation heads constants leftCode leftParts atLeft
  obtain ⟨rightDomain, _, atRightDomain, _, _, rightProductDomain⟩ :=
    assemble_piFormation heads constants rightCode rightParts atRight
  have sameDomain := assemble_supported_values heads constants supportedA
    atLeftDomain atRightDomain
  rw [leftProductDomain, rightProductDomain, sameDomain]

/-- The complete set-coded function of a checked lambda is independent of
its two retained certificates if its raw domain and body are structural.
The body may still compute by application or projection. Both accepted
certificates and both actual assembly receipts are used in the conclusion. -/
theorem checked_lambda_values_eq_of_supported
    (context : Ctx Head n) (A : Tm Head n) (B body : Tm Head (n + 1))
    (leftLevel rightLevel : Head)
    (leftFormation rightFormation : Code Head NoConversion n)
    (leftBodyCode rightBodyCode : Code Head NoConversion (n + 1))
    (left right : Meaning.{u} n)
    (leftChecked : check R noConversionCheck context (.lam body) (.pi A B)
      (.lamIntro leftLevel leftFormation leftBodyCode) = true)
    (rightChecked : check R noConversionCheck context (.lam body) (.pi A B)
      (.lamIntro rightLevel rightFormation rightBodyCode) = true)
    (atLeft : assemble heads constants (.lamIntro leftLevel leftFormation leftBodyCode)
      (.lam body) (.pi A B) = some left)
    (atRight : assemble heads constants (.lamIntro rightLevel rightFormation rightBodyCode)
      (.lam body) (.pi A B) = some right)
    (supportedA : ZFSetTypeExpressionInterpretation.supported A = true)
    (supportedBody : ZFSetTypeExpressionInterpretation.supported body = true) :
    left.value = right.value := by
  have leftParts := leftChecked
  have rightParts := rightChecked
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at leftParts rightParts
  have leftFormationChecked := leftParts.1.2
  have rightFormationChecked := rightParts.1.2
  have leftBodyChecked := leftParts.2
  have rightBodyChecked := rightParts.2
  obtain ⟨leftFormed, atLeftFormation, leftProduct⟩ :=
    accepted_assembles heads constants R noConversionCheck leftFormation leftFormationChecked
  obtain ⟨rightFormed, atRightFormation, rightProduct⟩ :=
    accepted_assembles heads constants R noConversionCheck rightFormation rightFormationChecked
  obtain ⟨leftDomain, atLeftDomain⟩ := leftProduct A B rfl
  obtain ⟨rightDomain, atRightDomain⟩ := rightProduct A B rfl
  obtain ⟨leftBody, atLeftBody, _⟩ :=
    accepted_assembles heads constants R noConversionCheck leftBodyCode leftBodyChecked
  obtain ⟨rightBody, atRightBody, _⟩ :=
    accepted_assembles heads constants R noConversionCheck rightBodyCode rightBodyChecked
  have sameDomain := checked_pi_domains_eq_of_supported heads constants R
    context A B leftLevel rightLevel leftFormation rightFormation leftFormed rightFormed
    leftFormationChecked rightFormationChecked atLeftFormation atRightFormation supportedA
  rw [atLeftDomain, atRightDomain] at sameDomain
  have domainsEqual : leftDomain = rightDomain := Option.some.inj sameDomain
  have bodiesEqual := assemble_supported_values heads constants supportedBody
    atLeftBody atRightBody
  funext env
  apply assembled_lambdas_eq_of_related heads constants leftLevel rightLevel A A B B
    body body leftFormation rightFormation leftBodyCode rightBodyCode leftFormed
    rightFormed left right leftBody rightBody leftDomain rightDomain atLeftFormation
    atRightFormation atLeftDomain atRightDomain atLeftBody atRightBody atLeft
    atRight env env (congrFun domainsEqual env)
  intro x _
  exact congrFun bodiesEqual (extend env x)

#print axioms checked_pi_domains_eq_of_supported
#print axioms checked_lambda_values_eq_of_supported

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
