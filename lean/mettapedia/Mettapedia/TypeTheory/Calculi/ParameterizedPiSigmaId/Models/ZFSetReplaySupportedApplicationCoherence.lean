import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySupportedLambdaCoherence

/-!
# Checked applications with structural computed arguments

The actual replay of an application uses the separately assembled function and
argument. When two accepted certificates check the same lambda application,
structural interpretation of its domain, body, and argument identifies those
two ingredients. Hence the complete application values agree. The argument
may itself be a computed expression, including a dependent-pair projection.

This is an extensional comparison of replayed values, not a general semantic
typing theorem: typing membership for non-structural arguments still needs
the qualification and universe-model hypotheses of `qualified_membership`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

/-- Two independently checked applications of the same lambda to the same
computed structural argument have the same complete replay value. Formation,
body, and argument certificates may differ; both application receipts are
required. This does not identify unrelated functions or arguments. -/
theorem checked_structural_lambda_applications_agree
    (context : Ctx Head n) (A : Tm Head n) (B body : Tm Head (n + 1))
    (argument : Tm Head n)
    (leftLevel rightLevel : Head)
    (leftFormation rightFormation leftArgumentCode rightArgumentCode :
      Code Head NoConversion n)
    (leftBodyCode rightBodyCode : Code Head NoConversion (n + 1))
    (left right : Meaning.{u} n)
    (leftChecked : check R noConversionCheck context (.app (.lam body) argument)
      (inst0 argument B)
      (.appElim A B (.lamIntro leftLevel leftFormation leftBodyCode)
        leftArgumentCode) = true)
    (rightChecked : check R noConversionCheck context (.app (.lam body) argument)
      (inst0 argument B)
      (.appElim A B (.lamIntro rightLevel rightFormation rightBodyCode)
        rightArgumentCode) = true)
    (atLeft : assemble heads constants
      (.appElim A B (.lamIntro leftLevel leftFormation leftBodyCode)
        leftArgumentCode) (.app (.lam body) argument) (inst0 argument B) = some left)
    (atRight : assemble heads constants
      (.appElim A B (.lamIntro rightLevel rightFormation rightBodyCode)
        rightArgumentCode) (.app (.lam body) argument) (inst0 argument B) = some right)
    (supportedA : ZFSetTypeExpressionInterpretation.supported A = true)
    (supportedBody : ZFSetTypeExpressionInterpretation.supported body = true)
    (supportedArgument : ZFSetTypeExpressionInterpretation.supported argument = true) :
    left.value = right.value := by
  have leftParts := leftChecked
  have rightParts := rightChecked
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at leftParts rightParts
  have leftLambdaChecked : check R noConversionCheck context (.lam body) (.pi A B)
      (.lamIntro leftLevel leftFormation leftBodyCode) = true := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using leftParts.1.1
  have rightLambdaChecked : check R noConversionCheck context (.lam body) (.pi A B)
      (.lamIntro rightLevel rightFormation rightBodyCode) = true := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using rightParts.1.1
  obtain ⟨leftFunction, atLeftFunction, _⟩ :=
    accepted_assembles heads constants R noConversionCheck
      (.lamIntro leftLevel leftFormation leftBodyCode) leftLambdaChecked
  obtain ⟨rightFunction, atRightFunction, _⟩ :=
    accepted_assembles heads constants R noConversionCheck
      (.lamIntro rightLevel rightFormation rightBodyCode) rightLambdaChecked
  obtain ⟨leftArg, atLeftArg, _⟩ :=
    accepted_assembles heads constants R noConversionCheck
      leftArgumentCode leftParts.1.2
  obtain ⟨rightArg, atRightArg, _⟩ :=
    accepted_assembles heads constants R noConversionCheck
      rightArgumentCode rightParts.1.2
  have functionsEqual := checked_lambda_values_eq_of_supported heads constants R
    context A B body leftLevel rightLevel leftFormation rightFormation
    leftBodyCode rightBodyCode leftFunction rightFunction
    leftLambdaChecked rightLambdaChecked atLeftFunction atRightFunction
    supportedA supportedBody
  have argumentsEqual := assemble_supported_values heads constants
    supportedArgument atLeftArg atRightArg
  change (do
    let f' ← assemble heads constants
      (.lamIntro leftLevel leftFormation leftBodyCode) (.lam body) (.pi A B)
    let a' ← assemble heads constants leftArgumentCode argument A
    return .plain (fun env =>
      Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts.traceApp
        (f'.value env) (a'.value env))) = some left at atLeft
  change (do
    let f' ← assemble heads constants
      (.lamIntro rightLevel rightFormation rightBodyCode) (.lam body) (.pi A B)
    let a' ← assemble heads constants rightArgumentCode argument A
    return .plain (fun env =>
      Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts.traceApp
        (f'.value env) (a'.value env))) = some right at atRight
  rw [atLeftFunction, atLeftArg] at atLeft
  rw [atRightFunction, atRightArg] at atRight
  change some (.plain (fun env =>
    Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts.traceApp
      (leftFunction.value env) (leftArg.value env))) = some left at atLeft
  change some (.plain (fun env =>
    Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts.traceApp
      (rightFunction.value env) (rightArg.value env))) = some right at atRight
  have leftValue := congrArg Meaning.value (Option.some.inj atLeft).symm
  have rightValue := congrArg Meaning.value (Option.some.inj atRight).symm
  change left.value = (fun env =>
    Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts.traceApp
      (leftFunction.value env) (leftArg.value env)) at leftValue
  change right.value = (fun env =>
    Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts.traceApp
      (rightFunction.value env) (rightArg.value env)) at rightValue
  rw [leftValue, rightValue]
  funext env
  rw [congrFun functionsEqual env, congrFun argumentsEqual env]

#print axioms checked_structural_lambda_applications_agree

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
