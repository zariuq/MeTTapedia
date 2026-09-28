import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySubstitution

/-!
# Computation with the domains retained by replay interpretation

The receipts below are equations for the actual recursive assembly function.
Application uses the lambda's original formation-domain value. Argument
membership is explicit; no equality of product sets supplies it. Projection
computation uses the same Kuratowski pair representation as dependent sums.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment extend)
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.SetTheory

universe u
variable {Head : Type} {ConversionCode : Nat → Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

theorem application_lambda_value
    (level : Head) (A : Tm Head n) (B body : Tm Head (n + 1)) (argument : Tm Head n)
    (formation argumentCode : Code Head ConversionCode n) (bodyCode : Code Head ConversionCode (n + 1))
    (formed arg result : Meaning.{u} n) (bodyMeaning : Meaning.{u} (n + 1)) (domain : Value.{u} n)
    (atFormation : assemble heads constants formation (.pi A B) (.head level) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (atBody : assemble heads constants bodyCode body B = some bodyMeaning)
    (atArgument : assemble heads constants argumentCode argument A = some arg)
    (atResult : assemble heads constants
      (.appElim A B (.lamIntro level formation bodyCode) argumentCode)
      (.app (.lam body) argument) (inst0 argument B) = some result)
    (environment : Environment.{u} n) (inside : arg.value environment ∈ domain environment) :
    result.value environment = bodyMeaning.value (extend environment (arg.value environment)) := by
  simp [assemble, atFormation, atDomain, atBody, atArgument] at atResult
  subst result
  exact ZFSetTraceProducts.traceApp_graph_beta _ inside

/-- Where the reduct is in the structural fragment, the result agrees with
interpretation of the actual capture-avoiding native substitution. Nested
lambda bodies use the more general environment equation above. -/
theorem application_lambda_substituted_value
    (level : Head) (A : Tm Head n) (B body : Tm Head (n + 1)) (argument : Tm Head n)
    (formation argumentCode : Code Head ConversionCode n) (bodyCode : Code Head ConversionCode (n + 1))
    (formed arg result : Meaning.{u} n) (bodyMeaning : Meaning.{u} (n + 1)) (domain : Value.{u} n)
    (atFormation : assemble heads constants formation (.pi A B) (.head level) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (atBody : assemble heads constants bodyCode body B = some bodyMeaning)
    (atArgument : assemble heads constants argumentCode argument A = some arg)
    (atResult : assemble heads constants
      (.appElim A B (.lamIntro level formation bodyCode) argumentCode)
      (.app (.lam body) argument) (inst0 argument B) = some result)
    (supportedBody : ZFSetTypeExpressionInterpretation.supported body = true)
    (supportedArgument : ZFSetTypeExpressionInterpretation.supported argument = true)
    (environment : Environment.{u} n) (inside : arg.value environment ∈ domain environment) :
    ∃ admitted : ZFSetTypeExpressionInterpretation.supported (inst0 argument body) = true,
      result.value environment =
        ZFSetTypeExpressionInterpretation.interpret heads constants (inst0 argument body) admitted environment := by
  have supportedImages : ∀ index, ZFSetTypeExpressionInterpretation.supported
      (subst0 argument index) = true := by
    intro index
    exact Fin.cases supportedArgument (fun _ => rfl) index
  refine ⟨ZFSetTypeExpressionInterpretation.supported_subst body supportedBody
    (subst0 argument) supportedImages, ?_⟩
  rw [application_lambda_value heads constants level A B body argument formation argumentCode bodyCode
    formed arg result bodyMeaning domain atFormation atDomain atBody atArgument atResult environment inside]
  rw [agrees_with_type_expressions heads constants bodyCode body B bodyMeaning supportedBody atBody]
  rw [agrees_with_type_expressions heads constants argumentCode argument A arg supportedArgument atArgument]
  dsimp only [inst0]
  rw [ZFSetTypeExpressionInterpretation.interpret_subst heads constants body supportedBody
    (subst0 argument) supportedImages]
  congr 1
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

theorem first_pair_value (level : Head) (A x y : Tm Head n) (B : Tm Head (n + 1))
    (formation firstCode secondCode : Code Head ConversionCode n) (first second result : Meaning.{u} n)
    (atFirst : assemble heads constants firstCode x A = some first)
    (atSecond : assemble heads constants secondCode y (inst0 x B) = some second)
    (atResult : assemble heads constants (.fstElim B (.pairIntro level formation firstCode secondCode))
      (.fst (.pair x y)) A = some result) (environment : Environment.{u} n) :
    result.value environment = first.value environment := by
  simp [assemble, atFirst, atSecond] at atResult
  subst result
  exact ZFSetOrderedPair.first_pair _ _

theorem second_pair_value (level : Head) (A x y : Tm Head n) (B : Tm Head (n + 1))
    (formation firstCode secondCode : Code Head ConversionCode n) (first second result : Meaning.{u} n)
    (atFirst : assemble heads constants firstCode x A = some first)
    (atSecond : assemble heads constants secondCode y (inst0 x B) = some second)
    (atResult : assemble heads constants (.sndElim A B (.pairIntro level formation firstCode secondCode))
      (.snd (.pair x y)) (inst0 (.fst (.pair x y)) B) = some result)
    (environment : Environment.{u} n) : result.value environment = second.value environment := by
  simp [assemble, atFirst, atSecond] at atResult
  subst result
  exact ZFSetOrderedPair.second_pair _ _

/-- Beta agrees with the actual certificate-instantiated reduct for arbitrary
checked bodies, not just the lambda-free structural interpretation fragment.
Argument membership uses the introduction's retained domain. -/
theorem application_lambda_instantiated_value
    (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
    (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)
    (R : Rules Head) [DecidableEq Head]
    [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
    [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]
    (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)
    (context : Ctx Head n) (level : Head) (A : Tm Head n) (B body : Tm Head (n + 1))
    (argument : Tm Head n) (formation argumentCode : Code Head ConversionCode n)
    (bodyCode : Code Head ConversionCode (n + 1))
    (formed arg result : Meaning.{u} n) (bodyMeaning : Meaning.{u} (n + 1)) (domain : Value.{u} n)
    (bodyAccepted : check R conversionCheck (.snoc context A) body B bodyCode = true)
    (atFormation : assemble heads constants formation (.pi A B) (.head level) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (atBody : assemble heads constants bodyCode body B = some bodyMeaning)
    (atArgument : assemble heads constants argumentCode argument A = some arg)
    (atResult : assemble heads constants
      (.appElim A B (.lamIntro level formation bodyCode) argumentCode)
      (.app (.lam body) argument) (inst0 argument B) = some result)
    (environment : Environment.{u} n) (inside : arg.value environment ∈ domain environment) :
    ∃ reduct, assemble heads constants
        (Code.instantiate renameConversion substituteConversion body B argument bodyCode argumentCode)
        (inst0 argument body) (inst0 argument B) = some reduct ∧
      result.value environment = reduct.value environment := by
  obtain ⟨reduct, assembled, values⟩ :=
    assemble_instantiate renameConversion substituteConversion heads constants R conversionCheck
      bodyCode argumentCode bodyMeaning arg bodyAccepted atBody atArgument
  refine ⟨reduct, assembled, ?_⟩
  exact (application_lambda_value heads constants level A B body argument formation argumentCode bodyCode
    formed arg result bodyMeaning domain atFormation atDomain atBody atArgument atResult environment inside).trans
      (values environment).symm

#print axioms application_lambda_instantiated_value
#print axioms application_lambda_value
#print axioms application_lambda_substituted_value
#print axioms first_pair_value
#print axioms second_pair_value

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
