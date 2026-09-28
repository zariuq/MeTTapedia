import Mettapedia.Logic.HOL.Embedding.ZFSetTraceFunctionRelations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputation

/-!
# Domain-indexed observations of assembled dependent functions

Two lambda certificates may denote different function sets because their
retained domains differ. Their observable applications can nevertheless be
related on the inputs admitted by each domain. This is the introduction law
for that relation over the actual replay assembly, not equality of graphs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment extend)
open Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts
open Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts (graph)

universe u
variable {Head : Type} {ConversionCode : Nat → Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

/-- The actual lambda replay constructor respects any input/output relation
that its two body interpretations respect on admitted inputs. The result is
an observational relation, not equality of potentially distinct graphs. -/
theorem assembled_lambdas_related
    (leftLevel rightLevel : Head) (leftA rightA : Tm Head n)
    (leftB rightB leftBody rightBody : Tm Head (n + 1))
    (leftFormation rightFormation : Code Head ConversionCode n)
    (leftBodyCode rightBodyCode : Code Head ConversionCode (n + 1))
    (leftFormed rightFormed leftLambda rightLambda : Meaning.{u} n)
    (leftBodyMeaning rightBodyMeaning : Meaning.{u} (n + 1))
    (leftDomain rightDomain : Value.{u} n)
    (atLeftFormation : assemble heads constants leftFormation (.pi leftA leftB)
      (.head leftLevel) = some leftFormed)
    (atRightFormation : assemble heads constants rightFormation (.pi rightA rightB)
      (.head rightLevel) = some rightFormed)
    (atLeftDomain : leftFormed.productDomain? = some leftDomain)
    (atRightDomain : rightFormed.productDomain? = some rightDomain)
    (atLeftBody : assemble heads constants leftBodyCode leftBody leftB = some leftBodyMeaning)
    (atRightBody : assemble heads constants rightBodyCode rightBody rightB = some rightBodyMeaning)
    (atLeftLambda : assemble heads constants (.lamIntro leftLevel leftFormation leftBodyCode)
      (.lam leftBody) (.pi leftA leftB) = some leftLambda)
    (atRightLambda : assemble heads constants (.lamIntro rightLevel rightFormation rightBodyCode)
      (.lam rightBody) (.pi rightA rightB) = some rightLambda)
    (leftEnv rightEnv : Environment.{u} n)
    (inputRelation outputRelation : ZFSet.{u} → ZFSet.{u} → Prop)
    (bodiesRelated : ∀ x ∈ leftDomain leftEnv, ∀ y ∈ rightDomain rightEnv,
      inputRelation x y → outputRelation
        (leftBodyMeaning.value (extend leftEnv x))
        (rightBodyMeaning.value (extend rightEnv y))) :
    TraceFunctionRelated (leftDomain leftEnv) (rightDomain rightEnv)
      inputRelation outputRelation (leftLambda.value leftEnv) (rightLambda.value rightEnv) := by
  simp [assemble, atLeftFormation, atLeftDomain, atLeftBody] at atLeftLambda
  simp [assemble, atRightFormation, atRightDomain, atRightBody] at atRightLambda
  subst leftLambda rightLambda
  exact (traceFunctionRelated_graph_iff _ _ inputRelation outputRelation _ _).mpr
    bodiesRelated

/-- Application elimination preserves a relation between the *assembled*
function values at related, admitted arguments. The function terms and their
certificates are arbitrary: they need not be lambda introductions. -/
theorem assembled_applications_related
    (leftA rightA : Tm Head n) (leftB rightB : Tm Head (n + 1))
    (leftFunction rightFunction leftArgument rightArgument : Tm Head n)
    (leftFunctionCode rightFunctionCode leftArgumentCode rightArgumentCode :
      Code Head ConversionCode n)
    (leftFunctionMeaning rightFunctionMeaning leftArg rightArg leftResult rightResult :
      Meaning.{u} n)
    (atLeftFunction : assemble heads constants leftFunctionCode leftFunction
      (.pi leftA leftB) = some leftFunctionMeaning)
    (atRightFunction : assemble heads constants rightFunctionCode rightFunction
      (.pi rightA rightB) = some rightFunctionMeaning)
    (atLeftArgument : assemble heads constants leftArgumentCode leftArgument leftA = some leftArg)
    (atRightArgument : assemble heads constants rightArgumentCode rightArgument rightA = some rightArg)
    (atLeftResult : assemble heads constants
      (.appElim leftA leftB leftFunctionCode leftArgumentCode)
      (.app leftFunction leftArgument) (inst0 leftArgument leftB) = some leftResult)
    (atRightResult : assemble heads constants
      (.appElim rightA rightB rightFunctionCode rightArgumentCode)
      (.app rightFunction rightArgument) (inst0 rightArgument rightB) = some rightResult)
    (leftEnv rightEnv : Environment.{u} n) (leftDomain rightDomain : ZFSet.{u})
    (inputRelation outputRelation : ZFSet.{u} → ZFSet.{u} → Prop)
    (functionsRelated : TraceFunctionRelated leftDomain rightDomain
      inputRelation outputRelation (leftFunctionMeaning.value leftEnv)
      (rightFunctionMeaning.value rightEnv))
    (leftInside : leftArg.value leftEnv ∈ leftDomain)
    (rightInside : rightArg.value rightEnv ∈ rightDomain)
    (argumentsRelated : inputRelation (leftArg.value leftEnv) (rightArg.value rightEnv)) :
    outputRelation (leftResult.value leftEnv) (rightResult.value rightEnv) := by
  simp only [assemble, atLeftFunction, atLeftArgument] at atLeftResult
  simp only [assemble, atRightFunction, atRightArgument] at atRightResult
  cases Option.some.inj atLeftResult
  cases Option.some.inj atRightResult
  exact functionsRelated _ leftInside _ rightInside argumentsRelated

/-- The older same-domain equality law follows from the relational
introduction rule once its two actual domains are identified. -/
theorem assembled_lambdas_eq_of_related
    (leftLevel rightLevel : Head) (leftA rightA : Tm Head n)
    (leftB rightB leftBody rightBody : Tm Head (n + 1))
    (leftFormation rightFormation : Code Head ConversionCode n)
    (leftBodyCode rightBodyCode : Code Head ConversionCode (n + 1))
    (leftFormed rightFormed leftLambda rightLambda : Meaning.{u} n)
    (leftBodyMeaning rightBodyMeaning : Meaning.{u} (n + 1))
    (leftDomain rightDomain : Value.{u} n)
    (atLeftFormation : assemble heads constants leftFormation (.pi leftA leftB)
      (.head leftLevel) = some leftFormed)
    (atRightFormation : assemble heads constants rightFormation (.pi rightA rightB)
      (.head rightLevel) = some rightFormed)
    (atLeftDomain : leftFormed.productDomain? = some leftDomain)
    (atRightDomain : rightFormed.productDomain? = some rightDomain)
    (atLeftBody : assemble heads constants leftBodyCode leftBody leftB = some leftBodyMeaning)
    (atRightBody : assemble heads constants rightBodyCode rightBody rightB = some rightBodyMeaning)
    (atLeftLambda : assemble heads constants (.lamIntro leftLevel leftFormation leftBodyCode)
      (.lam leftBody) (.pi leftA leftB) = some leftLambda)
    (atRightLambda : assemble heads constants (.lamIntro rightLevel rightFormation rightBodyCode)
      (.lam rightBody) (.pi rightA rightB) = some rightLambda)
    (leftEnv rightEnv : Environment.{u} n)
    (domainsEqual : leftDomain leftEnv = rightDomain rightEnv)
    (bodiesEqual : ∀ x ∈ leftDomain leftEnv,
      leftBodyMeaning.value (extend leftEnv x) =
        rightBodyMeaning.value (extend rightEnv x)) :
    leftLambda.value leftEnv = rightLambda.value rightEnv := by
  have related := assembled_lambdas_related heads constants leftLevel rightLevel
    leftA rightA leftB rightB leftBody rightBody leftFormation rightFormation
    leftBodyCode rightBodyCode leftFormed rightFormed leftLambda rightLambda
    leftBodyMeaning rightBodyMeaning leftDomain rightDomain atLeftFormation
    atRightFormation atLeftDomain atRightDomain atLeftBody atRightBody
    atLeftLambda atRightLambda leftEnv rightEnv Eq Eq
    (by intro x hx y _ equal; subst y; exact bodiesEqual x hx)
  simp [assemble, atLeftFormation, atLeftDomain, atLeftBody] at atLeftLambda
  simp [assemble, atRightFormation, atRightDomain, atRightBody] at atRightLambda
  subst leftLambda rightLambda
  change TraceFunctionRelated (leftDomain leftEnv) (rightDomain rightEnv) Eq Eq
    (traceLam (graph (leftDomain leftEnv)
      (fun x => leftBodyMeaning.value (extend leftEnv x))))
    (traceLam (graph (rightDomain rightEnv)
      (fun x => rightBodyMeaning.value (extend rightEnv x)))) at related
  change traceLam (graph (leftDomain leftEnv)
    (fun x => leftBodyMeaning.value (extend leftEnv x))) =
    traceLam (graph (rightDomain rightEnv)
      (fun x => rightBodyMeaning.value (extend rightEnv x)))
  rw [domainsEqual]
  exact traceLam_graph_eq_of_related_eq (rightDomain rightEnv)
    (fun x => leftBodyMeaning.value (extend leftEnv x))
    (fun x => rightBodyMeaning.value (extend rightEnv x)) (by
      simpa only [domainsEqual] using related)

#print axioms assembled_lambdas_related
#print axioms assembled_applications_related
#print axioms assembled_lambdas_eq_of_related

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
