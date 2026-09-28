import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayFunctionRelations

/-!
# Comparing applications with different retained domains

The two replay trees may supply different function domains, codomains and
typing certificates. Their applications are compared at arguments admitted
by the respective retained domains. A relation between bodies on such inputs
is enough; equality of the entire function graphs is not required.

The substitution results transport the comparison through the actual
certificate-instantiation and simultaneous-substitution algorithms. These
are compatibility laws with explicit local premises, not an assumption or a
proof that all accepted certificates are semantically coherent.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment extend)
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (graph mem_graph)
open ZFSetTraceProducts (traceLam)

universe u
variable {Head : Type} {ConversionCode : Nat → Type} {n m : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

/-- At equal retained domains, agreement of the bodies on that domain gives
equality of the actual lambda values. The premise only concerns admitted
arguments, not arbitrary raw extensions of the two environments. -/
theorem lambda_values_eq
    (leftLevel rightLevel : Head) (leftA rightA : Tm Head n)
    (leftB rightB leftBody rightBody : Tm Head (n + 1))
    (leftFormation rightFormation : Code Head ConversionCode n)
    (leftBodyCode rightBodyCode : Code Head ConversionCode (n + 1))
    (leftFormed rightFormed leftResult rightResult : Meaning.{u} n)
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
    (atLeftResult : assemble heads constants (.lamIntro leftLevel leftFormation leftBodyCode)
      (.lam leftBody) (.pi leftA leftB) = some leftResult)
    (atRightResult : assemble heads constants (.lamIntro rightLevel rightFormation rightBodyCode)
      (.lam rightBody) (.pi rightA rightB) = some rightResult)
    (leftEnv rightEnv : Environment.{u} n)
    (domainsEqual : leftDomain leftEnv = rightDomain rightEnv)
    (bodiesEqual : ∀ x ∈ leftDomain leftEnv,
      leftBodyMeaning.value (extend leftEnv x) = rightBodyMeaning.value (extend rightEnv x)) :
    leftResult.value leftEnv = rightResult.value rightEnv := by
  exact assembled_lambdas_eq_of_related heads constants leftLevel rightLevel
    leftA rightA leftB rightB leftBody rightBody leftFormation rightFormation
    leftBodyCode rightBodyCode leftFormed rightFormed leftResult rightResult
    leftBodyMeaning rightBodyMeaning leftDomain rightDomain atLeftFormation
    atRightFormation atLeftDomain atRightDomain atLeftBody atRightBody
    atLeftResult atRightResult leftEnv rightEnv domainsEqual bodiesEqual

/-- The two local beta laws transport an arbitrary relation on body results.
Neither equality of the retained domains nor equality of the input values is
required: the input relation states exactly which applications are compared. -/
theorem application_lambda_related
    (leftLevel rightLevel : Head) (leftA rightA : Tm Head n)
    (leftB rightB leftBody rightBody : Tm Head (n + 1))
    (leftArgument rightArgument : Tm Head n)
    (leftFormation rightFormation leftArgumentCode rightArgumentCode : Code Head ConversionCode n)
    (leftBodyCode rightBodyCode : Code Head ConversionCode (n + 1))
    (leftFormed rightFormed leftArg rightArg leftResult rightResult : Meaning.{u} n)
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
    (atLeftArgument : assemble heads constants leftArgumentCode leftArgument leftA = some leftArg)
    (atRightArgument : assemble heads constants rightArgumentCode rightArgument rightA = some rightArg)
    (atLeftResult : assemble heads constants
      (.appElim leftA leftB (.lamIntro leftLevel leftFormation leftBodyCode) leftArgumentCode)
      (.app (.lam leftBody) leftArgument) (inst0 leftArgument leftB) = some leftResult)
    (atRightResult : assemble heads constants
      (.appElim rightA rightB (.lamIntro rightLevel rightFormation rightBodyCode) rightArgumentCode)
      (.app (.lam rightBody) rightArgument) (inst0 rightArgument rightB) = some rightResult)
    (leftEnv rightEnv : Environment.{u} n)
    (inputRelation outputRelation : ZFSet.{u} → ZFSet.{u} → Prop)
    (leftInside : leftArg.value leftEnv ∈ leftDomain leftEnv)
    (rightInside : rightArg.value rightEnv ∈ rightDomain rightEnv)
    (argumentsRelated : inputRelation (leftArg.value leftEnv) (rightArg.value rightEnv))
    (bodiesRelated : ∀ x ∈ leftDomain leftEnv, ∀ y ∈ rightDomain rightEnv,
      inputRelation x y → outputRelation
        (leftBodyMeaning.value (extend leftEnv x)) (rightBodyMeaning.value (extend rightEnv y))) :
    outputRelation (leftResult.value leftEnv) (rightResult.value rightEnv) := by
  let leftFunction : Meaning.{u} n := .plain (fun env =>
    ZFSetTraceProducts.traceLam (graph (leftDomain env)
      (fun x => leftBodyMeaning.value (extend env x))))
  let rightFunction : Meaning.{u} n := .plain (fun env =>
    ZFSetTraceProducts.traceLam (graph (rightDomain env)
      (fun x => rightBodyMeaning.value (extend env x))))
  have atLeftFunction : assemble heads constants
      (.lamIntro leftLevel leftFormation leftBodyCode) (.lam leftBody) (.pi leftA leftB) =
      some leftFunction := by
    simp [assemble, atLeftFormation, atLeftDomain, atLeftBody, leftFunction]
  have atRightFunction : assemble heads constants
      (.lamIntro rightLevel rightFormation rightBodyCode) (.lam rightBody) (.pi rightA rightB) =
      some rightFunction := by
    simp [assemble, atRightFormation, atRightDomain, atRightBody, rightFunction]
  have functionsRelated := assembled_lambdas_related heads constants leftLevel rightLevel
    leftA rightA leftB rightB leftBody rightBody leftFormation rightFormation
    leftBodyCode rightBodyCode leftFormed rightFormed leftFunction rightFunction
    leftBodyMeaning rightBodyMeaning leftDomain rightDomain atLeftFormation
    atRightFormation atLeftDomain atRightDomain atLeftBody atRightBody
    atLeftFunction atRightFunction leftEnv rightEnv inputRelation outputRelation bodiesRelated
  exact assembled_applications_related heads constants leftA rightA leftB rightB
    (.lam leftBody) (.lam rightBody) leftArgument rightArgument
    (.lamIntro leftLevel leftFormation leftBodyCode)
    (.lamIntro rightLevel rightFormation rightBodyCode)
    leftArgumentCode rightArgumentCode leftFunction rightFunction leftArg rightArg
    leftResult rightResult atLeftFunction atRightFunction atLeftArgument atRightArgument
    atLeftResult atRightResult leftEnv rightEnv (leftDomain leftEnv) (rightDomain rightEnv)
    inputRelation outputRelation functionsRelated leftInside rightInside argumentsRelated

variable (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
variable (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)

/-- Independent substitutions preserve a source comparison when their actual
image meanings induce related environments. The two source contexts and
types may differ, and the image certificates are not identified. -/
theorem assemble_substitute_related
    (leftContext rightContext : Ctx Head n)
    (leftSubject leftType rightSubject rightType : Tm Head n)
    (leftCode rightCode : Code Head ConversionCode n) (left right : Meaning.{u} n)
    (leftChecked : check R conversionCheck leftContext leftSubject leftType leftCode = true)
    (rightChecked : check R conversionCheck rightContext rightSubject rightType rightCode = true)
    (atLeft : assemble heads constants leftCode leftSubject leftType = some left)
    (atRight : assemble heads constants rightCode rightSubject rightType = some right)
    (leftSub rightSub : Sub Head n m)
    (leftImages rightImages : Fin n → Code Head ConversionCode m)
    (leftMeanings rightMeanings : Fin n → Meaning.{u} m)
    (atLeftImages : ∀ i, assemble heads constants (leftImages i) (leftSub i)
      (subst leftSub (leftContext.lookup i)) = some (leftMeanings i))
    (atRightImages : ∀ i, assemble heads constants (rightImages i) (rightSub i)
      (subst rightSub (rightContext.lookup i)) = some (rightMeanings i))
    (sourceRelation : Environment.{u} n → Environment.{u} n → Prop)
    (targetRelation : Environment.{u} m → Environment.{u} m → Prop)
    (outputRelation : ZFSet.{u} → ZFSet.{u} → Prop)
    (sourcesRelated : ∀ leftEnv rightEnv, sourceRelation leftEnv rightEnv →
      outputRelation (left.value leftEnv) (right.value rightEnv))
    (imagesRelated : ∀ leftEnv rightEnv, targetRelation leftEnv rightEnv →
      sourceRelation (imageEnvironment leftMeanings leftEnv) (imageEnvironment rightMeanings rightEnv)) :
    ∃ leftResult rightResult,
      assemble heads constants
        (leftCode.substitute renameConversion substituteConversion leftSub leftImages leftSubject leftType)
        (subst leftSub leftSubject) (subst leftSub leftType) = some leftResult ∧
      assemble heads constants
        (rightCode.substitute renameConversion substituteConversion rightSub rightImages rightSubject rightType)
        (subst rightSub rightSubject) (subst rightSub rightType) = some rightResult ∧
      ∀ leftEnv rightEnv, targetRelation leftEnv rightEnv →
        outputRelation (leftResult.value leftEnv) (rightResult.value rightEnv) := by
  obtain ⟨leftResult, rightResult, atLeftResult, atRightResult, _, _, related⟩ :=
    assemble_substitute_indexed_related renameConversion substituteConversion
    heads constants R conversionCheck leftContext rightContext leftSubject leftType
    rightSubject rightType leftCode rightCode left right leftChecked rightChecked
    atLeft atRight leftSub rightSub leftImages rightImages leftMeanings rightMeanings
    atLeftImages atRightImages sourceRelation targetRelation
    (fun _ _ => outputRelation) sourcesRelated imagesRelated
  exact ⟨leftResult, rightResult, atLeftResult, atRightResult, related⟩

/-- Two independently instantiated bodies retain their relation. The target
need not use the same body certificate, argument certificate, domain or
codomain as the source. This includes type-family instantiation. -/
theorem assemble_instantiate_related
    (leftContext rightContext : Ctx Head n) (leftA rightA : Tm Head n)
    (leftBody leftB rightBody rightB : Tm Head (n + 1))
    (leftArgument rightArgument : Tm Head n)
    (leftBodyCode rightBodyCode : Code Head ConversionCode (n + 1))
    (leftArgumentCode rightArgumentCode : Code Head ConversionCode n)
    (leftBodyMeaning rightBodyMeaning : Meaning.{u} (n + 1)) (leftArg rightArg : Meaning.{u} n)
    (leftChecked : check R conversionCheck (.snoc leftContext leftA) leftBody leftB leftBodyCode = true)
    (rightChecked : check R conversionCheck (.snoc rightContext rightA) rightBody rightB rightBodyCode = true)
    (atLeftBody : assemble heads constants leftBodyCode leftBody leftB = some leftBodyMeaning)
    (atRightBody : assemble heads constants rightBodyCode rightBody rightB = some rightBodyMeaning)
    (atLeftArgument : assemble heads constants leftArgumentCode leftArgument leftA = some leftArg)
    (atRightArgument : assemble heads constants rightArgumentCode rightArgument rightA = some rightArg)
    (environments : Environment.{u} n → Environment.{u} n → Prop)
    (outputRelation : ZFSet.{u} → ZFSet.{u} → Prop)
    (related : ∀ leftEnv rightEnv, environments leftEnv rightEnv →
      outputRelation (leftBodyMeaning.value (extend leftEnv (leftArg.value leftEnv)))
        (rightBodyMeaning.value (extend rightEnv (rightArg.value rightEnv)))) :
    ∃ leftResult rightResult,
      assemble heads constants
        (Code.instantiate renameConversion substituteConversion leftBody leftB leftArgument
          leftBodyCode leftArgumentCode) (inst0 leftArgument leftBody) (inst0 leftArgument leftB) =
          some leftResult ∧
      assemble heads constants
        (Code.instantiate renameConversion substituteConversion rightBody rightB rightArgument
          rightBodyCode rightArgumentCode) (inst0 rightArgument rightBody) (inst0 rightArgument rightB) =
          some rightResult ∧
      ∀ leftEnv rightEnv, environments leftEnv rightEnv →
        outputRelation (leftResult.value leftEnv) (rightResult.value rightEnv) := by
  obtain ⟨leftResult, atLeft, leftValues⟩ :=
    assemble_instantiate renameConversion substituteConversion heads constants R conversionCheck
      leftBodyCode leftArgumentCode leftBodyMeaning leftArg leftChecked atLeftBody atLeftArgument
  obtain ⟨rightResult, atRight, rightValues⟩ :=
    assemble_instantiate renameConversion substituteConversion heads constants R conversionCheck
      rightBodyCode rightArgumentCode rightBodyMeaning rightArg rightChecked atRightBody atRightArgument
  refine ⟨leftResult, rightResult, atLeft, atRight, ?_⟩
  intro leftEnv rightEnv compatible
  rw [leftValues, rightValues]
  exact related leftEnv rightEnv compatible

#print axioms lambda_values_eq
#print axioms application_lambda_related
#print axioms assemble_substitute_related
#print axioms assemble_instantiate_related

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
