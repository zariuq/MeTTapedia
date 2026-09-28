import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayFunctionRelations

/-!
# Substitution of checked, domain-indexed function observations

The actual certificate-substitution algorithm transports both accepted
function evidence and its retained product formation. Consequently a
function relation is reindexed along the meanings of the supplied telescope
images, with the resulting domains still witnessed by the transformed
formation certificates. The two substitutions and contexts may differ.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts (TraceFunctionRelated)

universe u
variable {Head : Type} {ConversionCode : Nat → Type} {n m : Nat}
variable (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
variable (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)
variable (renamePreserves : ∀ {n m} (ρ : Ren n m) (code : ConversionCode n)
  {left right : Tm Head n}, conversionCheck code left right = true →
    conversionCheck (renameConversion ρ code) (Presentation.rename ρ left)
      (Presentation.rename ρ right) = true)
variable (substitutePreserves : ∀ {n m} (σ : Sub Head n m) (code : ConversionCode n)
  {left right : Tm Head n}, conversionCheck code left right = true →
    conversionCheck (substituteConversion σ code) (subst σ left) (subst σ right) = true)

include renamePreserves substitutePreserves in
/-- Substitution preserves a domain-indexed relation between *checked*
function values and simultaneously transports both product-domain receipts.
The output relation is only claimed at target environments whose actual
computed image environments satisfy the source relation. -/
theorem checked_function_relations_substitute
    (leftContext rightContext : Ctx Head n)
    (leftTarget rightTarget : Ctx Head m)
    (leftLevel rightLevel : Head)
    (leftA rightA : Tm Head n) (leftB rightB : Tm Head (n + 1))
    (leftFunction rightFunction : Tm Head n)
    (leftCode rightCode leftFormation rightFormation : Code Head ConversionCode n)
    (leftMeaning rightMeaning leftFormed rightFormed : Meaning.{u} n)
    (leftDomain rightDomain : Value.{u} n)
    (leftChecked : check R conversionCheck leftContext leftFunction
      (.pi leftA leftB) leftCode = true)
    (rightChecked : check R conversionCheck rightContext rightFunction
      (.pi rightA rightB) rightCode = true)
    (leftFormationChecked : check R conversionCheck leftContext (.pi leftA leftB)
      (.head leftLevel) leftFormation = true)
    (rightFormationChecked : check R conversionCheck rightContext (.pi rightA rightB)
      (.head rightLevel) rightFormation = true)
    (atLeft : assemble heads constants leftCode leftFunction (.pi leftA leftB) = some leftMeaning)
    (atRight : assemble heads constants rightCode rightFunction (.pi rightA rightB) = some rightMeaning)
    (atLeftFormation : assemble heads constants leftFormation (.pi leftA leftB)
      (.head leftLevel) = some leftFormed)
    (atRightFormation : assemble heads constants rightFormation (.pi rightA rightB)
      (.head rightLevel) = some rightFormed)
    (atLeftDomain : leftFormed.productDomain? = some leftDomain)
    (atRightDomain : rightFormed.productDomain? = some rightDomain)
    (leftSub rightSub : Sub Head n m)
    (leftCodes rightCodes : Fin n → Code Head ConversionCode m)
    (leftImages rightImages : Fin n → Meaning.{u} m)
    (leftImagesChecked : ∀ i, check R conversionCheck leftTarget (leftSub i)
      (subst leftSub (leftContext.lookup i)) (leftCodes i) = true)
    (rightImagesChecked : ∀ i, check R conversionCheck rightTarget (rightSub i)
      (subst rightSub (rightContext.lookup i)) (rightCodes i) = true)
    (atLeftImages : ∀ i, assemble heads constants (leftCodes i) (leftSub i)
      (subst leftSub (leftContext.lookup i)) = some (leftImages i))
    (atRightImages : ∀ i, assemble heads constants (rightCodes i) (rightSub i)
      (subst rightSub (rightContext.lookup i)) = some (rightImages i))
    (sourceRelation : Environment.{u} n → Environment.{u} n → Prop)
    (targetRelation : Environment.{u} m → Environment.{u} m → Prop)
    (inputRelation outputRelation : ZFSet.{u} → ZFSet.{u} → Prop)
    (sourceRelated : ∀ leftEnv rightEnv, sourceRelation leftEnv rightEnv →
      TraceFunctionRelated (leftDomain leftEnv) (rightDomain rightEnv)
        inputRelation outputRelation (leftMeaning.value leftEnv) (rightMeaning.value rightEnv))
    (imagesRelated : ∀ leftEnv rightEnv, targetRelation leftEnv rightEnv →
      sourceRelation (imageEnvironment leftImages leftEnv)
        (imageEnvironment rightImages rightEnv)) :
    check R conversionCheck leftTarget (subst leftSub leftFunction)
      (subst leftSub (.pi leftA leftB))
      (leftCode.substitute renameConversion substituteConversion leftSub leftCodes
        leftFunction (.pi leftA leftB)) = true ∧
    check R conversionCheck rightTarget (subst rightSub rightFunction)
      (subst rightSub (.pi rightA rightB))
      (rightCode.substitute renameConversion substituteConversion rightSub rightCodes
        rightFunction (.pi rightA rightB)) = true ∧
    check R conversionCheck leftTarget (subst leftSub (.pi leftA leftB))
      (subst leftSub (.head leftLevel))
      (leftFormation.substitute renameConversion substituteConversion leftSub leftCodes
        (.pi leftA leftB) (.head leftLevel)) = true ∧
    check R conversionCheck rightTarget (subst rightSub (.pi rightA rightB))
      (subst rightSub (.head rightLevel))
      (rightFormation.substitute renameConversion substituteConversion rightSub rightCodes
        (.pi rightA rightB) (.head rightLevel)) = true ∧
    ∃ leftResult rightResult leftResultFormation rightResultFormation,
      assemble heads constants
        (leftCode.substitute renameConversion substituteConversion leftSub leftCodes
          leftFunction (.pi leftA leftB))
        (subst leftSub leftFunction) (subst leftSub (.pi leftA leftB)) = some leftResult ∧
      assemble heads constants
        (rightCode.substitute renameConversion substituteConversion rightSub rightCodes
          rightFunction (.pi rightA rightB))
        (subst rightSub rightFunction) (subst rightSub (.pi rightA rightB)) = some rightResult ∧
      assemble heads constants
        (leftFormation.substitute renameConversion substituteConversion leftSub leftCodes
          (.pi leftA leftB) (.head leftLevel))
        (subst leftSub (.pi leftA leftB)) (subst leftSub (.head leftLevel)) =
          some leftResultFormation ∧
      assemble heads constants
        (rightFormation.substitute renameConversion substituteConversion rightSub rightCodes
          (.pi rightA rightB) (.head rightLevel))
        (subst rightSub (.pi rightA rightB)) (subst rightSub (.head rightLevel)) =
          some rightResultFormation ∧
      (∀ env, leftResult.value env =
        leftMeaning.value (imageEnvironment leftImages env)) ∧
      (∀ env, rightResult.value env =
        rightMeaning.value (imageEnvironment rightImages env)) ∧
      leftResultFormation.productDomain? =
        some (fun env => leftDomain (imageEnvironment leftImages env)) ∧
      rightResultFormation.productDomain? =
        some (fun env => rightDomain (imageEnvironment rightImages env)) ∧
      ∀ leftEnv rightEnv, targetRelation leftEnv rightEnv →
        TraceFunctionRelated
          (leftDomain (imageEnvironment leftImages leftEnv))
          (rightDomain (imageEnvironment rightImages rightEnv))
          inputRelation outputRelation
          (leftResult.value leftEnv) (rightResult.value rightEnv) := by
  have leftCodeChecked := check_substitute renameConversion substituteConversion R
    conversionCheck renamePreserves substitutePreserves leftCode leftChecked
    leftSub leftCodes leftImagesChecked
  have rightCodeChecked := check_substitute renameConversion substituteConversion R
    conversionCheck renamePreserves substitutePreserves rightCode rightChecked
    rightSub rightCodes rightImagesChecked
  have leftFormationAccepted := check_substitute renameConversion substituteConversion R
    conversionCheck renamePreserves substitutePreserves leftFormation leftFormationChecked
    leftSub leftCodes leftImagesChecked
  have rightFormationAccepted := check_substitute renameConversion substituteConversion R
    conversionCheck renamePreserves substitutePreserves rightFormation rightFormationChecked
    rightSub rightCodes rightImagesChecked
  obtain ⟨leftResult, rightResult, atLeftResult, atRightResult,
    leftValues, rightValues, related⟩ :=
    assemble_substitute_indexed_related renameConversion substituteConversion
      heads constants R conversionCheck leftContext rightContext leftFunction
      (.pi leftA leftB) rightFunction (.pi rightA rightB) leftCode rightCode
      leftMeaning rightMeaning leftChecked rightChecked atLeft atRight leftSub rightSub
      leftCodes rightCodes leftImages rightImages atLeftImages atRightImages
      sourceRelation targetRelation
      (fun leftEnv rightEnv => TraceFunctionRelated
        (leftDomain leftEnv) (rightDomain rightEnv) inputRelation outputRelation)
      sourceRelated imagesRelated
  obtain ⟨leftResultFormation, atLeftResultFormation, _, leftDomainMap⟩ :=
    assemble_substitute renameConversion substituteConversion heads constants R
      conversionCheck leftFormation leftFormed leftFormationChecked atLeftFormation
      leftSub leftCodes leftImages atLeftImages
  obtain ⟨rightResultFormation, atRightResultFormation, _, rightDomainMap⟩ :=
    assemble_substitute renameConversion substituteConversion heads constants R
      conversionCheck rightFormation rightFormed rightFormationChecked atRightFormation
      rightSub rightCodes rightImages atRightImages
  have leftDomainReceipt : leftResultFormation.productDomain? =
      some (fun env => leftDomain (imageEnvironment leftImages env)) := by
    simpa only [atLeftDomain, Option.map_some] using leftDomainMap leftA leftB rfl
  have rightDomainReceipt : rightResultFormation.productDomain? =
      some (fun env => rightDomain (imageEnvironment rightImages env)) := by
    simpa only [atRightDomain, Option.map_some] using rightDomainMap rightA rightB rfl
  exact ⟨leftCodeChecked, rightCodeChecked, leftFormationAccepted,
    rightFormationAccepted, leftResult, rightResult, leftResultFormation,
    rightResultFormation, atLeftResult, atRightResult, atLeftResultFormation,
    atRightResultFormation, leftValues, rightValues,
    leftDomainReceipt, rightDomainReceipt, related⟩

#print axioms checked_function_relations_substitute

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
