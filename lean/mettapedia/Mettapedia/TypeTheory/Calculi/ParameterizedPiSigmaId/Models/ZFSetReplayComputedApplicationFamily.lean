import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedApplicationComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputedFamilyComparison

/-!
# Dependent families of related checked applications

A domain-indexed relation compares two independently checked applications at
qualified computed arguments. When their outputs are equal and their displayed
result types are literally the same expression, actual certificate
instantiation carries this comparison into a dependent type family. The raw
result-type equality is explicit: semantic equality does not add a conversion
rule to the checker.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts (TraceFunctionRelated)

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (successor : Head → Head) (universes : FormationSensitive.UniverseRegularity R)
variable (successorQualified : ∀ level, R.isUniverse level →
  R.isUniverse (successor level) ∧ R.headTyping level (successor level))

include universes successorQualified in
/-- Two applications may have different functions, domains, arguments and
certificates. Qualified checking admits each computed argument to its own
retained domain; the function relation and argument relation then compare the
results. A checked family over their common raw result type transports that
comparison to both actual instantiated family certificates. -/
theorem qualified_computed_applications_family_values
    (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)
    (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    (valid : Environment.{u} n → Prop)
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (leftLevel rightLevel : Head) (leftA rightA : Tm Head n)
    (leftB rightB : Tm Head (n + 1))
    (leftFunction rightFunction leftArgument rightArgument : Tm Head n)
    (leftFormation rightFormation leftFunctionCode rightFunctionCode
      leftArgumentCode rightArgumentCode : Code Head NoConversion n)
    (leftFormed rightFormed leftFunctionMeaning rightFunctionMeaning
      leftArg rightArg leftResult rightResult : Meaning.{u} n)
    (leftDomain rightDomain : Value.{u} n)
    (leftFormationChecked : check R noConversionCheck context (.pi leftA leftB)
      (.head leftLevel) leftFormation = true)
    (rightFormationChecked : check R noConversionCheck context (.pi rightA rightB)
      (.head rightLevel) rightFormation = true)
    (leftApplicationChecked : check R noConversionCheck context
      (.app leftFunction leftArgument) (inst0 leftArgument leftB)
      (.appElim leftA leftB leftFunctionCode leftArgumentCode) = true)
    (rightApplicationChecked : check R noConversionCheck context
      (.app rightFunction rightArgument) (inst0 rightArgument rightB)
      (.appElim rightA rightB rightFunctionCode rightArgumentCode) = true)
    (leftArgumentQualified : leftArgumentCode.resultFormationsNeutral R successor
      contextCode leftArgument leftA = true)
    (rightArgumentQualified : rightArgumentCode.resultFormationsNeutral R successor
      contextCode rightArgument rightA = true)
    (atLeftFormation : assemble heads constants leftFormation (.pi leftA leftB)
      (.head leftLevel) = some leftFormed)
    (atRightFormation : assemble heads constants rightFormation (.pi rightA rightB)
      (.head rightLevel) = some rightFormed)
    (atLeftDomain : leftFormed.productDomain? = some leftDomain)
    (atRightDomain : rightFormed.productDomain? = some rightDomain)
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
    (resultTypesEqual : inst0 leftArgument leftB = inst0 rightArgument rightB)
    (argumentsEqual : ∀ env, valid env →
      leftArg.value env = rightArg.value env)
    (functionsRelated : ∀ env, valid env →
      TraceFunctionRelated (leftDomain env) (rightDomain env) Eq Eq
        (leftFunctionMeaning.value env) (rightFunctionMeaning.value env))
    (family : Tm Head (n + 1)) (leftFamilyLevel rightFamilyLevel : Head)
    (leftFamily rightFamily : Code Head NoConversion (n + 1))
    (leftFamilyChecked : check R noConversionCheck
      (.snoc context (inst0 leftArgument leftB)) family
      (.head leftFamilyLevel) leftFamily = true)
    (rightFamilyChecked : check R noConversionCheck
      (.snoc context (inst0 leftArgument leftB)) family
      (.head rightFamilyLevel) rightFamily = true)
    (familyQualified : leftFamily.neutralEliminations family
      (.head leftFamilyLevel) = true) :
    let leftApp := Tm.app leftFunction leftArgument
    let rightApp := Tm.app rightFunction rightArgument
    let leftAppCode := Code.appElim leftA leftB leftFunctionCode leftArgumentCode
    let rightAppCode := Code.appElim rightA rightB rightFunctionCode rightArgumentCode
    let leftInstance := Code.instantiate noConversionRename noConversionSubstitute
      family (.head leftFamilyLevel) leftApp leftFamily leftAppCode
    let rightInstance := Code.instantiate noConversionRename noConversionSubstitute
      family (.head rightFamilyLevel) rightApp rightFamily rightAppCode
    check R noConversionCheck context (inst0 leftApp family)
      (.head leftFamilyLevel) leftInstance = true ∧
    check R noConversionCheck context (inst0 rightApp family)
      (.head rightFamilyLevel) rightInstance = true ∧
    ∃ left right,
      assemble heads constants leftInstance (inst0 leftApp family)
        (.head leftFamilyLevel) = some left ∧
      assemble heads constants rightInstance (inst0 rightApp family)
        (.head rightFamilyLevel) = some right ∧
      ∀ env, valid env → left.value env = right.value env := by
  dsimp only
  have rightCheckedAtLeftType : check R noConversionCheck context
      (.app rightFunction rightArgument) (inst0 leftArgument leftB)
      (.appElim rightA rightB rightFunctionCode rightArgumentCode) = true := by
    rw [resultTypesEqual]
    exact rightApplicationChecked
  have rightAssembledAtLeftType : assemble heads constants
      (.appElim rightA rightB rightFunctionCode rightArgumentCode)
      (.app rightFunction rightArgument) (inst0 leftArgument leftB) = some rightResult := by
    rw [resultTypesEqual]
    exact atRightResult
  have outputsEqual : ∀ env, valid env →
      leftResult.value env = rightResult.value env := by
    intro env admitted
    exact qualified_computed_function_applications_related heads constants R successor
      universes successorQualified model constantModel context contextCode valid
      contextChecked atContext leftLevel rightLevel leftA rightA leftB rightB
      leftFunction rightFunction leftArgument rightArgument leftFormation rightFormation
      leftFunctionCode rightFunctionCode leftArgumentCode rightArgumentCode leftFormed
      rightFormed leftFunctionMeaning rightFunctionMeaning leftArg rightArg leftResult
      rightResult leftDomain rightDomain leftFormationChecked rightFormationChecked
      leftApplicationChecked rightApplicationChecked leftArgumentQualified
      rightArgumentQualified atLeftFormation atRightFormation atLeftDomain atRightDomain
      atLeftFunction atRightFunction atLeftArgument atRightArgument atLeftResult
      atRightResult env env admitted admitted Eq Eq (functionsRelated env admitted)
      (argumentsEqual env admitted)
  exact computed_arguments_family_values heads constants R
    (.appElim leftA leftB leftFunctionCode leftArgumentCode)
    (.appElim rightA rightB rightFunctionCode rightArgumentCode)
    leftResult rightResult leftApplicationChecked rightCheckedAtLeftType
    atLeftResult rightAssembledAtLeftType outputsEqual family leftFamilyLevel
    rightFamilyLevel leftFamily rightFamily leftFamilyChecked rightFamilyChecked
    familyQualified

#print axioms qualified_computed_applications_family_values

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
