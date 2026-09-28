import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedHigherOrderApplication
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputedFamilyComparison

/-!
# Dependent families after independently computed higher-order applications

Checked paths to common supported endpoints derive equality of two computed
functions and two computed arguments on valid environments. Their checked
applications therefore agree, and actual certificate instantiation carries
that agreement into an independently checked dependent family. The two raw
application result types must coincide syntactically; this theorem does not
add an implicit conversion rule or assert arbitrary certificate coherence.
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
variable (successor : Head → Head)

/-- Qualified paths *derive* the comparison needed by a dependent family.
Both function and argument may compute, their certificates and displayed
types may differ, and both family certificates are actual instantiations.
Only the common raw result-type equality and the family's neutral formation
qualification are supplied separately. -/
theorem qualified_higher_order_application_family_values
    (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)
    (universes : FormationSensitive.UniverseRegularity R)
    (successorQualified : ∀ level, R.isUniverse level →
      R.isUniverse (successor level) ∧ R.headTyping level (successor level))
    (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    (valid : Environment.{u} n → Prop)
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (leftA rightA : Tm Head n) (leftB rightB : Tm Head (n + 1))
    (leftFunction rightFunction leftArgument rightArgument : Meaning.{u} n)
    (functions : QualifiedImagePaths heads constants R successor context contextCode
      leftFunction rightFunction)
    (arguments : QualifiedImagePaths heads constants R successor context contextCode
      leftArgument rightArgument)
    (leftFunctionType : functions.leftDisplayed = .pi leftA leftB)
    (rightFunctionType : functions.rightDisplayed = .pi rightA rightB)
    (leftArgumentType : arguments.leftDisplayed = leftA)
    (rightArgumentType : arguments.rightDisplayed = rightA)
    (resultTypesEqual : inst0 arguments.leftTerm leftB = inst0 arguments.rightTerm rightB)
    (family : Tm Head (n + 1)) (leftLevel rightLevel : Head)
    (leftFamily rightFamily : Code Head NoConversion (n + 1))
    (leftFamilyChecked : check R noConversionCheck
      (.snoc context (inst0 arguments.leftTerm leftB)) family
      (.head leftLevel) leftFamily = true)
    (rightFamilyChecked : check R noConversionCheck
      (.snoc context (inst0 arguments.leftTerm leftB)) family
      (.head rightLevel) rightFamily = true)
    (familyQualified : leftFamily.neutralEliminations family (.head leftLevel) = true) :
    let leftApplication := Tm.app functions.leftTerm arguments.leftTerm
    let rightApplication := Tm.app functions.rightTerm arguments.rightTerm
    let leftCode := Code.appElim leftA leftB functions.leftCode arguments.leftCode
    let rightCode := Code.appElim rightA rightB functions.rightCode arguments.rightCode
    let leftInstance := Code.instantiate noConversionRename noConversionSubstitute
      family (.head leftLevel) leftApplication leftFamily leftCode
    let rightInstance := Code.instantiate noConversionRename noConversionSubstitute
      family (.head rightLevel) rightApplication rightFamily rightCode
    check R noConversionCheck context (inst0 leftApplication family)
      (.head leftLevel) leftInstance = true ∧
    check R noConversionCheck context (inst0 rightApplication family)
      (.head rightLevel) rightInstance = true ∧
    ∃ left right,
      assemble heads constants leftInstance (inst0 leftApplication family)
        (.head leftLevel) = some left ∧
      assemble heads constants rightInstance (inst0 rightApplication family)
        (.head rightLevel) = some right ∧
      ∀ env, valid env → left.value env = right.value env := by
  dsimp only
  obtain ⟨leftChecked, rightChecked, leftResult, rightResult,
      atLeftResult, atRightResult, resultsEqual⟩ :=
    qualified_higher_order_applications_agree heads constants R successor
      model constantModel universes successorQualified context contextCode valid
      contextChecked atContext leftA rightA leftB rightB
      leftFunction rightFunction leftArgument rightArgument functions arguments
      leftFunctionType rightFunctionType leftArgumentType rightArgumentType
  have rightCheckedAtCommonType : check R noConversionCheck context
      (.app functions.rightTerm arguments.rightTerm)
      (inst0 arguments.leftTerm leftB)
      (.appElim rightA rightB functions.rightCode arguments.rightCode) = true := by
    rw [resultTypesEqual]
    exact rightChecked
  have atRightCommonType : assemble heads constants
      (.appElim rightA rightB functions.rightCode arguments.rightCode)
      (.app functions.rightTerm arguments.rightTerm) (inst0 arguments.leftTerm leftB) =
      some rightResult := by
    rw [resultTypesEqual]
    exact atRightResult
  exact computed_arguments_family_values heads constants R
    (.appElim leftA leftB functions.leftCode arguments.leftCode)
    (.appElim rightA rightB functions.rightCode arguments.rightCode)
    leftResult rightResult leftChecked rightCheckedAtCommonType
    atLeftResult atRightCommonType resultsEqual family leftLevel rightLevel
    leftFamily rightFamily leftFamilyChecked rightFamilyChecked familyQualified

#print axioms qualified_higher_order_application_family_values

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
