import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedBetaPath
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputedFamilyComparison

/-!
# Dependent families after finite qualified computations

Two independently checked computations may have different source terms,
typing certificates, and intermediate lambda domains. If their retained
qualified paths meet at one neutral term, their values agree on valid
environments. Actual certificate instantiation then compares their dependent
family instances. This makes no normalization claim outside those paths.
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
variable (successor : Head → Head) (universes : FormationSensitive.UniverseRegularity R)
variable (successorQualified : ∀ level, R.isUniverse level →
  R.isUniverse (successor level) ∧ R.headTyping level (successor level))
variable (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)

include universes successorQualified model constantModel

/-- Agreement of two finite, independently checked computations survives
substitution into two independently checked dependent families. The output
certificates are computed by the existing instantiation operation. -/
theorem qualified_paths_family_values
    {context : Ctx Head n} {A leftTerm rightTerm terminalTerm : Tm Head n}
    (contextCode : ContextCode Head NoConversion n)
    (leftCode rightCode leftTerminal rightTerminal : Code Head NoConversion n)
    (leftPath : QualifiedBetaPath R successor contextCode A
      leftTerm leftCode terminalTerm leftTerminal)
    (rightPath : QualifiedBetaPath R successor contextCode A
      rightTerm rightCode terminalTerm rightTerminal)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (leftChecked : check R noConversionCheck context leftTerm A leftCode = true)
    (rightChecked : check R noConversionCheck context rightTerm A rightCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (left right : Meaning.{u} n)
    (atLeft : assemble heads constants leftCode leftTerm A = some left)
    (atRight : assemble heads constants rightCode rightTerm A = some right)
    (family : Tm Head (n + 1)) (leftLevel rightLevel : Head)
    (leftFamily rightFamily : Code Head NoConversion (n + 1))
    (leftFamilyChecked : check R noConversionCheck (.snoc context A)
      family (.head leftLevel) leftFamily = true)
    (rightFamilyChecked : check R noConversionCheck (.snoc context A)
      family (.head rightLevel) rightFamily = true)
    (familyQualified : leftFamily.neutralEliminations family (.head leftLevel) = true) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head leftLevel) leftTerm leftFamily leftCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head rightLevel) rightTerm rightFamily rightCode
    check R noConversionCheck context (inst0 leftTerm family) (.head leftLevel) leftFormation = true ∧
      check R noConversionCheck context (inst0 rightTerm family) (.head rightLevel) rightFormation = true ∧
      ∃ leftResult rightResult,
        assemble heads constants leftFormation (inst0 leftTerm family) (.head leftLevel) =
          some leftResult ∧
        assemble heads constants rightFormation (inst0 rightTerm family) (.head rightLevel) =
          some rightResult ∧
        ∀ env, valid env → leftResult.value env = rightResult.value env := by
  exact computed_arguments_family_values heads constants R leftCode rightCode left right
    leftChecked rightChecked atLeft atRight
    (fun env admitted => qualified_paths_common_terminal_values heads constants R successor
      universes successorQualified model constantModel contextCode leftPath rightPath
      contextChecked leftChecked rightChecked atContext left right atLeft atRight env admitted)
    family leftLevel rightLevel leftFamily rightFamily leftFamilyChecked rightFamilyChecked
    familyQualified

/-- The two checked dependent types also define the same space of valid
extended environments. Equality is semantic, not equality of raw types or
generated certificates. -/
theorem qualified_paths_family_contexts
    {context : Ctx Head n} {A leftTerm rightTerm terminalTerm : Tm Head n}
    (contextCode : ContextCode Head NoConversion n)
    (leftCode rightCode leftTerminal rightTerminal : Code Head NoConversion n)
    (leftPath : QualifiedBetaPath R successor contextCode A
      leftTerm leftCode terminalTerm leftTerminal)
    (rightPath : QualifiedBetaPath R successor contextCode A
      rightTerm rightCode terminalTerm rightTerminal)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (leftChecked : check R noConversionCheck context leftTerm A leftCode = true)
    (rightChecked : check R noConversionCheck context rightTerm A rightCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (left right : Meaning.{u} n)
    (atLeft : assemble heads constants leftCode leftTerm A = some left)
    (atRight : assemble heads constants rightCode rightTerm A = some right)
    (family : Tm Head (n + 1)) (leftLevel rightLevel : Head)
    (leftLevelUniverse : R.isUniverse leftLevel)
    (rightLevelUniverse : R.isUniverse rightLevel)
    (leftFamily rightFamily : Code Head NoConversion (n + 1))
    (leftFamilyChecked : check R noConversionCheck (.snoc context A)
      family (.head leftLevel) leftFamily = true)
    (rightFamilyChecked : check R noConversionCheck (.snoc context A)
      family (.head rightLevel) rightFamily = true)
    (familyQualified : leftFamily.neutralEliminations family (.head leftLevel) = true) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head leftLevel) leftTerm leftFamily leftCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head rightLevel) rightTerm rightFamily rightCode
    checkContext R noConversionCheck (.snoc context (inst0 leftTerm family))
      (.snoc contextCode leftLevel leftFormation) = true ∧
    checkContext R noConversionCheck (.snoc context (inst0 rightTerm family))
      (.snoc contextCode rightLevel rightFormation) = true ∧
    ∃ leftValid rightValid,
      assembleContext heads constants (.snoc contextCode leftLevel leftFormation)
        (.snoc context (inst0 leftTerm family)) = some leftValid ∧
      assembleContext heads constants (.snoc contextCode rightLevel rightFormation)
        (.snoc context (inst0 rightTerm family)) = some rightValid ∧
      leftValid = rightValid := by
  exact computed_arguments_family_contexts heads constants R contextCode leftCode rightCode
    left right contextChecked atContext leftChecked rightChecked atLeft atRight
    (fun env admitted => qualified_paths_common_terminal_values heads constants R successor
      universes successorQualified model constantModel contextCode leftPath rightPath
      contextChecked leftChecked rightChecked atContext left right atLeft atRight env admitted)
    family leftLevel rightLevel leftLevelUniverse rightLevelUniverse leftFamily rightFamily
    leftFamilyChecked rightFamilyChecked familyQualified

#print axioms qualified_paths_family_values
#print axioms qualified_paths_family_contexts

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
