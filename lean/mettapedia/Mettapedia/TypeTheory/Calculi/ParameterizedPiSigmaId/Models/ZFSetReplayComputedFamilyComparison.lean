import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContextComparison

/-!
# Dependent families of independently checked computed values

Actual certificate instantiation transports a family across two computations.
The family certificates are compared before substitution, where the first
certificate still satisfies the neutral-elimination qualification. The
substituted family expressions and their certificates need not be neutral.

The general congruence law takes equality of the two argument values on valid
environments as an explicit premise. The beta specialization below derives
that premise from two checked, qualified source certificates and a checked
neutral reduct. No type conversion is added to the no-conversion checker.
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

/-- A comparison of two checked argument values induces a comparison of
independently checked dependent family instances. Both output certificates
are the ones produced by the existing substitution algorithm. -/
theorem computed_arguments_family_values
    {context : Ctx Head n} {A leftArgument rightArgument : Tm Head n}
    (leftCode rightCode : Code Head NoConversion n)
    (leftArgumentMeaning rightArgumentMeaning : Meaning.{u} n)
    (leftChecked : check R noConversionCheck context leftArgument A leftCode = true)
    (rightChecked : check R noConversionCheck context rightArgument A rightCode = true)
    (atLeftArgument : assemble heads constants leftCode leftArgument A = some leftArgumentMeaning)
    (atRightArgument : assemble heads constants rightCode rightArgument A = some rightArgumentMeaning)
    {valid : Environment.{u} n → Prop}
    (argumentAgreement : ∀ env, valid env →
      leftArgumentMeaning.value env = rightArgumentMeaning.value env)
    (family : Tm Head (n + 1)) (leftLevel rightLevel : Head)
    (leftFamily rightFamily : Code Head NoConversion (n + 1))
    (leftFamilyChecked : check R noConversionCheck (.snoc context A)
      family (.head leftLevel) leftFamily = true)
    (rightFamilyChecked : check R noConversionCheck (.snoc context A)
      family (.head rightLevel) rightFamily = true)
    (familyQualified : leftFamily.neutralEliminations family (.head leftLevel) = true) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head leftLevel) leftArgument leftFamily leftCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head rightLevel) rightArgument rightFamily rightCode
    check R noConversionCheck context (inst0 leftArgument family) (.head leftLevel) leftFormation = true ∧
      check R noConversionCheck context (inst0 rightArgument family) (.head rightLevel) rightFormation = true ∧
      ∃ left right,
        assemble heads constants leftFormation (inst0 leftArgument family) (.head leftLevel) = some left ∧
        assemble heads constants rightFormation (inst0 rightArgument family) (.head rightLevel) = some right ∧
        ∀ env, valid env → left.value env = right.value env := by
  dsimp only
  have leftFormationChecked := Code.instantiate_checked noConversionRename noConversionSubstitute
    R noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) leftFamilyChecked leftChecked
  have rightFormationChecked := Code.instantiate_checked noConversionRename noConversionSubstitute
    R noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) rightFamilyChecked rightChecked
  obtain ⟨leftFamilyMeaning, atLeftFamily, _⟩ :=
    accepted_assembles heads constants R noConversionCheck leftFamily leftFamilyChecked
  obtain ⟨rightFamilyMeaning, atRightFamily, _⟩ :=
    accepted_assembles heads constants R noConversionCheck rightFamily rightFamilyChecked
  have familyAgreement := assemble_neutralEliminations_coherent heads constants R leftFamily
    leftFamilyChecked familyQualified atLeftFamily rightFamilyChecked atRightFamily
    (EqualOrHeads.heads _ _)
  obtain ⟨left, atLeft, leftValues⟩ := assemble_instantiate noConversionRename noConversionSubstitute
    heads constants R noConversionCheck leftFamily leftCode leftFamilyMeaning leftArgumentMeaning
      leftFamilyChecked atLeftFamily atLeftArgument
  obtain ⟨right, atRight, rightValues⟩ := assemble_instantiate noConversionRename noConversionSubstitute
    heads constants R noConversionCheck rightFamily rightCode rightFamilyMeaning rightArgumentMeaning
      rightFamilyChecked atRightFamily atRightArgument
  refine ⟨leftFormationChecked, rightFormationChecked, left, right, atLeft, atRight, ?_⟩
  intro env admitted
  rw [leftValues, rightValues, familyAgreement, argumentAgreement env admitted]

/-- The two checked family instances give the same valid extended context,
even when their raw last types and retained certificates differ. -/
theorem computed_arguments_family_contexts
    {context : Ctx Head n} {A leftArgument rightArgument : Tm Head n}
    (contextCode : ContextCode Head NoConversion n)
    (leftCode rightCode : Code Head NoConversion n)
    (leftArgumentMeaning rightArgumentMeaning : Meaning.{u} n)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (leftChecked : check R noConversionCheck context leftArgument A leftCode = true)
    (rightChecked : check R noConversionCheck context rightArgument A rightCode = true)
    (atLeftArgument : assemble heads constants leftCode leftArgument A = some leftArgumentMeaning)
    (atRightArgument : assemble heads constants rightCode rightArgument A = some rightArgumentMeaning)
    (argumentAgreement : ∀ env, valid env →
      leftArgumentMeaning.value env = rightArgumentMeaning.value env)
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
      family (.head leftLevel) leftArgument leftFamily leftCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head rightLevel) rightArgument rightFamily rightCode
    checkContext R noConversionCheck (.snoc context (inst0 leftArgument family))
      (.snoc contextCode leftLevel leftFormation) = true ∧
      checkContext R noConversionCheck (.snoc context (inst0 rightArgument family))
        (.snoc contextCode rightLevel rightFormation) = true ∧
      ∃ leftValid rightValid,
        assembleContext heads constants (.snoc contextCode leftLevel leftFormation)
          (.snoc context (inst0 leftArgument family)) = some leftValid ∧
        assembleContext heads constants (.snoc contextCode rightLevel rightFormation)
          (.snoc context (inst0 rightArgument family)) = some rightValid ∧
        leftValid = rightValid := by
  dsimp only
  obtain ⟨leftChecked', rightChecked', left, right, atLeft, atRight, equal⟩ :=
    computed_arguments_family_values heads constants R leftCode rightCode
      leftArgumentMeaning rightArgumentMeaning leftChecked rightChecked atLeftArgument
      atRightArgument argumentAgreement family leftLevel rightLevel leftFamily rightFamily
      leftFamilyChecked rightFamilyChecked familyQualified
  refine ⟨?_, ?_,
    (fun env => valid (env ∘ wk) ∧ env 0 ∈ left.value (env ∘ wk)),
    (fun env => valid (env ∘ wk) ∧ env 0 ∈ right.value (env ∘ wk)), ?_, ?_, ?_⟩
  · simpa only [checkContext, Bool.and_eq_true, decide_eq_true_eq] using
      And.intro (And.intro contextChecked leftLevelUniverse) leftChecked'
  · simpa only [checkContext, Bool.and_eq_true, decide_eq_true_eq] using
      And.intro (And.intro contextChecked rightLevelUniverse) rightChecked'
  · simp only [assembleContext, atContext, atLeft, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]
  · simp only [assembleContext, atContext, atRight, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]
  · apply assembleContext_extensions_eq heads constants context context
      (inst0 leftArgument family) (inst0 rightArgument family) contextCode contextCode
      leftLevel rightLevel _ _ valid valid left right _ _ atContext atContext atLeft atRight
    · simp only [assembleContext, atContext, atLeft, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def]
    · simp only [assembleContext, atContext, atRight, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def]
    · exact fun _ => Iff.rfl
    · exact equal

variable (successor : Head → Head) (universes : FormationSensitive.UniverseRegularity R)
variable (successorQualified : ∀ level, R.isUniverse level →
  R.isUniverse (successor level) ∧ R.headTyping level (successor level))
variable (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)

include universes successorQualified model constantModel

/-- Two independently checked beta certificates can be substituted into
independently checked families. The intermediate lambda domains may differ;
agreement is earned through an independently checked neutral reduct. -/
theorem qualified_rootBeta_family_values
    {context : Ctx Head n} {body : Tm Head (n + 1)} {argument A : Tm Head n}
    (contextCode : ContextCode Head NoConversion n)
    (leftCode rightCode normalCode : Code Head NoConversion n)
    (left right normal : Meaning.{u} n) {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (leftChecked : check R noConversionCheck context (.app (.lam body) argument) A leftCode = true)
    (rightChecked : check R noConversionCheck context (.app (.lam body) argument) A rightCode = true)
    (leftQualified : leftCode.resultFormationsNeutral R successor contextCode
      (.app (.lam body) argument) A = true)
    (rightQualified : rightCode.resultFormationsNeutral R successor contextCode
      (.app (.lam body) argument) A = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (atLeft : assemble heads constants leftCode (.app (.lam body) argument) A = some left)
    (atRight : assemble heads constants rightCode (.app (.lam body) argument) A = some right)
    (normalChecked : check R noConversionCheck context (inst0 argument body) A normalCode = true)
    (normalQualified : normalCode.neutralEliminations (inst0 argument body) A = true)
    (atNormal : assemble heads constants normalCode (inst0 argument body) A = some normal)
    (family : Tm Head (n + 1)) (leftLevel rightLevel : Head)
    (leftFamily rightFamily : Code Head NoConversion (n + 1))
    (leftFamilyChecked : check R noConversionCheck (.snoc context A)
      family (.head leftLevel) leftFamily = true)
    (rightFamilyChecked : check R noConversionCheck (.snoc context A)
      family (.head rightLevel) rightFamily = true)
    (familyQualified : leftFamily.neutralEliminations family (.head leftLevel) = true) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head leftLevel) (.app (.lam body) argument) leftFamily leftCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head rightLevel) (.app (.lam body) argument) rightFamily rightCode
    check R noConversionCheck context (inst0 (.app (.lam body) argument) family)
        (.head leftLevel) leftFormation = true ∧
      check R noConversionCheck context (inst0 (.app (.lam body) argument) family)
        (.head rightLevel) rightFormation = true ∧
      ∃ leftResult rightResult,
        assemble heads constants leftFormation (inst0 (.app (.lam body) argument) family)
          (.head leftLevel) = some leftResult ∧
        assemble heads constants rightFormation (inst0 (.app (.lam body) argument) family)
          (.head rightLevel) = some rightResult ∧
        ∀ env, valid env → leftResult.value env = rightResult.value env := by
  exact computed_arguments_family_values heads constants R leftCode rightCode left right
    leftChecked rightChecked atLeft atRight
    (fun env admitted => qualified_rootBeta_coherent heads constants R successor universes
      successorQualified model constantModel contextCode leftCode rightCode normalCode
      left right normal contextChecked leftChecked rightChecked leftQualified rightQualified
      atContext atLeft atRight normalChecked normalQualified atNormal env admitted)
    family leftLevel rightLevel leftFamily rightFamily leftFamilyChecked rightFamilyChecked
    familyQualified

/-- The dependent contexts formed from two independently checked beta
certificates admit exactly the same environments. The result retains both
actual generated family certificates and context checks; it is not an
implicit conversion between their raw last-type expressions. -/
theorem qualified_rootBeta_family_contexts
    {context : Ctx Head n} {body : Tm Head (n + 1)} {argument A : Tm Head n}
    (contextCode : ContextCode Head NoConversion n)
    (leftCode rightCode normalCode : Code Head NoConversion n)
    (left right normal : Meaning.{u} n) {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (leftChecked : check R noConversionCheck context (.app (.lam body) argument) A leftCode = true)
    (rightChecked : check R noConversionCheck context (.app (.lam body) argument) A rightCode = true)
    (leftQualified : leftCode.resultFormationsNeutral R successor contextCode
      (.app (.lam body) argument) A = true)
    (rightQualified : rightCode.resultFormationsNeutral R successor contextCode
      (.app (.lam body) argument) A = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (atLeft : assemble heads constants leftCode (.app (.lam body) argument) A = some left)
    (atRight : assemble heads constants rightCode (.app (.lam body) argument) A = some right)
    (normalChecked : check R noConversionCheck context (inst0 argument body) A normalCode = true)
    (normalQualified : normalCode.neutralEliminations (inst0 argument body) A = true)
    (atNormal : assemble heads constants normalCode (inst0 argument body) A = some normal)
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
      family (.head leftLevel) (.app (.lam body) argument) leftFamily leftCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head rightLevel) (.app (.lam body) argument) rightFamily rightCode
    checkContext R noConversionCheck (.snoc context (inst0 (.app (.lam body) argument) family))
      (.snoc contextCode leftLevel leftFormation) = true ∧
    checkContext R noConversionCheck (.snoc context (inst0 (.app (.lam body) argument) family))
      (.snoc contextCode rightLevel rightFormation) = true ∧
    ∃ leftValid rightValid,
      assembleContext heads constants (.snoc contextCode leftLevel leftFormation)
        (.snoc context (inst0 (.app (.lam body) argument) family)) = some leftValid ∧
      assembleContext heads constants (.snoc contextCode rightLevel rightFormation)
        (.snoc context (inst0 (.app (.lam body) argument) family)) = some rightValid ∧
      leftValid = rightValid := by
  exact computed_arguments_family_contexts heads constants R contextCode leftCode rightCode
    left right contextChecked atContext leftChecked rightChecked atLeft atRight
    (fun env admitted => qualified_rootBeta_coherent heads constants R successor universes
      successorQualified model constantModel contextCode leftCode rightCode normalCode
      left right normal contextChecked leftChecked rightChecked leftQualified rightQualified
      atContext atLeft atRight normalChecked normalQualified atNormal env admitted)
    family leftLevel rightLevel leftLevelUniverse rightLevelUniverse leftFamily rightFamily
    leftFamilyChecked rightFamilyChecked familyQualified

#print axioms computed_arguments_family_values
#print axioms computed_arguments_family_contexts
#print axioms qualified_rootBeta_family_values
#print axioms qualified_rootBeta_family_contexts

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
