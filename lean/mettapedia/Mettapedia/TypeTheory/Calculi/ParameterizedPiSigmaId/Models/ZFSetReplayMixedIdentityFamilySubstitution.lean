import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputedFamilyComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIdentityComparison

/-!
# Computed substitution into a non-diagonal identity family

The left endpoint of the family contracts a beta redex; the right endpoint
may be a different neutral term. Two checked formations can retain different
certificates and lambda domains. Qualification of the actual left endpoint
trees supplies the beta argument admission needed for their comparison.
Substitution of two computed outer arguments then transports that comparison
to independently checked family instances on valid source environments.
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
variable (successor : Head → Head) (universes : FormationSensitive.UniverseRegularity R)
variable (successorQualified : ∀ level, R.isUniverse level →
  R.isUniverse (successor level) ∧ R.headTyping level (successor level))
variable (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)

include universes successorQualified model constantModel

/-- Two arbitrary checked outer argument expressions can be substituted into
independently certified, non-diagonal identity families. The left endpoint's
beta arguments are admitted by the qualified source trees, not by a new
semantic assumption. Comparison is restricted to valid source environments;
the two outer argument meanings must agree there. -/
theorem computed_arguments_mixed_identity_family_values
    {context : Ctx Head n} {A leftArgument rightArgument : Tm Head n}
    (contextCode : ContextCode Head NoConversion n)
    (valid : Environment.{u} n → Prop)
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (domainLevel : Head) (domainCode : Code Head NoConversion n)
    (domainMeaning : Meaning.{u} n)
    (domainUniverse : R.isUniverse domainLevel)
    (domainChecked : check R noConversionCheck context A (.head domainLevel) domainCode = true)
    (atDomain : assemble heads constants domainCode A (.head domainLevel) = some domainMeaning)
    (leftArgumentCode rightArgumentCode : Code Head NoConversion n)
    (leftArgumentMeaning rightArgumentMeaning : Meaning.{u} n)
    (leftArgumentChecked : check R noConversionCheck context leftArgument A leftArgumentCode = true)
    (rightArgumentChecked : check R noConversionCheck context rightArgument A rightArgumentCode = true)
    (leftArgumentQualified : leftArgumentCode.resultFormationsNeutral R successor
      contextCode leftArgument A = true)
    (atLeftArgument : assemble heads constants leftArgumentCode leftArgument A = some leftArgumentMeaning)
    (atRightArgument : assemble heads constants rightArgumentCode rightArgument A = some rightArgumentMeaning)
    (argumentAgreement : ∀ env, valid env →
      leftArgumentMeaning.value env = rightArgumentMeaning.value env)
    (carrier innerArgument rightEndpoint : Tm Head (n + 1))
    (leftBody : Tm Head (n + 1 + 1))
    (leftLevel rightLevel : Head)
    (leftCarrier rightCarrier leftBeta leftRight rightBeta rightRight normalCode :
      Code Head NoConversion (n + 1))
    (leftFamilyChecked : check R noConversionCheck (.snoc context A)
      (.id carrier (.app (.lam leftBody) innerArgument) rightEndpoint) (.head leftLevel)
      (.idForm leftLevel leftCarrier leftBeta leftRight) = true)
    (rightFamilyChecked : check R noConversionCheck (.snoc context A)
      (.id carrier (.app (.lam leftBody) innerArgument) rightEndpoint) (.head rightLevel)
      (.idForm rightLevel rightCarrier rightBeta rightRight) = true)
    (leftBetaQualified : leftBeta.resultFormationsNeutral R successor
      (.snoc contextCode domainLevel domainCode)
      (.app (.lam leftBody) innerArgument) carrier = true)
    (rightBetaQualified : rightBeta.resultFormationsNeutral R successor
      (.snoc contextCode domainLevel domainCode)
      (.app (.lam leftBody) innerArgument) carrier = true)
    (normalChecked : check R noConversionCheck (.snoc context A)
      (inst0 innerArgument leftBody) carrier normalCode = true)
    (normalNeutral : normalCode.neutralEliminations
      (inst0 innerArgument leftBody) carrier = true)
    (rightNeutral : leftRight.neutralEliminations rightEndpoint carrier = true) :
    let family := Tm.id carrier (.app (.lam leftBody) innerArgument) rightEndpoint
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head leftLevel) leftArgument
      (.idForm leftLevel leftCarrier leftBeta leftRight) leftArgumentCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head rightLevel) rightArgument
      (.idForm rightLevel rightCarrier rightBeta rightRight) rightArgumentCode
    check R noConversionCheck context (inst0 leftArgument family)
        (.head leftLevel) leftFormation = true ∧
      check R noConversionCheck context (inst0 rightArgument family)
        (.head rightLevel) rightFormation = true ∧
      ∃ left right,
        assemble heads constants leftFormation (inst0 leftArgument family)
          (.head leftLevel) = some left ∧
        assemble heads constants rightFormation (inst0 rightArgument family)
          (.head rightLevel) = some right ∧
        ∀ env, valid env → left.value env = right.value env := by
  dsimp only
  have leftFormationChecked := Code.instantiate_checked noConversionRename
    noConversionSubstitute R noConversionCheck
    (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) leftFamilyChecked leftArgumentChecked
  have rightFormationChecked := Code.instantiate_checked noConversionRename
    noConversionSubstitute R noConversionCheck
    (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) rightFamilyChecked rightArgumentChecked
  obtain ⟨leftFamilyMeaning, atLeftFamily, _⟩ := accepted_assembles heads constants R
    noConversionCheck (.idForm leftLevel leftCarrier leftBeta leftRight) leftFamilyChecked
  obtain ⟨rightFamilyMeaning, atRightFamily, _⟩ := accepted_assembles heads constants R
    noConversionCheck (.idForm rightLevel rightCarrier rightBeta rightRight) rightFamilyChecked
  obtain ⟨left, atLeft, leftValues⟩ := assemble_instantiate
    noConversionRename noConversionSubstitute heads constants R noConversionCheck
    (.idForm leftLevel leftCarrier leftBeta leftRight) leftArgumentCode
    leftFamilyMeaning leftArgumentMeaning leftFamilyChecked atLeftFamily atLeftArgument
  obtain ⟨right, atRight, rightValues⟩ := assemble_instantiate
    noConversionRename noConversionSubstitute heads constants R noConversionCheck
    (.idForm rightLevel rightCarrier rightBeta rightRight) rightArgumentCode
    rightFamilyMeaning rightArgumentMeaning rightFamilyChecked atRightFamily atRightArgument
  let extendedValid : Environment.{u} (n + 1) → Prop :=
    fun env => valid (env ∘ wk) ∧ env 0 ∈ domainMeaning.value (env ∘ wk)
  have extendedContextChecked : checkContext R noConversionCheck
      (.snoc context A) (.snoc contextCode domainLevel domainCode) = true := by
    simp [checkContext, contextChecked, domainUniverse, domainChecked]
  have atExtended : assembleContext heads constants
      (.snoc contextCode domainLevel domainCode) (.snoc context A) =
      some extendedValid := by
    simp [assembleContext, atContext, atDomain, extendedValid]
  obtain ⟨leftBetaChecked, _⟩ := identity_endpoint_checks R
    (.idForm leftLevel leftCarrier leftBeta leftRight) leftLevel
    leftCarrier leftBeta leftRight .hole leftFamilyChecked rfl
  obtain ⟨rightBetaChecked, _⟩ := identity_endpoint_checks R
    (.idForm rightLevel rightCarrier rightBeta rightRight) rightLevel
    rightCarrier rightBeta rightRight .hole rightFamilyChecked rfl
  have leftMember : ∀ env, valid env →
      leftArgumentMeaning.value env ∈ domainMeaning.value env :=
    qualified_membership heads constants R successor universes successorQualified
      model constantModel leftArgumentCode contextCode contextChecked
      leftArgumentChecked leftArgumentQualified valid leftArgumentMeaning atContext
      atLeftArgument domainLevel domainCode domainMeaning domainChecked atDomain
  refine ⟨leftFormationChecked, rightFormationChecked, left, right, atLeft, atRight, ?_⟩
  intro env admitted
  have extAdmitted : extendedValid (extend env (leftArgumentMeaning.value env)) :=
    (context_extension_valid_iff heads constants context A contextCode
      domainLevel domainCode valid extendedValid domainMeaning atContext
      atDomain atExtended env (leftArgumentMeaning.value env)).mpr
        ⟨admitted, leftMember env admitted⟩
  have firstAdmitted := qualified_rootBeta_admitted heads constants R successor
    universes successorQualified model constantModel leftBeta
    (.snoc contextCode domainLevel domainCode) extendedContextChecked
    leftBetaChecked leftBetaQualified atExtended _ extAdmitted
  have secondAdmitted := qualified_rootBeta_admitted heads constants R successor
    universes successorQualified model constantModel rightBeta
    (.snoc contextCode domainLevel domainCode) extendedContextChecked
    rightBetaChecked rightBetaQualified atExtended _ extAdmitted
  have familyEqual := identity_rootBeta_left_neutral_right_coherent heads constants R
    (.idForm leftLevel leftCarrier leftBeta leftRight)
    (.idForm rightLevel rightCarrier rightBeta rightRight)
    leftBody innerArgument leftLevel rightLevel leftCarrier leftBeta leftRight
    rightCarrier rightBeta rightRight .hole .hole
    leftFamilyMeaning rightFamilyMeaning normalCode leftFamilyChecked rightFamilyChecked
    rfl rfl atLeftFamily atRightFamily normalChecked normalNeutral rightNeutral
    (extend env (leftArgumentMeaning.value env)) firstAdmitted secondAdmitted
  rw [leftValues, rightValues, ← argumentAgreement env admitted]
  exact familyEqual

#print axioms computed_arguments_mixed_identity_family_values

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
