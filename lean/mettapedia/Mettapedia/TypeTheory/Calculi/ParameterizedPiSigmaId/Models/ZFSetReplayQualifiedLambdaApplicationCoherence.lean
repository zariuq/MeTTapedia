import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedApplicationComparison

/-!
# Coherence of checked applications of a common dependent lambda

Two accepted certificates can retain different product formations, lambda
certificates and computed arguments. A qualified certificate for the common
body compares its interpretations; qualified paths to a common argument
terminal compare the computed inputs. Each argument's own qualified typing
tree proves membership in the product domain retained by its application.

This compares the results of the checked applications, not the whole lambda
values outside their retained domains. The terminal need not have a structural
interpretation, so an annotated lambda terminal is permitted.
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

/-- Independently checked applications of one dependent lambda agree when
their computed arguments follow qualified paths to one neutral terminal.
The product, body, and argument certificates may differ. The first body tree
is qualified; the second need only be accepted. -/
theorem qualified_common_lambda_applications_coherent
    (universes : FormationSensitive.UniverseRegularity R)
    (successorQualified : ∀ level, R.isUniverse level →
      R.isUniverse (successor level) ∧ R.headTyping level (successor level))
    (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)
    (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (A : Tm Head n) (B body : Tm Head (n + 1))
    (leftLevel rightLevel : Head)
    (leftUniverse : R.isUniverse leftLevel) (rightUniverse : R.isUniverse rightLevel)
    (leftFormation rightFormation leftArgumentCode rightArgumentCode : Code Head NoConversion n)
    (leftBodyCode rightBodyCode : Code Head NoConversion (n + 1))
    (leftArgument rightArgument terminal : Tm Head n)
    (leftTerminal rightTerminal : Code Head NoConversion n)
    (leftFormationChecked : check R noConversionCheck context (.pi A B)
      (.head leftLevel) leftFormation = true)
    (rightFormationChecked : check R noConversionCheck context (.pi A B)
      (.head rightLevel) rightFormation = true)
    (leftBodyChecked : check R noConversionCheck (.snoc context A) body B leftBodyCode = true)
    (rightBodyChecked : check R noConversionCheck (.snoc context A) body B rightBodyCode = true)
    (bodyQualified : leftBodyCode.neutralEliminations body B = true)
    (leftArgumentChecked : check R noConversionCheck context leftArgument A
      leftArgumentCode = true)
    (rightArgumentChecked : check R noConversionCheck context rightArgument A
      rightArgumentCode = true)
    (leftArgumentQualified : leftArgumentCode.resultFormationsNeutral R successor
      contextCode leftArgument A = true)
    (rightArgumentQualified : rightArgumentCode.resultFormationsNeutral R successor
      contextCode rightArgument A = true)
    (leftPath : QualifiedBetaPath R successor contextCode A leftArgument leftArgumentCode
      terminal leftTerminal)
    (rightPath : QualifiedBetaPath R successor contextCode A rightArgument rightArgumentCode
      terminal rightTerminal) :
    let leftCode := Code.appElim A B (.lamIntro leftLevel leftFormation leftBodyCode)
      leftArgumentCode
    let rightCode := Code.appElim A B (.lamIntro rightLevel rightFormation rightBodyCode)
      rightArgumentCode
    check R noConversionCheck context (.app (.lam body) leftArgument)
        (inst0 leftArgument B) leftCode = true ∧
      check R noConversionCheck context (.app (.lam body) rightArgument)
        (inst0 rightArgument B) rightCode = true ∧
      ∃ leftResult rightResult,
        assemble heads constants leftCode (.app (.lam body) leftArgument)
          (inst0 leftArgument B) = some leftResult ∧
        assemble heads constants rightCode (.app (.lam body) rightArgument)
          (inst0 rightArgument B) = some rightResult ∧
        ∀ env, valid env → leftResult.value env = rightResult.value env := by
  dsimp only
  have leftChecked : check R noConversionCheck context (.app (.lam body) leftArgument)
      (inst0 leftArgument B)
      (.appElim A B (.lamIntro leftLevel leftFormation leftBodyCode) leftArgumentCode) = true := by
    simp only [check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨leftUniverse, leftFormationChecked⟩, leftBodyChecked⟩,
      leftArgumentChecked⟩, True.intro⟩
  have rightChecked : check R noConversionCheck context (.app (.lam body) rightArgument)
      (inst0 rightArgument B)
      (.appElim A B (.lamIntro rightLevel rightFormation rightBodyCode) rightArgumentCode) = true := by
    simp only [check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨rightUniverse, rightFormationChecked⟩, rightBodyChecked⟩,
      rightArgumentChecked⟩, True.intro⟩
  obtain ⟨leftFormed, atLeftFormation, leftProduct⟩ :=
    accepted_assembles heads constants R noConversionCheck leftFormation leftFormationChecked
  obtain ⟨rightFormed, atRightFormation, rightProduct⟩ :=
    accepted_assembles heads constants R noConversionCheck rightFormation rightFormationChecked
  obtain ⟨leftDomain, atLeftDomain⟩ := leftProduct A B rfl
  obtain ⟨rightDomain, atRightDomain⟩ := rightProduct A B rfl
  obtain ⟨leftBody, atLeftBody, _⟩ :=
    accepted_assembles heads constants R noConversionCheck leftBodyCode leftBodyChecked
  obtain ⟨rightBody, atRightBody, _⟩ :=
    accepted_assembles heads constants R noConversionCheck rightBodyCode rightBodyChecked
  obtain ⟨leftArg, atLeftArgument, _⟩ :=
    accepted_assembles heads constants R noConversionCheck leftArgumentCode leftArgumentChecked
  obtain ⟨rightArg, atRightArgument, _⟩ :=
    accepted_assembles heads constants R noConversionCheck rightArgumentCode rightArgumentChecked
  obtain ⟨leftResult, atLeftResult, _⟩ := accepted_assembles heads constants R
    noConversionCheck (.appElim A B (.lamIntro leftLevel leftFormation leftBodyCode)
      leftArgumentCode) leftChecked
  obtain ⟨rightResult, atRightResult, _⟩ := accepted_assembles heads constants R
    noConversionCheck (.appElim A B (.lamIntro rightLevel rightFormation rightBodyCode)
      rightArgumentCode) rightChecked
  refine ⟨leftChecked, rightChecked, leftResult, rightResult,
    atLeftResult, atRightResult, ?_⟩
  intro env admitted
  have argumentsEqual := qualified_paths_common_terminal_values heads constants R
    successor universes successorQualified model constantModel contextCode leftPath rightPath
    contextChecked leftArgumentChecked rightArgumentChecked atContext leftArg rightArg
    atLeftArgument atRightArgument env admitted
  have bodyAgreement := assemble_neutralEliminations_coherent heads constants R
    leftBodyCode leftBodyChecked bodyQualified atLeftBody rightBodyChecked atRightBody
    (EqualOrHeads.refl B)
  apply qualified_lambda_applications_related heads constants R successor universes
    successorQualified model constantModel context contextCode valid contextChecked atContext
    leftLevel rightLevel A A B B body body leftArgument rightArgument leftFormation
    rightFormation leftArgumentCode rightArgumentCode leftBodyCode rightBodyCode
    leftFormed rightFormed leftArg rightArg leftResult rightResult leftBody rightBody
    leftDomain rightDomain leftFormationChecked rightFormationChecked leftArgumentChecked
    rightArgumentChecked leftArgumentQualified rightArgumentQualified atLeftFormation
    atRightFormation atLeftDomain atRightDomain atLeftBody atRightBody atLeftArgument
    atRightArgument atLeftResult atRightResult env env admitted admitted Eq Eq
    argumentsEqual
  intro x _ y _ equal
  subst y
  exact congrArg (fun meaning : Meaning.{u} (n + 1) =>
    meaning.value (ZFSetTypeExpressionInterpretation.extend env x)) bodyAgreement

/-- A common structurally interpreted body makes the result of two checked
lambda applications independent of their retained product domains and body
certificates. The argument expressions and their displayed domain types may
differ; qualified paths compare their values at one supported terminal.
Only the application results are compared, on valid context environments. -/
theorem qualified_cross_domain_lambda_applications_coherent
    (universes : FormationSensitive.UniverseRegularity R)
    (successorQualified : ∀ level, R.isUniverse level →
      R.isUniverse (successor level) ∧ R.headTyping level (successor level))
    (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)
    (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (leftA rightA : Tm Head n) (leftB rightB body : Tm Head (n + 1))
    (leftLevel rightLevel : Head)
    (leftFormation rightFormation leftArgumentCode rightArgumentCode : Code Head NoConversion n)
    (leftBodyCode rightBodyCode : Code Head NoConversion (n + 1))
    (leftArgument rightArgument terminal : Tm Head n)
    (leftTerminal rightTerminal : Code Head NoConversion n)
    (leftChecked : check R noConversionCheck context (.app (.lam body) leftArgument)
      (inst0 leftArgument leftB)
      (.appElim leftA leftB (.lamIntro leftLevel leftFormation leftBodyCode)
        leftArgumentCode) = true)
    (rightChecked : check R noConversionCheck context (.app (.lam body) rightArgument)
      (inst0 rightArgument rightB)
      (.appElim rightA rightB (.lamIntro rightLevel rightFormation rightBodyCode)
        rightArgumentCode) = true)
    (leftArgumentQualified : leftArgumentCode.resultFormationsNeutral R successor
      contextCode leftArgument leftA = true)
    (rightArgumentQualified : rightArgumentCode.resultFormationsNeutral R successor
      contextCode rightArgument rightA = true)
    (leftPath : QualifiedBetaPath R successor contextCode leftA leftArgument leftArgumentCode
      terminal leftTerminal)
    (rightPath : QualifiedBetaPath R successor contextCode rightA rightArgument rightArgumentCode
      terminal rightTerminal)
    (terminalSupported : ZFSetTypeExpressionInterpretation.supported terminal = true)
    (bodySupported : ZFSetTypeExpressionInterpretation.supported body = true) :
    ∃ leftResult rightResult,
      assemble heads constants
        (.appElim leftA leftB (.lamIntro leftLevel leftFormation leftBodyCode)
          leftArgumentCode)
        (.app (.lam body) leftArgument) (inst0 leftArgument leftB) = some leftResult ∧
      assemble heads constants
        (.appElim rightA rightB (.lamIntro rightLevel rightFormation rightBodyCode)
          rightArgumentCode)
        (.app (.lam body) rightArgument) (inst0 rightArgument rightB) = some rightResult ∧
      ∀ env, valid env → leftResult.value env = rightResult.value env := by
  have leftParts := leftChecked
  have rightParts := rightChecked
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at leftParts rightParts
  have leftFormationChecked := leftParts.1.1.1.2
  have leftBodyChecked := leftParts.1.1.2
  have leftArgumentChecked := leftParts.1.2
  have rightFormationChecked := rightParts.1.1.1.2
  have rightBodyChecked := rightParts.1.1.2
  have rightArgumentChecked := rightParts.1.2
  obtain ⟨leftFormed, atLeftFormation, leftProduct⟩ :=
    accepted_assembles heads constants R noConversionCheck leftFormation leftFormationChecked
  obtain ⟨rightFormed, atRightFormation, rightProduct⟩ :=
    accepted_assembles heads constants R noConversionCheck rightFormation rightFormationChecked
  obtain ⟨leftDomain, atLeftDomain⟩ := leftProduct leftA leftB rfl
  obtain ⟨rightDomain, atRightDomain⟩ := rightProduct rightA rightB rfl
  obtain ⟨leftBody, atLeftBody, _⟩ :=
    accepted_assembles heads constants R noConversionCheck leftBodyCode leftBodyChecked
  obtain ⟨rightBody, atRightBody, _⟩ :=
    accepted_assembles heads constants R noConversionCheck rightBodyCode rightBodyChecked
  obtain ⟨leftArg, atLeftArgument, _⟩ :=
    accepted_assembles heads constants R noConversionCheck leftArgumentCode leftArgumentChecked
  obtain ⟨rightArg, atRightArgument, _⟩ :=
    accepted_assembles heads constants R noConversionCheck rightArgumentCode rightArgumentChecked
  obtain ⟨leftResult, atLeftResult, _⟩ := accepted_assembles heads constants R
    noConversionCheck (.appElim leftA leftB (.lamIntro leftLevel leftFormation leftBodyCode)
      leftArgumentCode) leftChecked
  obtain ⟨rightResult, atRightResult, _⟩ := accepted_assembles heads constants R
    noConversionCheck (.appElim rightA rightB (.lamIntro rightLevel rightFormation rightBodyCode)
      rightArgumentCode) rightChecked
  refine ⟨leftResult, rightResult, atLeftResult, atRightResult, ?_⟩
  intro env admitted
  have bodyAgreement := assemble_supported_values heads constants bodySupported
    atLeftBody atRightBody
  apply qualified_lambda_applications_related_of_paths heads constants R successor
    universes successorQualified model constantModel context contextCode valid
    contextChecked atContext leftLevel rightLevel leftA rightA leftB rightB body body
    leftArgument rightArgument terminal leftFormation rightFormation leftArgumentCode
    rightArgumentCode leftTerminal rightTerminal leftBodyCode rightBodyCode leftFormed
    rightFormed leftArg rightArg leftResult rightResult leftBody rightBody leftDomain
    rightDomain leftFormationChecked rightFormationChecked leftArgumentChecked
    rightArgumentChecked leftArgumentQualified rightArgumentQualified leftPath rightPath
    terminalSupported atLeftFormation atRightFormation atLeftDomain atRightDomain
    atLeftBody atRightBody atLeftArgument atRightArgument atLeftResult atRightResult
    env admitted Eq
  intro x _ y _ equal
  subst y
  exact congrArg (fun value : Value.{u} (n + 1) =>
    value (ZFSetTypeExpressionInterpretation.extend env x)) bodyAgreement

#print axioms qualified_common_lambda_applications_coherent
#print axioms qualified_cross_domain_lambda_applications_coherent

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
