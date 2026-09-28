import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayApplicationComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayFunctionRelations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedBetaPath

/-!
# Comparing checked lambda applications with computed arguments

The result-formation qualification supplies semantic membership for an
arbitrary checked argument. A checked Π-formation identifies its exact retained
domain, so application comparison need not take argument admission as an
independent premise. The body relation remains explicit: this is a local
coherence principle, not agreement of all accepted certificates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment extend)
open Mettapedia.Logic.HOL.Embedding
open ZFSetTraceProducts (TraceFunctionRelated)

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
/-- A qualified checked argument inhabits the domain retained by any checked
Π-formation at every valid environment. The domain code is recovered from
the actual formation tree; neither the argument nor its certificate is
required to be a variable or a normal form. -/
theorem qualified_argument_in_product_domain
    (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)
    (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    (valid : Environment.{u} n → Prop)
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (level : Head) (A : Tm Head n) (B : Tm Head (n + 1))
    (formation : Code Head NoConversion n) (formed : Meaning.{u} n)
    (domain : Value.{u} n)
    (formationChecked : check R noConversionCheck context (.pi A B) (.head level) formation = true)
    (atFormation : assemble heads constants formation (.pi A B) (.head level) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (argument : Tm Head n) (argumentCode : Code Head NoConversion n)
    (arg : Meaning.{u} n)
    (argumentChecked : check R noConversionCheck context argument A argumentCode = true)
    (argumentQualified : argumentCode.resultFormationsNeutral R successor
      contextCode argument A = true)
    (atArgument : assemble heads constants argumentCode argument A = some arg)
    (env : Environment.{u} n) (admitted : valid env) :
    arg.value env ∈ domain env := by
  obtain ⟨domainLevel, bodyLevel, domainCode, bodyCode, parts, _, _, domainChecked, _⟩ :=
    formation.piFormation_checked R noConversionCheck formationChecked
  obtain ⟨domainMeaning, _, atDomainCode, _, _, retained⟩ :=
    assemble_piFormation heads constants formation parts atFormation
  rw [atDomain] at retained
  cases Option.some.inj retained
  exact qualified_membership heads constants R successor universes successorQualified
    model constantModel argumentCode contextCode contextChecked argumentChecked
    argumentQualified valid arg atContext atArgument domainLevel domainCode
    domainMeaning domainChecked atDomainCode env admitted

include universes successorQualified in
/-- Application of independently computed functions preserves their
domain-indexed relation. Qualified checking admits each computed argument
to the exact domain retained by its own checked product formation; the
function terms themselves need not be lambda introductions. -/
theorem qualified_computed_function_applications_related
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
    (leftEnv rightEnv : Environment.{u} n)
    (leftAdmitted : valid leftEnv) (rightAdmitted : valid rightEnv)
    (inputRelation outputRelation : ZFSet.{u} → ZFSet.{u} → Prop)
    (functionsRelated : TraceFunctionRelated (leftDomain leftEnv) (rightDomain rightEnv)
      inputRelation outputRelation (leftFunctionMeaning.value leftEnv)
      (rightFunctionMeaning.value rightEnv))
    (argumentsRelated : inputRelation (leftArg.value leftEnv) (rightArg.value rightEnv)) :
    outputRelation (leftResult.value leftEnv) (rightResult.value rightEnv) := by
  have leftParts := leftApplicationChecked
  have rightParts := rightApplicationChecked
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at leftParts rightParts
  have leftInside := qualified_argument_in_product_domain heads constants R successor
    universes successorQualified model constantModel context contextCode valid
    contextChecked atContext leftLevel leftA leftB leftFormation leftFormed leftDomain
    leftFormationChecked atLeftFormation atLeftDomain leftArgument leftArgumentCode leftArg
    leftParts.1.2 leftArgumentQualified atLeftArgument leftEnv leftAdmitted
  have rightInside := qualified_argument_in_product_domain heads constants R successor
    universes successorQualified model constantModel context contextCode valid
    contextChecked atContext rightLevel rightA rightB rightFormation rightFormed rightDomain
    rightFormationChecked atRightFormation atRightDomain rightArgument rightArgumentCode rightArg
    rightParts.1.2 rightArgumentQualified atRightArgument rightEnv rightAdmitted
  exact assembled_applications_related heads constants leftA rightA leftB rightB
    leftFunction rightFunction leftArgument rightArgument leftFunctionCode
    rightFunctionCode leftArgumentCode rightArgumentCode leftFunctionMeaning
    rightFunctionMeaning leftArg rightArg leftResult rightResult atLeftFunction
    atRightFunction atLeftArgument atRightArgument atLeftResult atRightResult
    leftEnv rightEnv (leftDomain leftEnv) (rightDomain rightEnv)
    inputRelation outputRelation functionsRelated leftInside rightInside argumentsRelated

include universes successorQualified in
/-- Two independently checked applications may retain different Π-domains
and different certificates for computed arguments. Qualified argument trees
discharge both domain obligations; a relation on admitted body values then
compares the resulting applications. -/
theorem qualified_lambda_applications_related
    (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)
    (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    (valid : Environment.{u} n → Prop)
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (leftLevel rightLevel : Head) (leftA rightA : Tm Head n)
    (leftB rightB leftBody rightBody : Tm Head (n + 1))
    (leftArgument rightArgument : Tm Head n)
    (leftFormation rightFormation leftArgumentCode rightArgumentCode : Code Head NoConversion n)
    (leftBodyCode rightBodyCode : Code Head NoConversion (n + 1))
    (leftFormed rightFormed leftArg rightArg leftResult rightResult : Meaning.{u} n)
    (leftBodyMeaning rightBodyMeaning : Meaning.{u} (n + 1))
    (leftDomain rightDomain : Value.{u} n)
    (leftFormationChecked : check R noConversionCheck context (.pi leftA leftB)
      (.head leftLevel) leftFormation = true)
    (rightFormationChecked : check R noConversionCheck context (.pi rightA rightB)
      (.head rightLevel) rightFormation = true)
    (leftArgumentChecked : check R noConversionCheck context leftArgument leftA
      leftArgumentCode = true)
    (rightArgumentChecked : check R noConversionCheck context rightArgument rightA
      rightArgumentCode = true)
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
    (leftAdmitted : valid leftEnv) (rightAdmitted : valid rightEnv)
    (inputRelation outputRelation : ZFSet.{u} → ZFSet.{u} → Prop)
    (argumentsRelated : inputRelation (leftArg.value leftEnv) (rightArg.value rightEnv))
    (bodiesRelated : ∀ x ∈ leftDomain leftEnv, ∀ y ∈ rightDomain rightEnv,
      inputRelation x y → outputRelation
        (leftBodyMeaning.value (extend leftEnv x)) (rightBodyMeaning.value (extend rightEnv y))) :
    outputRelation (leftResult.value leftEnv) (rightResult.value rightEnv) := by
  have leftInside := qualified_argument_in_product_domain heads constants R successor
    universes successorQualified model constantModel context contextCode valid
    contextChecked atContext leftLevel leftA leftB leftFormation leftFormed leftDomain
    leftFormationChecked atLeftFormation atLeftDomain leftArgument leftArgumentCode leftArg
    leftArgumentChecked leftArgumentQualified atLeftArgument leftEnv leftAdmitted
  have rightInside := qualified_argument_in_product_domain heads constants R successor
    universes successorQualified model constantModel context contextCode valid
    contextChecked atContext rightLevel rightA rightB rightFormation rightFormed rightDomain
    rightFormationChecked atRightFormation atRightDomain rightArgument rightArgumentCode rightArg
    rightArgumentChecked rightArgumentQualified atRightArgument rightEnv rightAdmitted
  exact application_lambda_related heads constants leftLevel rightLevel leftA rightA
    leftB rightB leftBody rightBody leftArgument rightArgument leftFormation rightFormation
    leftArgumentCode rightArgumentCode leftBodyCode rightBodyCode leftFormed rightFormed
    leftArg rightArg leftResult rightResult leftBodyMeaning rightBodyMeaning leftDomain rightDomain
    atLeftFormation atRightFormation atLeftDomain atRightDomain atLeftBody atRightBody
    atLeftArgument atRightArgument atLeftResult atRightResult leftEnv rightEnv
    inputRelation outputRelation leftInside rightInside argumentsRelated bodiesRelated

include universes successorQualified in
/-- Two computed arguments may have different terms, displayed domains and
retained certificates. Qualified paths to one supported endpoint establish
their input equality; qualified typing admits each into its own retained
Π-domain. Hence a body comparison on equal admitted inputs transports through
both checked applications without identifying their intermediate types. -/
theorem qualified_lambda_applications_related_of_paths
    (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)
    (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    (valid : Environment.{u} n → Prop)
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (leftLevel rightLevel : Head) (leftA rightA : Tm Head n)
    (leftB rightB leftBody rightBody : Tm Head (n + 1))
    (leftArgument rightArgument terminal : Tm Head n)
    (leftFormation rightFormation leftArgumentCode rightArgumentCode
      leftTerminal rightTerminal : Code Head NoConversion n)
    (leftBodyCode rightBodyCode : Code Head NoConversion (n + 1))
    (leftFormed rightFormed leftArg rightArg leftResult rightResult : Meaning.{u} n)
    (leftBodyMeaning rightBodyMeaning : Meaning.{u} (n + 1))
    (leftDomain rightDomain : Value.{u} n)
    (leftFormationChecked : check R noConversionCheck context (.pi leftA leftB)
      (.head leftLevel) leftFormation = true)
    (rightFormationChecked : check R noConversionCheck context (.pi rightA rightB)
      (.head rightLevel) rightFormation = true)
    (leftArgumentChecked : check R noConversionCheck context leftArgument leftA
      leftArgumentCode = true)
    (rightArgumentChecked : check R noConversionCheck context rightArgument rightA
      rightArgumentCode = true)
    (leftArgumentQualified : leftArgumentCode.resultFormationsNeutral R successor
      contextCode leftArgument leftA = true)
    (rightArgumentQualified : rightArgumentCode.resultFormationsNeutral R successor
      contextCode rightArgument rightA = true)
    (leftPath : StructuralTypingReplay.QualifiedBetaPath R successor contextCode leftA
      leftArgument leftArgumentCode terminal leftTerminal)
    (rightPath : StructuralTypingReplay.QualifiedBetaPath R successor contextCode rightA
      rightArgument rightArgumentCode terminal rightTerminal)
    (terminalSupported : ZFSetTypeExpressionInterpretation.supported terminal = true)
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
    (env : Environment.{u} n) (admitted : valid env)
    (outputRelation : ZFSet.{u} → ZFSet.{u} → Prop)
    (bodiesRelated : ∀ x ∈ leftDomain env, ∀ y ∈ rightDomain env,
      x = y → outputRelation
        (leftBodyMeaning.value (extend env x)) (rightBodyMeaning.value (extend env y))) :
    outputRelation (leftResult.value env) (rightResult.value env) := by
  have argumentsEqual := qualified_paths_supported_terminal_values heads constants R
    successor universes successorQualified model constantModel contextCode leftPath
    rightPath contextChecked leftArgumentChecked rightArgumentChecked atContext
    leftArg rightArg atLeftArgument atRightArgument terminalSupported env admitted
  exact qualified_lambda_applications_related heads constants R successor universes
    successorQualified model constantModel context contextCode valid contextChecked
    atContext leftLevel rightLevel leftA rightA leftB rightB leftBody rightBody
    leftArgument rightArgument leftFormation rightFormation leftArgumentCode
    rightArgumentCode leftBodyCode rightBodyCode leftFormed rightFormed leftArg
    rightArg leftResult rightResult leftBodyMeaning rightBodyMeaning leftDomain
    rightDomain leftFormationChecked rightFormationChecked leftArgumentChecked
    rightArgumentChecked leftArgumentQualified rightArgumentQualified atLeftFormation
    atRightFormation atLeftDomain atRightDomain atLeftBody atRightBody atLeftArgument
    atRightArgument atLeftResult atRightResult env env admitted admitted Eq
    outputRelation argumentsEqual bodiesRelated

#print axioms qualified_argument_in_product_domain
#print axioms qualified_computed_function_applications_related
#print axioms qualified_lambda_applications_related
#print axioms qualified_lambda_applications_related_of_paths

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
