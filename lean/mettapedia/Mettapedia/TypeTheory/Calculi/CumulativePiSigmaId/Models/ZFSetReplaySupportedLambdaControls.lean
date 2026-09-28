import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySupportedApplicationCoherence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayQualifiedLambdaApplicationControls

/-!
# Two checked whole functions with a computed projection body

The same lambda is checked with two genuinely different retained product
formations, one directly and one through a cumulative wrapper. Its body
constructs a dependent pair and projects its first component, so this is
not a variable-only lambda. The general structural-coherence theorem then
identifies the entire trace-coded function, not just one application.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplaySupportedLambdaControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.SetTheory
open ZFSetTypeExpressionInterpretation (Environment)
open ZFSetTypeExpressionInterpretation (extend)
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayUniverseModel (universeModel empty_constants_model successor_qualified)
open ZFSetReplayApplicationComparisonControls
  (context contextCode context_checked context_assembles valid reduct reductCode pairType)
open ZFSetReplayQualifiedLambdaApplicationControls
  (projectedBody projectedLowerFormation projectedLowerBodyCode
    projectedUpperFormation projectedUpperBodyCode projected_body_supported)

universe u

private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev lowerLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ (.succ Tower.zero)))
private abbrev higherLevel : Tower.Head :=
  .sort (.succ (.max (.succ Tower.zero) (.succ (.succ Tower.zero))))
private abbrev upperLevel : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))
private abbrev aboveUpperLevel : Tower.Head :=
  .sort (.succ (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero))))

def productType : Tower.Tm 1 := .pi (.head zero) (.head one)
def program : Tower.Tm 1 := .lam projectedBody
def directCode : Code Tower.Head NoConversion 1 :=
  .lamIntro lowerLevel projectedLowerFormation projectedLowerBodyCode
def liftedCode : Code Tower.Head NoConversion 1 :=
  .lamIntro higherLevel (.cumul lowerLevel projectedLowerFormation)
    projectedLowerBodyCode

theorem direct_checked :
    check Tower.rules noConversionCheck context program productType directCode = true := by
  decide +kernel

theorem lifted_checked :
    check Tower.rules noConversionCheck context program productType liftedCode = true := by
  decide +kernel

theorem codes_differ : directCode ≠ liftedCode := by
  intro equal
  cases equal

theorem program_body_computes :
    projectedBody = .fst ZFSetReplayApplicationComparisonControls.body := rfl

/-- The two actual checked certificates assemble equal *whole function sets*
for every interpretation of heads and declared constants. This uses the
direct and cumulative product formations retained by those certificates. -/
theorem checked_computed_body_function_agrees
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    ∃ direct lifted : Meaning.{u} 1,
      assemble heads constants directCode program productType = some direct ∧
      assemble heads constants liftedCode program productType = some lifted ∧
      direct.value = lifted.value := by
  obtain ⟨direct, atDirect, _⟩ :=
    accepted_assembles heads constants Tower.rules noConversionCheck directCode direct_checked
  obtain ⟨lifted, atLifted, _⟩ :=
    accepted_assembles heads constants Tower.rules noConversionCheck liftedCode lifted_checked
  refine ⟨direct, lifted, atDirect, atLifted, ?_⟩
  exact checked_lambda_values_eq_of_supported heads constants Tower.rules
    context (.head zero) (.head one) projectedBody lowerLevel higherLevel
    projectedLowerFormation (.cumul lowerLevel projectedLowerFormation)
    projectedLowerBodyCode projectedLowerBodyCode direct lifted
    direct_checked lifted_checked atDirect atLifted rfl projected_body_supported

/-- The direct certificate's semantic function is not vacuous: it can be
applied to any member of its explicitly retained input domain. -/
theorem direct_domain_has_empty_input
    (h : Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.CofinalInaccessibles.{u}) :
    (∅ : ZFSet.{u}) ∈
      Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.universeSet h ∅ 0 :=
  Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.seed_mem_zero h ∅

/-- The argument is computed by constructing a dependent proof-carrying
pair, then eliminating its first projection. It is not a context variable. -/
def computedArgument : Tower.Tm 1 := .fst reduct
def computedArgumentCode : Code Tower.Head NoConversion 1 :=
  .fstElim (.id (.head one) (.var 0) (.var 0)) reductCode
def computedProgram : Tower.Tm 1 := .app (.lam projectedBody) computedArgument
def directApplicationCode : Code Tower.Head NoConversion 1 :=
  .appElim (.head one) (.head one)
    (.lamIntro upperLevel projectedUpperFormation projectedUpperBodyCode)
    computedArgumentCode
def liftedApplicationCode : Code Tower.Head NoConversion 1 :=
  .appElim (.head one) (.head one)
    (.lamIntro aboveUpperLevel (.cumul upperLevel projectedUpperFormation)
      projectedUpperBodyCode) computedArgumentCode

theorem computed_argument_supported :
    ZFSetTypeExpressionInterpretation.supported computedArgument = true := by
  decide +kernel

theorem computed_argument_checked :
    check Tower.rules noConversionCheck context computedArgument (.head one)
      computedArgumentCode = true := by
  decide +kernel

theorem computed_argument_qualified :
    computedArgumentCode.resultFormationsNeutral Tower.rules
      TowerDecisions.headTarget contextCode computedArgument (.head one) = true := by
  decide +kernel

/-- The checked projection inhabits the input set actually retained by the
independently checked Π-formation. This uses universe-model soundness and
result-formation qualification, not equality of two arbitrary replay values. -/
theorem computed_argument_in_retained_domain
    (h : ZFSetUniverseClosure.CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
    ∃ formed argument domain,
      assemble heads constants projectedUpperFormation
        (.pi (.head one) (.head one)) (.head upperLevel) = some formed ∧
      assemble heads constants computedArgumentCode computedArgument (.head one) =
        some argument ∧
      formed.productDomain? = some domain ∧
      ∀ env, valid h env → argument.value env ∈ domain env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  have formationChecked : check Tower.rules noConversionCheck context
      (.pi (.head one) (.head one)) (.head upperLevel)
      projectedUpperFormation = true := by decide +kernel
  obtain ⟨formed, atFormation, product⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck projectedUpperFormation formationChecked
  obtain ⟨domain, atDomain⟩ := product (.head one) (.head one) rfl
  obtain ⟨argument, atArgument, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck computedArgumentCode computed_argument_checked
  refine ⟨formed, argument, domain, atFormation, atArgument, atDomain, ?_⟩
  intro env admitted
  exact qualified_argument_in_product_domain heads constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
    (empty_constants_model heads constants) context contextCode (valid h)
    context_checked (context_assembles h constants) upperLevel (.head one)
    (.head one) projectedUpperFormation formed domain formationChecked
    atFormation atDomain computedArgument computedArgumentCode argument
    computed_argument_checked computed_argument_qualified atArgument env admitted

theorem direct_application_checked :
    check Tower.rules noConversionCheck context computedProgram (.head one)
      directApplicationCode = true := by
  decide +kernel

theorem lifted_application_checked :
    check Tower.rules noConversionCheck context computedProgram (.head one)
      liftedApplicationCode = true := by
  decide +kernel

theorem application_codes_differ : directApplicationCode ≠ liftedApplicationCode := by
  intro equal
  cases equal

/-- No common beta terminal or neutral-result-formation path is needed here:
the pair projection is structural, and both actual application receipts are
compared after independent checking. -/
theorem checked_computed_argument_applications_agree
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    ∃ direct lifted : Meaning.{u} 1,
      assemble heads constants directApplicationCode computedProgram (.head one) =
        some direct ∧
      assemble heads constants liftedApplicationCode computedProgram (.head one) =
        some lifted ∧
      direct.value = lifted.value := by
  obtain ⟨direct, atDirect, _⟩ :=
    accepted_assembles heads constants Tower.rules noConversionCheck
      directApplicationCode direct_application_checked
  obtain ⟨lifted, atLifted, _⟩ :=
    accepted_assembles heads constants Tower.rules noConversionCheck
      liftedApplicationCode lifted_application_checked
  refine ⟨direct, lifted, atDirect, atLifted, ?_⟩
  exact checked_structural_lambda_applications_agree heads constants Tower.rules
    context (.head one) (.head one) projectedBody computedArgument
    upperLevel aboveUpperLevel projectedUpperFormation
    (.cumul upperLevel projectedUpperFormation) computedArgumentCode
    computedArgumentCode projectedUpperBodyCode projectedUpperBodyCode
    direct lifted direct_application_checked lifted_application_checked
    atDirect atLifted rfl projected_body_supported computed_argument_supported

/-- On valid inputs the checked application really returns its computed
argument: both the argument and the function body construct a dependent pair
and project it. Membership above justifies beta evaluation in the retained
domain. -/
theorem checked_computed_application_returns_input
    (h : ZFSetUniverseClosure.CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    ∃ result : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        directApplicationCode computedProgram (.head one) = some result ∧
      ∀ env, valid h env → result.value env = env 0 := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  obtain ⟨formed, argument, domain, atFormation, atArgument, atDomain, inside⟩ :=
    computed_argument_in_retained_domain h constants
  have bodyChecked : check Tower.rules noConversionCheck
      (.snoc context (.head one)) projectedBody (.head one)
      projectedUpperBodyCode = true := by decide +kernel
  obtain ⟨bodyMeaning, atBody, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck projectedUpperBodyCode bodyChecked
  obtain ⟨result, atResult, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck directApplicationCode direct_application_checked
  refine ⟨result, atResult, ?_⟩
  intro env admitted
  have appValue := application_lambda_value heads constants upperLevel
    (.head one) (.head one) projectedBody computedArgument
    projectedUpperFormation computedArgumentCode projectedUpperBodyCode
    formed argument result bodyMeaning domain atFormation atDomain atBody
    atArgument atResult env (inside env admitted)
  have bodyValue := agrees_with_type_expressions heads constants
    projectedUpperBodyCode projectedBody (.head one) bodyMeaning
    projected_body_supported atBody (extend env (argument.value env))
  have argumentValue := agrees_with_type_expressions heads constants
    computedArgumentCode computedArgument (.head one) argument
    computed_argument_supported atArgument env
  calc
    result.value env = bodyMeaning.value (extend env (argument.value env)) := appValue
    _ = argument.value env := by
      simpa [projectedBody, ZFSetReplayApplicationComparisonControls.body,
        ZFSetTypeExpressionInterpretation.interpret,
        ZFSetTypeExpressionInterpretation.extend,
        ZFSetOrderedPair.first_pair] using bodyValue
    _ = env 0 := by
      simpa [computedArgument, reduct,
        ZFSetTypeExpressionInterpretation.interpret,
        ZFSetOrderedPair.first_pair] using argumentValue

/-- Both independently checked routes return the live context value, so
whole-result agreement is not merely agreement on an unused argument. -/
theorem both_checked_computed_applications_return_input
    (h : ZFSetUniverseClosure.CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    ∃ direct lifted : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        directApplicationCode computedProgram (.head one) = some direct ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        liftedApplicationCode computedProgram (.head one) = some lifted ∧
      ∀ env, valid h env →
        direct.value env = env 0 ∧ lifted.value env = env 0 := by
  obtain ⟨direct, lifted, atDirect, atLifted, same⟩ :=
    checked_computed_argument_applications_agree
      (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
  obtain ⟨actual, atActual, computes⟩ :=
    checked_computed_application_returns_input h constants
  have sameDirect : direct = actual := Option.some.inj (atDirect.symm.trans atActual)
  subst actual
  refine ⟨direct, lifted, atDirect, atLifted, ?_⟩
  intro env admitted
  exact ⟨computes env admitted,
    (congrFun same env).symm.trans (computes env admitted)⟩

#print axioms direct_checked
#print axioms lifted_checked
#print axioms codes_differ
#print axioms checked_computed_body_function_agrees
#print axioms direct_domain_has_empty_input
#print axioms computed_argument_supported
#print axioms computed_argument_checked
#print axioms computed_argument_qualified
#print axioms computed_argument_in_retained_domain
#print axioms direct_application_checked
#print axioms lifted_application_checked
#print axioms application_codes_differ
#print axioms checked_computed_argument_applications_agree
#print axioms checked_computed_application_returns_input
#print axioms both_checked_computed_applications_return_input

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplaySupportedLambdaControls
