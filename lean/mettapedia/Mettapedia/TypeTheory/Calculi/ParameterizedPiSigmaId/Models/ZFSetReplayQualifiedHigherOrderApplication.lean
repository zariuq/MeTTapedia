import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedBetaPath

/-!
# Comparing applications of independently computed functions

An accepted application need not have a lambda in function position. Both
function and argument can themselves be computations with independent typing
trees, displayed types, and finite qualified paths. This theorem compares the
actual replay assemblies of such higher-order applications on valid context
environments. It does not normalize arbitrary accepted terms or assert global
certificate independence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.Logic.HOL.Embedding

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (successor : Head → Head)

/-- Two higher-order applications can be checked and compared when their
independently computed functions and arguments have qualified paths to common
supported endpoints. Neither function is required to be a syntactic lambda.
The result meanings are those assembled by the accepted application codes. -/
theorem qualified_higher_order_applications_agree
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
    (rightArgumentType : arguments.rightDisplayed = rightA) :
    let leftApplication := Tm.app functions.leftTerm arguments.leftTerm
    let rightApplication := Tm.app functions.rightTerm arguments.rightTerm
    let leftCode := Code.appElim leftA leftB functions.leftCode arguments.leftCode
    let rightCode := Code.appElim rightA rightB functions.rightCode arguments.rightCode
    check R noConversionCheck context leftApplication
        (inst0 arguments.leftTerm leftB) leftCode = true ∧
      check R noConversionCheck context rightApplication
        (inst0 arguments.rightTerm rightB) rightCode = true ∧
      ∃ leftResult rightResult,
        assemble heads constants leftCode leftApplication
          (inst0 arguments.leftTerm leftB) = some leftResult ∧
        assemble heads constants rightCode rightApplication
          (inst0 arguments.rightTerm rightB) = some rightResult ∧
        ∀ env, valid env → leftResult.value env = rightResult.value env := by
  have leftFunctionChecked : check R noConversionCheck context functions.leftTerm
      (.pi leftA leftB) functions.leftCode = true := by
    simpa only [leftFunctionType] using functions.leftChecked
  have rightFunctionChecked : check R noConversionCheck context functions.rightTerm
      (.pi rightA rightB) functions.rightCode = true := by
    simpa only [rightFunctionType] using functions.rightChecked
  have leftArgumentChecked : check R noConversionCheck context arguments.leftTerm
      leftA arguments.leftCode = true := by
    simpa only [leftArgumentType] using arguments.leftChecked
  have rightArgumentChecked : check R noConversionCheck context arguments.rightTerm
      rightA arguments.rightCode = true := by
    simpa only [rightArgumentType] using arguments.rightChecked
  have leftChecked : check R noConversionCheck context
      (.app functions.leftTerm arguments.leftTerm) (inst0 arguments.leftTerm leftB)
      (.appElim leftA leftB functions.leftCode arguments.leftCode) = true := by
    simp only [check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨leftFunctionChecked, leftArgumentChecked⟩, True.intro⟩
  have rightChecked : check R noConversionCheck context
      (.app functions.rightTerm arguments.rightTerm) (inst0 arguments.rightTerm rightB)
      (.appElim rightA rightB functions.rightCode arguments.rightCode) = true := by
    simp only [check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨rightFunctionChecked, rightArgumentChecked⟩, True.intro⟩
  obtain ⟨leftResult, atLeftResult, _⟩ := accepted_assembles heads constants R
    noConversionCheck (.appElim leftA leftB functions.leftCode arguments.leftCode) leftChecked
  obtain ⟨rightResult, atRightResult, _⟩ := accepted_assembles heads constants R
    noConversionCheck (.appElim rightA rightB functions.rightCode arguments.rightCode) rightChecked
  refine ⟨leftChecked, rightChecked, leftResult, rightResult,
    atLeftResult, atRightResult, ?_⟩
  intro env admitted
  have functionValues := qualified_paths_supported_terminal_values heads constants R
    successor universes successorQualified model constantModel contextCode
    functions.leftPath functions.rightPath contextChecked functions.leftChecked
    functions.rightChecked atContext leftFunction rightFunction functions.atLeft
    functions.atRight functions.terminalSupported env admitted
  have argumentValues := qualified_paths_supported_terminal_values heads constants R
    successor universes successorQualified model constantModel contextCode
    arguments.leftPath arguments.rightPath contextChecked arguments.leftChecked
    arguments.rightChecked atContext leftArgument rightArgument arguments.atLeft
    arguments.atRight arguments.terminalSupported env admitted
  have atLeftFunction : assemble heads constants functions.leftCode functions.leftTerm
      (.pi leftA leftB) = some leftFunction := by
    simpa only [leftFunctionType] using functions.atLeft
  have atRightFunction : assemble heads constants functions.rightCode functions.rightTerm
      (.pi rightA rightB) = some rightFunction := by
    simpa only [rightFunctionType] using functions.atRight
  have atLeftArgument : assemble heads constants arguments.leftCode arguments.leftTerm
      leftA = some leftArgument := by
    simpa only [leftArgumentType] using arguments.atLeft
  have atRightArgument : assemble heads constants arguments.rightCode arguments.rightTerm
      rightA = some rightArgument := by
    simpa only [rightArgumentType] using arguments.atRight
  have leftValue : leftResult.value env = ZFSetTraceProducts.traceApp
      (leftFunction.value env) (leftArgument.value env) := by
    simp only [assemble, atLeftFunction, atLeftArgument] at atLeftResult
    change some (Meaning.plain (fun e => ZFSetTraceProducts.traceApp
      (leftFunction.value e) (leftArgument.value e))) = some leftResult at atLeftResult
    cases Option.some.inj atLeftResult
    rfl
  have rightValue : rightResult.value env = ZFSetTraceProducts.traceApp
      (rightFunction.value env) (rightArgument.value env) := by
    simp only [assemble, atRightFunction, atRightArgument] at atRightResult
    change some (Meaning.plain (fun e => ZFSetTraceProducts.traceApp
      (rightFunction.value e) (rightArgument.value e))) = some rightResult at atRightResult
    cases Option.some.inj atRightResult
    rfl
  rw [leftValue, rightValue, functionValues, argumentValues]

/-- Equality of the computed inputs matters: two distinct traced functions
can disagree at the same admitted argument. -/
theorem different_functions_same_argument :
    ZFSetTraceProducts.traceApp
        (ZFSetTraceProducts.traceLam
          (ZFSetDependentProducts.graph ({∅} : ZFSet.{u}) (fun _ => ∅))) ∅ ≠
      ZFSetTraceProducts.traceApp
        (ZFSetTraceProducts.traceLam
          (ZFSetDependentProducts.graph ({∅} : ZFSet.{u}) (fun _ => {∅}))) ∅ := by
  rw [ZFSetTraceProducts.traceApp_graph_beta
      (fun _ => ∅) (ZFSet.mem_singleton.mpr rfl),
    ZFSetTraceProducts.traceApp_graph_beta
      (fun _ => {∅}) (ZFSet.mem_singleton.mpr rfl)]
  intro equal
  have member : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [← equal] at member
  exact ZFSet.notMem_empty _ member

#print axioms qualified_higher_order_applications_agree
#print axioms different_functions_same_argument

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
