import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedApplicationComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedImageSearch
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayQualifiedTypingControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayUniverseModel

/-!
# A checked application of a computed function to a computed argument

The context contains a function and an argument. One program first computes
each independently by an identity beta step, then applies the computed
function to the computed argument. A second program applies the original
variables. The two programs and their retained certificates differ, while
their replay values agree on every valid environment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayHigherOrderApplicationControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayQualifiedTypingControls
open ZFSetReplayUniverseModel

private abbrev u0 : Tower.Head := .sort Tower.zero
private abbrev u1 : Tower.Head := .sort (.succ Tower.zero)
private abbrev functionUniverse : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ Tower.zero))
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n

def context : Tower.Ctx 2 := .snoc (.snoc .nil functionType) (.head u0)
def contextCode : ContextCode Tower.Head NoConversion 2 :=
  .snoc (.snoc .nil functionUniverse functionFormation) u1 .headType

def computedFunction : Tower.Tm 2 := .app identity (.var 1)
def computedFunctionCode : Replay 2 :=
  .appElim functionType functionType consumerCode .var
def originalFunction : Tower.Tm 2 := .var 1
def originalFunctionCode : Replay 2 := .var

def computedArgument : Tower.Tm 2 := .app identity (.var 0)
def computedArgumentCode : Replay 2 :=
  .appElim (.head u0) (.head u0) identityCode .var
def originalArgument : Tower.Tm 2 := .var 0
def originalArgumentCode : Replay 2 := .var

def computedApplication : Tower.Tm 2 := .app computedFunction computedArgument
def originalApplication : Tower.Tm 2 := .app originalFunction originalArgument
def computedApplicationCode : Replay 2 :=
  .appElim (.head u0) (.head u0) computedFunctionCode computedArgumentCode
def originalApplicationCode : Replay 2 :=
  .appElim (.head u0) (.head u0) originalFunctionCode originalArgumentCode

theorem context_checked : checkContext Tower.rules noConversionCheck context contextCode = true := by
  decide +kernel

theorem components_checked :
    check Tower.rules noConversionCheck context computedFunction functionType
      computedFunctionCode = true ∧
    check Tower.rules noConversionCheck context originalFunction functionType
      originalFunctionCode = true ∧
    check Tower.rules noConversionCheck context computedArgument (.head u0)
      computedArgumentCode = true ∧
    check Tower.rules noConversionCheck context originalArgument (.head u0)
      originalArgumentCode = true := by
  decide +kernel

theorem applications_qualified :
    computedApplicationCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget
      contextCode computedApplication (.head u0) = true ∧
    originalApplicationCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget
      contextCode originalApplication (.head u0) = true := by
  decide +kernel

theorem computed_function_path : QualifiedBetaPath Tower.rules TowerDecisions.headTarget
    contextCode functionType computedFunction computedFunctionCode
      originalFunction originalFunctionCode := by
  exact .contraction (by decide +kernel) rfl
    (.terminal originalFunction originalFunctionCode (by decide +kernel))

theorem computed_argument_path : QualifiedBetaPath Tower.rules TowerDecisions.headTarget
    contextCode (.head u0) computedArgument computedArgumentCode
      originalArgument originalArgumentCode := by
  exact .contraction (by decide +kernel) rfl
    (.terminal originalArgument originalArgumentCode (by decide +kernel))

theorem original_function_path : QualifiedBetaPath Tower.rules TowerDecisions.headTarget
    contextCode functionType originalFunction originalFunctionCode
      originalFunction originalFunctionCode :=
  .terminal originalFunction originalFunctionCode (by decide +kernel)

theorem original_argument_path : QualifiedBetaPath Tower.rules TowerDecisions.headTarget
    contextCode (.head u0) originalArgument originalArgumentCode
      originalArgument originalArgumentCode :=
  .terminal originalArgument originalArgumentCode (by decide +kernel)

/-- Both inputs really compute before the outer application; this is not a
comparison of the same raw application under two differently named proofs. -/
theorem programs_are_distinct :
    computedFunction ≠ originalFunction ∧
      computedArgument ≠ originalArgument ∧
      computedApplication ≠ originalApplication := by
  decide +kernel

universe u

theorem computed_application_agrees
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    let heads := interpretHead h seed ground valuation
    ∃ valid : Environment.{u} 2 → Prop,
      assembleContext heads constants contextCode context = some valid ∧
      check Tower.rules noConversionCheck context computedApplication (.head u0)
        computedApplicationCode = true ∧
      check Tower.rules noConversionCheck context originalApplication (.head u0)
        originalApplicationCode = true ∧
      ∃ left right,
        assemble heads constants computedApplicationCode computedApplication (.head u0) = some left ∧
        assemble heads constants originalApplicationCode originalApplication (.head u0) = some right ∧
        ∀ env, valid env → left.value env = right.value env ∧
          left.value env ∈ universeSet h seed 0 := by
  let heads := interpretHead h seed ground valuation
  obtain ⟨valid, atContext⟩ := accepted_context_assembles heads constants
    Tower.rules noConversionCheck contextCode context_checked
  obtain ⟨leftFunction, atLeftFunction, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck computedFunctionCode components_checked.1
  obtain ⟨rightFunction, atRightFunction, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck originalFunctionCode components_checked.2.1
  obtain ⟨leftArgument, atLeftArgument, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck computedArgumentCode components_checked.2.2.1
  obtain ⟨rightArgument, atRightArgument, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck originalArgumentCode components_checked.2.2.2
  let functions : QualifiedImagePaths heads constants Tower.rules
      TowerDecisions.headTarget context contextCode leftFunction rightFunction :=
    QualifiedImagePaths.ofSearch heads constants Tower.rules TowerDecisions.headTarget
      context contextCode leftFunction rightFunction
      functionType functionType computedFunction originalFunction originalFunction
      computedFunctionCode originalFunctionCode originalFunctionCode originalFunctionCode
      2 1 (by rfl) (by rfl) components_checked.1 components_checked.2.1
      atLeftFunction atRightFunction rfl
  let arguments : QualifiedImagePaths heads constants Tower.rules
      TowerDecisions.headTarget context contextCode leftArgument rightArgument :=
    QualifiedImagePaths.ofSearch heads constants Tower.rules TowerDecisions.headTarget
      context contextCode leftArgument rightArgument
      (.head u0) (.head u0) computedArgument originalArgument originalArgument
      computedArgumentCode originalArgumentCode originalArgumentCode originalArgumentCode
      2 1 (by rfl) (by rfl) components_checked.2.2.1 components_checked.2.2.2
      atLeftArgument atRightArgument rfl
  have leftChecked : check Tower.rules noConversionCheck context computedApplication
      (.head u0) computedApplicationCode = true := by
    simp only [computedApplication, computedApplicationCode, check, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨⟨components_checked.1, components_checked.2.2.1⟩, rfl⟩
  have rightChecked : check Tower.rules noConversionCheck context originalApplication
      (.head u0) originalApplicationCode = true := by
    simp only [originalApplication, originalApplicationCode, check, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨⟨components_checked.2.1, components_checked.2.2.2⟩, rfl⟩
  obtain ⟨leftResult, atLeftResult, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck computedApplicationCode leftChecked
  obtain ⟨rightResult, atRightResult, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck originalApplicationCode rightChecked
  refine ⟨valid, atContext, leftChecked, rightChecked,
    leftResult, rightResult, atLeftResult, atRightResult, ?_⟩
  intro env admitted
  let formed : Meaning.{u} 2 :=
    ⟨fun _ => ZFSetTraceProducts.tracePiSet (heads u0) (fun _ => heads u0),
      some (fun _ => heads u0)⟩
  have atFormation : assemble heads constants (functionFormation : Replay 2)
      functionType (.head functionUniverse) = some formed := rfl
  have atDomain : formed.productDomain? = some (fun _ => heads u0) := rfl
  have formationChecked : check Tower.rules noConversionCheck context functionType
      (.head functionUniverse) (functionFormation : Replay 2) = true := by
    decide +kernel
  have leftArgumentQualified : computedArgumentCode.resultFormationsNeutral Tower.rules
      TowerDecisions.headTarget contextCode computedArgument (.head u0) = true := by
    decide +kernel
  have rightArgumentQualified : originalArgumentCode.resultFormationsNeutral Tower.rules
      TowerDecisions.headTarget contextCode originalArgument (.head u0) = true := by
    decide +kernel
  have functionValues := qualified_paths_supported_terminal_values heads constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity successor_qualified
    (universeModel h seed ground valuation groundTyped)
    (empty_constants_model heads constants) contextCode
    functions.leftPath functions.rightPath context_checked functions.leftChecked
    functions.rightChecked atContext leftFunction rightFunction functions.atLeft
    functions.atRight functions.terminalSupported env admitted
  have argumentValues := qualified_paths_supported_terminal_values heads constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity successor_qualified
    (universeModel h seed ground valuation groundTyped)
    (empty_constants_model heads constants) contextCode
    arguments.leftPath arguments.rightPath context_checked arguments.leftChecked
    arguments.rightChecked atContext leftArgument rightArgument arguments.atLeft
    arguments.atRight arguments.terminalSupported env admitted
  have functionsRelated : ZFSetTraceProducts.TraceFunctionRelated
      (heads u0) (heads u0) Eq Eq (leftFunction.value env) (rightFunction.value env) := by
    rw [functionValues]
    intro x _ y _ equal
    subst y
    rfl
  have valueEquality := qualified_computed_function_applications_related heads constants
    Tower.rules TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (universeModel h seed ground valuation groundTyped)
    (empty_constants_model heads constants) context contextCode valid context_checked
    atContext functionUniverse functionUniverse (.head u0) (.head u0)
    (.head u0) (.head u0) computedFunction originalFunction
    computedArgument originalArgument (functionFormation : Replay 2)
    (functionFormation : Replay 2) computedFunctionCode originalFunctionCode
    computedArgumentCode originalArgumentCode formed formed leftFunction rightFunction
    leftArgument rightArgument leftResult rightResult (fun _ => heads u0)
    (fun _ => heads u0) formationChecked formationChecked leftChecked rightChecked
    leftArgumentQualified rightArgumentQualified atFormation atFormation atDomain atDomain
    atLeftFunction atRightFunction atLeftArgument atRightArgument atLeftResult
    atRightResult env env admitted admitted Eq Eq functionsRelated argumentValues
  have atType : assemble heads constants (.headType : Replay 2)
      (.head u0) (.head u1) = some (Meaning.plain (fun _ => heads u0)) := rfl
  have typeChecked : check Tower.rules noConversionCheck context
      (.head u0) (.head u1) (.headType : Replay 2) = true := by
    decide +kernel
  have member := qualified_membership heads constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (universeModel h seed ground valuation groundTyped)
    (empty_constants_model heads constants) computedApplicationCode contextCode
    context_checked leftChecked applications_qualified.1 valid leftResult
    atContext atLeftResult u1 .headType (Meaning.plain (fun _ => heads u0))
    typeChecked atType env admitted
  exact ⟨valueEquality, member⟩

/-- The valid-context comparison is not an empty-domain statement. The
context contains a concrete total traced function and a typed argument. -/
theorem computed_application_context_inhabited
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    ∃ (valid : Environment.{u} 2 → Prop),
      assembleContext (interpretHead h seed ground valuation) constants
        contextCode context = some valid ∧ ∃ env, valid env := by
  let heads := interpretHead h seed ground valuation
  let U : ZFSet.{u} := heads u0
  let valid1 : Environment.{u} 1 → Prop :=
    fun environment => True ∧ environment 0 ∈ ZFSetTraceProducts.tracePiSet U (fun _ => U)
  let valid2 : Environment.{u} 2 → Prop :=
    fun environment => valid1 (environment ∘ wk) ∧ environment 0 ∈ U
  have atContext : assembleContext heads constants contextCode context = some valid2 := by
    rfl
  let functionValue : ZFSetDependentProducts.Elements
      (ZFSetTraceProducts.tracePiSet U (fun _ => U)) :=
    ZFSetTraceProducts.traceEncode (a := U) (b := fun _ => U)
      (fun _ => ⟨ground, groundTyped⟩)
  let environment : Environment.{u} 2 :=
    Fin.cases ground (Fin.cases functionValue.1 Fin.elim0)
  refine ⟨valid2, atContext, environment, ?_⟩
  change (True ∧ functionValue.1 ∈ ZFSetTraceProducts.tracePiSet U (fun _ => U)) ∧
    ground ∈ U
  exact ⟨⟨True.intro, functionValue.2⟩, groundTyped⟩

#print axioms computed_application_agrees
#print axioms programs_are_distinct
#print axioms computed_application_context_inhabited
#print axioms applications_qualified

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayHigherOrderApplicationControls
