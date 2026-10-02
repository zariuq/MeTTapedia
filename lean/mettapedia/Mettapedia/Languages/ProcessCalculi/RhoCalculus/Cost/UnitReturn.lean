import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.UnitPolicyControls
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceTransition

/-!
# Authored unit syntax returned by actual funded computations

The existing parameterized execution monad can return a value at an unchanged
funded state.  It can also carry the actual one-firing paths used by the unit
policy controls.  A returned value is not automatically executed.

The value below is admitted by the authored generated Cost grammar: it is a
signed inert rho term carrying the signature unit.  It has no generated
whole-redex transition.  Thus the pure result has concrete authored syntax,
while the existing positive meter and its funding requirement remain intact.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.UnitReturn

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open UnitPolicyControls

/-- A literal signature unit is a value of the authored signature sort. -/
theorem signature_unit_typed (source : CIGSLT)
    (free : FreeTypeContext) (bound : List TypeExpr) :
    HasSort source.costWholeLanguage free bound
      (.apply costSignatureUnitConstructorName []) costSignatureSortName := by
  apply HasType.constructor (rule := costSignatureUnitConstructor)
  · rw [source.costWholeLanguage_terms]
    apply List.mem_append_right
    simp [costCoreConstructors]
  · simp [UsesBareCollection, costSignatureUnitConstructor]
  · exact .nil

/-- The actual signed constructor accepts the unit at any typed base body. -/
theorem signed_unit_typed (source : CIGSLT)
    {free : FreeTypeContext} {bound : List TypeExpr} {body : Pattern}
    (bodyTyped : HasSort source.costWholeLanguage free bound body
      (costBaseSortName source.theory.presentation.interactingSort.1.name)) :
    HasSort source.costWholeLanguage free bound
      (.apply costSignedConstructorName
        [body, .apply costSignatureUnitConstructorName []])
      costWrappedSortName := by
  apply HasType.constructor
    (rule := costSignedConstructor source.theory.presentation.interactingSort.1.name)
  · rw [source.costWholeLanguage_terms]
    apply List.mem_append_right
    simp [costCoreConstructors]
  · simp [UsesBareCollection, costSignedConstructor]
  · exact .cons trivial rfl bodyTyped
      (.cons trivial rfl (signature_unit_typed source free bound) .nil)

def authoredUnitPattern : Pattern :=
  .apply costSignedConstructorName
    [.apply (costBaseConstructorName "PZero") [],
      .apply costSignatureUnitConstructorName []]

/-- The returned wrapper is typed by the generated rho grammar. -/
theorem authored_unit_pattern_typed :
    HasSort rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      authoredUnitPattern costWrappedSortName := by
  apply signed_unit_typed
  exact checkHasType_sound (by decide +kernel)

def authoredUnitSort : LangSort rhoCIGSLT.costWholeLanguage :=
  ⟨costWrappedSortName, rhoCIGSLT.costWrappedSortName_mem_costWhole⟩

/-- The pure result is an admitted closed generated term, rather than an
untyped tree used only to satisfy the parameterized-monad interface. -/
def authoredUnitValue :
    WellSorted.OpenTerm rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty [] authoredUnitSort :=
  ⟨authoredUnitPattern, authored_unit_pattern_typed, rfl, rfl,
    authored_unit_pattern_typed.isWellScopedAt⟩

/-- The whole-redex matcher requires a funded contact, which this value lacks. -/
theorem authored_unit_no_rule_match :
    matchPatternForRule rhoCIGSLT.costWholeLanguage
      rhoCIGSLT.costWholeRedexRewrite authoredUnitPattern = [] := by
  decide +kernel

/-- No contextual depth enables a generated rewrite of this returned value. -/
theorem authored_unit_rewriteAt_nil (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage fuel authoredUnitPattern = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [rewriteAt, rhoCIGSLT.costWholeLanguage_rewrites,
        List.flatMap_cons, List.flatMap_nil, List.append_nil,
        applyRuleUsing, authored_unit_no_rule_match, List.flatMap_nil]

/-- No premise evaluator supplies a step when the authored rule cannot match. -/
theorem authored_unit_no_step (base : BasePremiseEvaluator) (target : Pattern) :
    ¬ Step base
      rhoCIGSLT.costWholeLanguage authoredUnitPattern target := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule membership
  simp only [rhoCIGSLT.costWholeLanguage_rewrites,
    List.mem_singleton] at membership
  subst rule
  exact authored_unit_no_rule_match

def combinedExecution :
    FundedExecution combinedHeadPath.sourceState
      combinedHeadPath.targetState Unit :=
  FundedExecution.ofPath combinedHeadPath ()

def splitExecution :
    FundedExecution splitHeadsPath.sourceState
      splitHeadsPath.targetState Unit :=
  FundedExecution.ofPath splitHeadsPath ()

/-- The established parameterized monad carries a real one-event execution. -/
theorem combined_execution_nonempty :
    combinedExecution.transition.rawEmission.length = 1 ∧
      combinedExecution.transition.consumedPurseCells = 1 := by
  change combinedHeadPath.rawEmission.length = 1 ∧
    combinedHeadPath.consumedPurseCells = 1
  rw [combinedHeadPath.rawEmission_length_eq_depth]
  exact combined_head_path_counts

/-- Its split-funding computation retains two consumed cells in one event. -/
theorem split_execution_nonempty :
    splitExecution.transition.rawEmission.length = 1 ∧
      splitExecution.transition.consumedPurseCells = 2 := by
  change splitHeadsPath.rawEmission.length = 1 ∧
    splitHeadsPath.consumedPurseCells = 2
  rw [splitHeadsPath.rawEmission_length_eq_depth]
  exact split_heads_path_counts

/-- Return the admitted authored wrapper at the very source of the actual
combined-head execution.  Its pre/post states coincide by construction. -/
def pureAuthoredUnit :
    FundedExecution combinedHeadPath.sourceState combinedHeadPath.sourceState
      (WellSorted.OpenTerm rhoCIGSLT.costWholeLanguage
        FreeTypeContext.empty [] authoredUnitSort) :=
  fundedExecutionParameterizedMonad.pure combinedHeadPath.sourceState authoredUnitValue

/-- Pure return leaves the exact runtime/provenance state and counter intact. -/
theorem pure_authored_unit_controls :
    pureAuthoredUnit.transition.rawEmission = [] ∧
      pureAuthoredUnit.transition.depth = 0 ∧
      pureAuthoredUnit.transition.sourceState.components =
        combinedHeadPath.sourceState.components ∧
      pureAuthoredUnit.transition.targetState.components =
        combinedHeadPath.sourceState.components ∧
      pureAuthoredUnit.transition.targetState.nextId =
        combinedHeadPath.sourceState.nextId ∧
      pureAuthoredUnit.result.1 = authoredUnitPattern := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The same real source admits both a nonempty funded computation and a
pure return of a typed authored value without treating return as execution. -/
theorem pure_and_firing_share_actual_source :
    combinedExecution.transition.rawEmission.length = 1 ∧
      pureAuthoredUnit.transition.rawEmission = [] ∧
      (∀ target, ¬ Step (engineBasePremises RelationEnv.empty)
        rhoCIGSLT.costWholeLanguage pureAuthoredUnit.result.1 target) := by
  refine ⟨combined_execution_nonempty.1, pure_authored_unit_controls.1, ?_⟩
  exact authored_unit_no_step (engineBasePremises RelationEnv.empty)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.UnitReturn
