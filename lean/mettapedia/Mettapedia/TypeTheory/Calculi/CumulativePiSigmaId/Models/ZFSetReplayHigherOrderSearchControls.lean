import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayQualifiedBetaSearch
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayHigherOrderApplicationControls

/-!
# Searching the retained computations of a higher-order application

The existing checked program computes both a function and its argument before
application. The general finite-path completeness theorem supplies fuel for
the executable certificate search on both components. The semantic result
is then the checked dependent application's comparison and membership law.
Search success alone never substitutes for checking the source judgment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayHigherOrderSearchControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay
open ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayHigherOrderApplicationControls
open ZFSetReplayQualifiedTypingControls
open ZFSetReplayUniverseModel

/-- The actual computed function and computed argument both have finite fuel
bounds at which search returns their exact original variable and certificate. -/
theorem computed_components_search :
    (∃ functionFuel,
      (computedFunctionCode.qualifiedBetaPath? Tower.rules TowerDecisions.headTarget
        contextCode functionFuel computedFunction functionType).map Subtype.val =
        some (originalFunction, originalFunctionCode)) ∧
    (∃ argumentFuel,
      (computedArgumentCode.qualifiedBetaPath? Tower.rules TowerDecisions.headTarget
        contextCode argumentFuel computedArgument (.head (.sort Tower.zero))).map Subtype.val =
        some (originalArgument, originalArgumentCode)) :=
  ⟨computed_function_path.search_complete Tower.rules TowerDecisions.headTarget
      contextCode functionType,
   computed_argument_path.search_complete Tower.rules TowerDecisions.headTarget
      contextCode (.head (.sort Tower.zero))⟩

/-- The concrete one-contraction components each need two units of search
fuel: one for the contraction and one to certify the neutral endpoint. -/
theorem computed_components_two_fuel :
    (computedFunctionCode.qualifiedBetaPath? Tower.rules TowerDecisions.headTarget
      contextCode 2 computedFunction functionType).map Subtype.val =
        some (originalFunction, originalFunctionCode) ∧
    (computedArgumentCode.qualifiedBetaPath? Tower.rules TowerDecisions.headTarget
      contextCode 2 computedArgument (.head (.sort Tower.zero))).map Subtype.val =
        some (originalArgument, originalArgumentCode) := by
  constructor <;> rfl

/-- A malformed root certificate can produce a syntactic terminal search
result, but cannot pass the independent checker. -/
theorem search_success_does_not_admit_malformed_code :
    ((Code.headType : Code Tower.Head NoConversion 2).qualifiedBetaPath?
      Tower.rules TowerDecisions.headTarget contextCode 1 computedArgument
      (.head (.sort Tower.zero))).isSome = true ∧
    check Tower.rules noConversionCheck context computedArgument
      (.head (.sort Tower.zero)) (.headType : Code Tower.Head NoConversion 2) = false := by
  decide +kernel

universe u

/-- In the same concrete higher-order program, both component searches
recover their certificates and the independently checked application has
equal, universe-typed values. The semantic implication from search output
in general is `qualified_searched_supported_terminal_values`. -/
theorem computed_component_search_and_application_agreement
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    (∃ functionFuel,
      (computedFunctionCode.qualifiedBetaPath? Tower.rules TowerDecisions.headTarget
        contextCode functionFuel computedFunction functionType).map Subtype.val =
        some (originalFunction, originalFunctionCode)) ∧
    (∃ argumentFuel,
      (computedArgumentCode.qualifiedBetaPath? Tower.rules TowerDecisions.headTarget
        contextCode argumentFuel computedArgument (.head (.sort Tower.zero))).map Subtype.val =
        some (originalArgument, originalArgumentCode)) ∧
    (let heads := interpretHead h seed ground valuation
      ∃ valid : Environment.{u} 2 → Prop,
        assembleContext heads constants contextCode context = some valid ∧
        check Tower.rules noConversionCheck context computedApplication
          (.head (.sort Tower.zero)) computedApplicationCode = true ∧
        check Tower.rules noConversionCheck context originalApplication
          (.head (.sort Tower.zero)) originalApplicationCode = true ∧
        ∃ left right,
          assemble heads constants computedApplicationCode computedApplication
            (.head (.sort Tower.zero)) = some left ∧
          assemble heads constants originalApplicationCode originalApplication
            (.head (.sort Tower.zero)) = some right ∧
          ∀ env, valid env → left.value env = right.value env ∧
            left.value env ∈ universeSet h seed 0) := by
  exact ⟨computed_components_search.1, computed_components_search.2,
    computed_application_agrees h seed ground valuation groundTyped constants⟩

#print axioms computed_components_search
#print axioms computed_components_two_fuel
#print axioms search_success_does_not_admit_malformed_code
#print axioms computed_component_search_and_application_agreement

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayHigherOrderSearchControls
