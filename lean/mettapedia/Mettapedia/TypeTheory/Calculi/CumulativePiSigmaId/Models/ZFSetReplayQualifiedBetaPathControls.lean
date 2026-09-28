import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayQualifiedTypingControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayComputedFamilyControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedBetaFamily

/-!
# Two real contractions before a dependent consumer

The nested function applies identity to a computed function. The first
certificate contraction leaves another redex; the second reaches the neutral
identity. Each transition uses its actual checked certificate and exact
contraction receipt. A zero-fuel search is deliberately inconclusive.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedBetaPathControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay
open ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedTypingControls
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedFamilyControls
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayUniverseModel
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetTraceUniverseInterpretation (interpretHead)

theorem nested_path : QualifiedBetaPath Tower.rules TowerDecisions.headTarget
    .nil functionType nestedFunction nestedFunctionCode identity identityCode := by
  exact .contraction functions_qualified.2.2 function_contraction_receipts.2
    (.contraction functions_qualified.2.1 function_contraction_receipts.1
      (.terminal identity identityCode (by decide +kernel)))

theorem computed_path : QualifiedBetaPath Tower.rules TowerDecisions.headTarget
    .nil functionType computedFunction computedFunctionCode identity identityCode := by
  exact .contraction functions_qualified.2.1 function_contraction_receipts.1
    (.terminal identity identityCode (by decide +kernel))

/-- Both paths actually preserve the accepted typing judgment. -/
theorem nested_and_computed_terminal_checked :
    check Tower.rules noConversionCheck .nil identity functionType identityCode = true ∧
      check Tower.rules noConversionCheck .nil identity functionType identityCode = true :=
  ⟨nested_path.terminal_checked Tower.rules functions_checked.2.2,
    computed_path.terminal_checked Tower.rules functions_checked.2.1⟩

/-- Exhaustion is not a refutation of the accepted program or its path. -/
theorem zero_fuel_is_inconclusive :
    nestedFunctionCode.qualifiedBetaPath? Tower.rules TowerDecisions.headTarget
      .nil 0 nestedFunction functionType = none ∧
      check Tower.rules noConversionCheck .nil nestedFunction functionType nestedFunctionCode = true :=
  ⟨rfl, functions_checked.2.2⟩

/-- Three units of fuel suffice for the two actual contractions and terminal
certificate of this program. -/
theorem nested_search_succeeds :
    (nestedFunctionCode.qualifiedBetaPath? Tower.rules TowerDecisions.headTarget
      .nil 3 nestedFunction functionType).isSome = true := by
  decide +kernel

/-- The bounded search returns the same retained endpoint as the explicit
two-step proof, not merely some successful path. -/
theorem nested_search_endpoint :
    (nestedFunctionCode.qualifiedBetaPath? Tower.rules TowerDecisions.headTarget
      .nil 3 nestedFunction functionType).map Subtype.val =
        some (identity, identityCode) := by
  rfl

universe u

private abbrev functionLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ Tower.zero))

/-- Two independently certified computations, one taking two beta steps and
the other taking one, feed the same genuinely dependent identity family.
Their raw instantiated types differ, while their checked set values agree. -/
theorem nested_computed_family_values
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      identityFamily (.head functionLevel) nestedFunction lowerFamily nestedFunctionCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      identityFamily (.head (.sort (.succ (.succ Tower.zero))))
        computedFunction upperFamily computedFunctionCode
    check Tower.rules noConversionCheck .nil (inst0 nestedFunction identityFamily)
      (.head functionLevel) leftFormation = true ∧
    check Tower.rules noConversionCheck .nil (inst0 computedFunction identityFamily)
      (.head (.sort (.succ (.succ Tower.zero)))) rightFormation = true ∧
    ∃ left right,
      assemble (interpretHead h seed ground valuation) constants leftFormation
        (inst0 nestedFunction identityFamily) (.head functionLevel) = some left ∧
      assemble (interpretHead h seed ground valuation) constants rightFormation
        (inst0 computedFunction identityFamily)
          (.head (.sort (.succ (.succ Tower.zero)))) = some right ∧
      ∀ env : Environment.{u} 0, left.value env = right.value env := by
  obtain ⟨nested, atNested, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    nestedFunctionCode functions_checked.2.2
  obtain ⟨computed, atComputed, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    computedFunctionCode functions_checked.2.1
  simpa only [true_imp_iff] using
    (qualified_paths_family_values (interpretHead h seed ground valuation) constants
      Tower.rules TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
      successor_qualified (universeModel h seed ground valuation groundTyped)
      (empty_constants_model _ constants) .nil nestedFunctionCode computedFunctionCode
      identityCode identityCode nested_path computed_path (valid := fun _ => True)
      rfl functions_checked.2.2 functions_checked.2.1 rfl nested computed atNested atComputed
      identityFamily functionLevel (.sort (.succ (.succ Tower.zero))) lowerFamily upperFamily
      family_checked.1 family_checked.2.1 family_checked.2.2)

/-- The dependent family observes a syntactic distinction that the semantic
comparison does not erase at the source level. -/
theorem nested_computed_family_types_differ :
    inst0 nestedFunction identityFamily ≠ inst0 computedFunction identityFamily := by
  decide +kernel

/-- The two distinct checked dependent types have exactly the same valid
one-variable extensions after different-length source computations. -/
theorem nested_computed_family_contexts
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      identityFamily (.head functionLevel) nestedFunction lowerFamily nestedFunctionCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      identityFamily (.head (.sort (.succ (.succ Tower.zero))))
        computedFunction upperFamily computedFunctionCode
    checkContext Tower.rules noConversionCheck (.snoc .nil (inst0 nestedFunction identityFamily))
      (.snoc .nil functionLevel leftFormation) = true ∧
    checkContext Tower.rules noConversionCheck (.snoc .nil (inst0 computedFunction identityFamily))
      (.snoc .nil (.sort (.succ (.succ Tower.zero))) rightFormation) = true ∧
    ∃ leftValid rightValid : Environment.{u} 1 → Prop,
      assembleContext (interpretHead h seed ground valuation) constants
        (.snoc .nil functionLevel leftFormation)
        (.snoc .nil (inst0 nestedFunction identityFamily)) = some leftValid ∧
      assembleContext (interpretHead h seed ground valuation) constants
        (.snoc .nil (.sort (.succ (.succ Tower.zero))) rightFormation)
        (.snoc .nil (inst0 computedFunction identityFamily)) = some rightValid ∧
      leftValid = rightValid := by
  obtain ⟨nested, atNested, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    nestedFunctionCode functions_checked.2.2
  obtain ⟨computed, atComputed, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    computedFunctionCode functions_checked.2.1
  exact qualified_paths_family_contexts (interpretHead h seed ground valuation) constants
    Tower.rules TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (universeModel h seed ground valuation groundTyped)
    (empty_constants_model _ constants) .nil nestedFunctionCode computedFunctionCode
    identityCode identityCode nested_path computed_path (valid := fun _ => True)
    rfl functions_checked.2.2 functions_checked.2.1 rfl nested computed atNested atComputed
    identityFamily functionLevel (.sort (.succ (.succ Tower.zero)))
    (by decide +kernel) (by decide +kernel) lowerFamily upperFamily
    family_checked.1 family_checked.2.1 family_checked.2.2

#print axioms nested_path
#print axioms computed_path
#print axioms nested_and_computed_terminal_checked
#print axioms zero_fuel_is_inconclusive
#print axioms nested_search_succeeds
#print axioms nested_search_endpoint
#print axioms nested_computed_family_values
#print axioms nested_computed_family_types_differ
#print axioms nested_computed_family_contexts

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedBetaPathControls
