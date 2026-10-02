import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayComputedBodyApplicationControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedBodyPathCoherence

/-!
# Two checked function values related without being equal

The inner application of each lambda is certified by a different universe
context. The values of the outer lambdas are observably equal on the inputs
both domains admit, but their full set-coded functions differ outside that
common observation. This is a higher-order boundary control, not function
extensionality across unequal domains.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedFunctionObservationControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetTraceProducts (TraceFunctionRelated traceApp traceLam tracePiSet)
open ZFSetDependentProducts (graph)
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayUniverseModel (universeModel empty_constants_model successor_qualified)
open ZFSetReplayApplicationComparisonControls (context contextCode context_checked
  context_assembles valid)
open ZFSetReplayComputedBodyApplicationControls (computedBody lowerBodyCode upperBodyCode
  lowerFormation upperFormation lower_body_path upper_body_path)

universe u

private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev two : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev oneJoin : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ Tower.zero))
private abbrev twoJoin : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))
private abbrev Replay (m : Nat) := Code Tower.Head NoConversion m

def lowerLambdaCode : Replay 1 := .lamIntro oneJoin lowerFormation lowerBodyCode
def upperLambdaCode : Replay 1 := .lamIntro twoJoin upperFormation upperBodyCode

noncomputable def lowerFormationMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  ⟨fun _ => tracePiSet (universeSet h ∅ 0) (fun _ => universeSet h ∅ 0),
    some (fun _ => universeSet h ∅ 0)⟩

noncomputable def upperFormationMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  ⟨fun _ => tracePiSet (universeSet h ∅ 1) (fun _ => universeSet h ∅ 1),
    some (fun _ => universeSet h ∅ 1)⟩

noncomputable def lowerBodyMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 2 :=
  .plain (fun env => traceApp (traceLam (graph (universeSet h ∅ 0) id)) (env 0))

noncomputable def upperBodyMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 2 :=
  .plain (fun env => traceApp (traceLam (graph (universeSet h ∅ 1) id)) (env 0))

noncomputable def lowerLambdaMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  .plain (fun _ => traceLam (graph (universeSet h ∅ 0)
    (fun x => traceApp (traceLam (graph (universeSet h ∅ 0) id)) x)))

noncomputable def upperLambdaMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  .plain (fun _ => traceLam (graph (universeSet h ∅ 1)
    (fun x => traceApp (traceLam (graph (universeSet h ∅ 1) id)) x)))

theorem lambdas_checked :
    check Tower.rules noConversionCheck context (.lam computedBody)
      (.pi (.head zero) (.head zero)) lowerLambdaCode = true ∧
    check Tower.rules noConversionCheck context (.lam computedBody)
      (.pi (.head one) (.head one)) upperLambdaCode = true := by decide

theorem lower_formation_assembles (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerFormation (.pi (.head zero) (.head zero)) (.head oneJoin) =
      some (lowerFormationMeaning h) := rfl

theorem upper_formation_assembles (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      upperFormation (.pi (.head one) (.head one)) (.head twoJoin) =
      some (upperFormationMeaning h) := rfl

theorem lower_body_assembles (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerBodyCode computedBody (.head zero) = some (lowerBodyMeaning h) := rfl

theorem upper_body_assembles (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      upperBodyCode computedBody (.head one) = some (upperBodyMeaning h) := rfl

theorem lower_lambda_assembles (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      lowerLambdaCode (.lam computedBody) (.pi (.head zero) (.head zero)) =
      some (lowerLambdaMeaning h) := rfl

theorem upper_lambda_assembles (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      upperLambdaCode (.lam computedBody) (.pi (.head one) (.head one)) =
      some (upperLambdaMeaning h) := rfl

/-- Both independently accepted function values agree when applied to one
common input admitted by their actual product domains. -/
theorem lambda_values_related (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u})
    (env : Environment.{u} 1) (admitted : valid h env) :
    TraceFunctionRelated (universeSet h ∅ 0) (universeSet h ∅ 1) Eq Eq
      ((lowerLambdaMeaning h).value env) ((upperLambdaMeaning h).value env) := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  exact qualified_lambdas_observationally_related_of_body_paths heads constants
    Tower.rules TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
    (empty_constants_model heads constants) context contextCode context_checked
    (context_assembles h constants) (.head zero) (.head one) (.head zero)
    (.head one) computedBody (.var 0) oneJoin twoJoin one one two two
    lowerFormation upperFormation .headType .headType .headType .headType
    lowerBodyCode upperBodyCode .var .var
    (lowerFormationMeaning h) (upperFormationMeaning h)
    (lowerLambdaMeaning h) (upperLambdaMeaning h)
    (lowerBodyMeaning h) (upperBodyMeaning h)
    (fun _ => universeSet h ∅ 0) (fun _ => universeSet h ∅ 1)
    lambdas_checked.1 lambdas_checked.2 rfl rfl lower_body_path upper_body_path
    (lower_formation_assembles h constants) (upper_formation_assembles h constants)
    rfl rfl (lower_body_assembles h constants) (upper_body_assembles h constants)
    (lower_lambda_assembles h constants) (upper_lambda_assembles h constants)
    rfl env admitted

/-- The observational theorem cannot be strengthened to equality of whole
function values: the upper function accepts the lower universe set itself,
while the lower function does not. -/
theorem lambda_values_not_equal (h : CofinalInaccessibles.{u})
    (env : Environment.{u} 1) :
    (lowerLambdaMeaning h).value env ≠ (upperLambdaMeaning h).value env := by
  intro equal
  have observed := congrArg (fun f => traceApp f (universeSet h ∅ 0)) equal
  have lower : traceApp ((lowerLambdaMeaning h).value env) (universeSet h ∅ 0) = ∅ := by
    change traceApp (traceLam (graph (universeSet h ∅ 0)
      (fun x => traceApp (traceLam (graph (universeSet h ∅ 0) id)) x)))
      (universeSet h ∅ 0) = ∅
    exact ZFSetTraceProducts.traceApp_graph_outside _
      (universeSet_no_self_membership h ∅ 0)
  have upper : traceApp ((upperLambdaMeaning h).value env) (universeSet h ∅ 0) =
      universeSet h ∅ 0 := by
    change traceApp (traceLam (graph (universeSet h ∅ 1)
      (fun x => traceApp (traceLam (graph (universeSet h ∅ 1) id)) x)))
      (universeSet h ∅ 0) = universeSet h ∅ 0
    rw [ZFSetTraceProducts.traceApp_graph_beta _ (universeSet_mem_next h ∅ 0),
      ZFSetTraceProducts.traceApp_graph_beta _ (universeSet_mem_next h ∅ 0)]
    rfl
  rw [lower, upper] at observed
  have member := seed_mem_universeSet h (∅ : ZFSet.{u}) (0 : Nat)
  rw [← observed] at member
  exact ZFSet.notMem_empty _ member

#print axioms lambda_values_related
#print axioms lambda_values_not_equal

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedFunctionObservationControls
