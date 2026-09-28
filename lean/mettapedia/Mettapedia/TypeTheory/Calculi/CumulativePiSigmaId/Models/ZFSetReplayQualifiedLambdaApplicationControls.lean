import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayQualifiedApplicationControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedLambdaApplicationCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedHigherOrderApplication

/-!
# Computed-argument controls for common-lambda application coherence

Two different depths of the checked computation return the same context
variable. Applying the same dependent pair-producing lambda at either depth
therefore returns the same interpreted result on valid environments. The
argument computations are not reduced or erased before checking.

The negative control uses two different bodies at the same admitted input:
equal inputs alone do not establish equality of application outputs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedLambdaApplicationControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.SetTheory
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayUniverseModel (universeModel empty_constants_model successor_qualified)
open ZFSetReplayApplicationComparisonControls (context contextCode valid pairType body
  lowerFormation lowerBodyCode upperBodyCode context_checked context_assembles)
open ZFSetReplayQualifiedApplicationControls (pairProgram lowerApplicationCode
  lower_argument_qualified upper_argument_qualified lower_argument_path upper_argument_path)
open ZFSetReplayComputedArgumentControls (program lowerCode upperCode lower_checked upper_checked)

universe u

private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev two : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev lowerLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero))))
private abbrev projectedLowerLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ (.succ Tower.zero)))
private abbrev projectedUpperLevel : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))
private abbrev Replay (m : Nat) := Code Tower.Head NoConversion m

/-- A depth-`k` computation and a depth-`k+1` computation are separately
accepted as arguments to the dependent lambda, and their checked
applications agree at every valid environment. -/
theorem successive_computed_applications_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    ∃ left right : Meaning.{u} 1,
      check Tower.rules noConversionCheck context (pairProgram depth) pairType
        (lowerApplicationCode depth) = true ∧
      check Tower.rules noConversionCheck context (pairProgram (depth + 1)) pairType
        (lowerApplicationCode (depth + 1)) = true ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (lowerApplicationCode depth) (pairProgram depth) pairType = some left ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (lowerApplicationCode (depth + 1)) (pairProgram (depth + 1)) pairType = some right ∧
      ∀ env, valid h env → left.value env = right.value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  have formationChecked : check Tower.rules noConversionCheck context
      (.pi (.head zero) pairType) (.head lowerLevel) lowerFormation = true := by decide
  have bodyChecked : check Tower.rules noConversionCheck (.snoc context (.head zero))
      body pairType lowerBodyCode = true := by decide
  have bodyQualified : lowerBodyCode.neutralEliminations body pairType = true := by decide
  have levelUniverse : Tower.rules.isUniverse lowerLevel := by decide
  obtain ⟨leftCheck, rightCheck, left, right, atLeft, atRight, equal⟩ :=
    qualified_common_lambda_applications_coherent heads constants Tower.rules
      TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
      successor_qualified (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
      (empty_constants_model heads constants) context contextCode context_checked
      (context_assembles h constants) (.head zero) pairType body lowerLevel lowerLevel
      levelUniverse levelUniverse lowerFormation lowerFormation (lowerCode depth)
      (lowerCode (depth + 1)) lowerBodyCode lowerBodyCode (program depth)
      (program (depth + 1)) (.var 0) .var .var formationChecked formationChecked
      bodyChecked bodyChecked bodyQualified (lower_checked depth) (lower_checked (depth + 1))
      (lower_argument_qualified depth) (lower_argument_qualified (depth + 1))
      (lower_argument_path depth) (lower_argument_path (depth + 1))
  exact ⟨left, right, leftCheck, rightCheck, atLeft, atRight, equal⟩

/-- The body computes by eliminating the first projection of the existing
dependent pair. Projection was not in the former structural fragment. -/
def projectedBody : Tower.Tm 2 := .fst body

def projectedLowerBodyCode : Replay 2 :=
  .fstElim (.id (.head one) (.var 0) (.var 0)) lowerBodyCode

def projectedUpperBodyCode : Replay 2 :=
  .fstElim (.id (.head one) (.var 0) (.var 0)) upperBodyCode

def projectedLowerFormation : Replay 1 := .piForm one two .headType .headType
def projectedUpperFormation : Replay 1 := .piForm two two .headType .headType

def projectedProgram (depth : Nat) : Tower.Tm 1 :=
  .app (.lam projectedBody) (program depth)

def projectedLowerCode (depth : Nat) : Replay 1 :=
  .appElim (.head zero) (.head one)
    (.lamIntro projectedLowerLevel projectedLowerFormation projectedLowerBodyCode)
    (lowerCode depth)

def projectedUpperCode (depth : Nat) : Replay 1 :=
  .appElim (.head one) (.head one)
    (.lamIntro projectedUpperLevel projectedUpperFormation projectedUpperBodyCode)
    (upperCode depth)

theorem projected_body_supported :
    ZFSetTypeExpressionInterpretation.supported projectedBody = true := by decide

theorem projected_lower_checked (depth : Nat) :
    check Tower.rules noConversionCheck context (projectedProgram depth) (.head one)
      (projectedLowerCode depth) = true := by
  change ((true && check Tower.rules noConversionCheck context (program depth)
    (.head zero) (lowerCode depth)) && true) = true
  simpa only [Bool.true_and, Bool.and_true] using lower_checked depth

theorem projected_upper_checked (depth : Nat) :
    check Tower.rules noConversionCheck context (projectedProgram depth) (.head one)
      (projectedUpperCode depth) = true := by
  change ((true && check Tower.rules noConversionCheck context (program depth)
    (.head one) (upperCode depth)) && true) = true
  simpa only [Bool.true_and, Bool.and_true] using upper_checked depth

/-- A nontrivial dependent body first constructs a proof-carrying pair and
then projects its data component. Independent computations at U₀ and U₁
are checked and compared without a manually supplied body relation. -/
theorem projected_computed_applications_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    ∃ lower upper : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (projectedLowerCode depth) (projectedProgram depth) (.head one) = some lower ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (projectedUpperCode depth) (projectedProgram depth) (.head one) = some upper ∧
      ∀ env, valid h env → lower.value env = upper.value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  exact qualified_cross_domain_lambda_applications_coherent heads constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
    (empty_constants_model heads constants) context contextCode context_checked
    (context_assembles h constants) (.head zero) (.head one) (.head one) (.head one)
    projectedBody projectedLowerLevel projectedUpperLevel projectedLowerFormation
    projectedUpperFormation (lowerCode depth) (upperCode depth)
    projectedLowerBodyCode projectedUpperBodyCode (program depth) (program depth)
    (.var 0) .var (.cumul zero .var) (projected_lower_checked depth)
    (projected_upper_checked depth) (lower_argument_qualified depth)
    (upper_argument_qualified depth) (lower_argument_path depth)
    (upper_argument_path depth) rfl projected_body_supported

/-- The lower checked route computes the current context value, after
constructing a dependent pair, projecting it, and consuming a recursively
computed argument. No erased-term certificate is reconstructed. -/
theorem projected_lower_returns_input (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    ∃ result : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (projectedLowerCode depth) (projectedProgram depth) (.head one) = some result ∧
      ∀ env, valid h env → result.value env = env 0 := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  have formationChecked : check Tower.rules noConversionCheck context
      (.pi (.head zero) (.head one)) (.head projectedLowerLevel)
      projectedLowerFormation = true := by decide
  have bodyChecked : check Tower.rules noConversionCheck (.snoc context (.head zero))
      projectedBody (.head one) projectedLowerBodyCode = true := by decide
  obtain ⟨formed, atFormation, product⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck projectedLowerFormation formationChecked
  obtain ⟨domain, atDomain⟩ := product (.head zero) (.head one) rfl
  obtain ⟨bodyMeaning, atBody, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck projectedLowerBodyCode bodyChecked
  obtain ⟨arg, atArg, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck (lowerCode depth) (lower_checked depth)
  obtain ⟨result, atResult, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck (projectedLowerCode depth) (projected_lower_checked depth)
  refine ⟨result, atResult, ?_⟩
  intro env admitted
  have inside := qualified_argument_in_product_domain heads constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
    (empty_constants_model heads constants) context contextCode (valid h)
    context_checked (context_assembles h constants) projectedLowerLevel (.head zero)
    (.head one) projectedLowerFormation formed domain formationChecked atFormation
    atDomain (program depth) (lowerCode depth) arg (lower_checked depth)
    (lower_argument_qualified depth) atArg env admitted
  have appValue := application_lambda_value heads constants projectedLowerLevel
    (.head zero) (.head one) projectedBody (program depth) projectedLowerFormation
    (lowerCode depth) projectedLowerBodyCode formed arg result bodyMeaning domain
    atFormation atDomain atBody atArg atResult env inside
  obtain ⟨terminalMeaning, atTerminal, pathValue⟩ := QualifiedBetaPath.values
    heads constants Tower.rules TowerDecisions.headTarget
    FormationSensitive.towerUniverseRegularity successor_qualified
    (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
    (empty_constants_model heads constants) contextCode (lower_argument_path depth)
    context_checked (lower_checked depth) (context_assembles h constants) arg atArg
  have bodyValue := agrees_with_type_expressions heads constants projectedLowerBodyCode
    projectedBody (.head one) bodyMeaning projected_body_supported atBody
    (ZFSetTypeExpressionInterpretation.extend env (arg.value env))
  have terminalValue := agrees_with_type_expressions heads constants
    (.var : Replay 1) (.var 0) (.head zero) terminalMeaning rfl atTerminal env
  change terminalMeaning.value env = env 0 at terminalValue
  calc
    result.value env = bodyMeaning.value
        (ZFSetTypeExpressionInterpretation.extend env (arg.value env)) := appValue
    _ = arg.value env := by
      rw [bodyValue]
      simp [projectedBody, body, ZFSetTypeExpressionInterpretation.interpret,
        ZFSetTypeExpressionInterpretation.extend, ZFSetOrderedPair.first_pair]
    _ = terminalMeaning.value env := pathValue env admitted
    _ = env 0 := terminalValue

/-- The independently checked upper-universe route returns the same actual
input, not merely an abstractly related result. -/
theorem projected_both_return_input (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    ∃ lower upper : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (projectedLowerCode depth) (projectedProgram depth) (.head one) = some lower ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (projectedUpperCode depth) (projectedProgram depth) (.head one) = some upper ∧
      ∀ env, valid h env → lower.value env = env 0 ∧ upper.value env = env 0 := by
  obtain ⟨lower, upper, atLower, atUpper, equal⟩ :=
    projected_computed_applications_agree h constants depth
  obtain ⟨actualLower, atActualLower, computes⟩ :=
    projected_lower_returns_input h constants depth
  have same : lower = actualLower := Option.some.inj (atLower.symm.trans atActualLower)
  subst actualLower
  refine ⟨lower, upper, atLower, atUpper, ?_⟩
  intro env admitted
  exact ⟨computes env admitted, (equal env admitted).symm.trans (computes env admitted)⟩

/-- Equal arguments alone do not imply equal application results when the
body comparison is absent. -/
theorem different_bodies_same_argument_not_coherent :
    ZFSetTraceProducts.traceApp
        (ZFSetTraceProducts.traceLam
          (ZFSetDependentProducts.graph ({∅} : ZFSet.{u}) (fun _ => ∅))) ∅ ≠
      ZFSetTraceProducts.traceApp
        (ZFSetTraceProducts.traceLam
          (ZFSetDependentProducts.graph ({∅} : ZFSet.{u}) (fun _ => {∅}))) ∅ :=
  different_functions_same_argument

#print axioms successive_computed_applications_agree
#print axioms projected_computed_applications_agree
#print axioms projected_lower_returns_input
#print axioms projected_both_return_input
#print axioms different_bodies_same_argument_not_coherent

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedLambdaApplicationControls
