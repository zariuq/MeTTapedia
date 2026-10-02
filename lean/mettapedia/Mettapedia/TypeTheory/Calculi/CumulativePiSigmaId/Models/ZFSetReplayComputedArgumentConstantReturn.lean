import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayQualifiedApplicationControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedComputation

/-!
# A computed argument in two checked constant-returning applications

The argument is an arbitrary finite nest of identity applications. Two
accepted trees retain different universe domains for the outer lambda. Its
body returns the older context variable, so the checked contraction has a
structural reduct even when the argument is non-neutral. This exercises the
supported-reduct comparison without identifying the argument with a variable
or treating a reduction trace as typing authority.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedArgumentConstantReturn

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayUniverseModel (universeModel empty_constants_model successor_qualified)
open ZFSetReplayApplicationComparisonControls (context contextCode context_checked context_assembles valid)
open ZFSetReplayComputedArgumentControls (program lowerCode upperCode lower_checked upper_checked)
open ZFSetReplayQualifiedApplicationControls (lower_argument_qualified upper_argument_qualified)

universe u

private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev two : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n

def term (depth : Nat) : Tower.Tm 1 :=
  .app (.lam (.var 1)) (program depth)

def lowerFormation : Replay 1 := .piForm one one .headType .headType
def upperFormation : Replay 1 := .piForm two one .headType .headType

def lowerApplicationCode (depth : Nat) : Replay 1 :=
  .appElim (.head zero) (.head zero)
    (.lamIntro (.sort (.max (.succ Tower.zero) (.succ Tower.zero))) lowerFormation .var)
    (lowerCode depth)

def upperApplicationCode (depth : Nat) : Replay 1 :=
  .appElim (.head one) (.head zero)
    (.lamIntro (.sort (.max (.succ (.succ Tower.zero)) (.succ Tower.zero))) upperFormation .var)
    (upperCode depth)

theorem lower_checked (depth : Nat) :
    check Tower.rules noConversionCheck context (term depth) (.head zero)
      (lowerApplicationCode depth) = true := by
  change ((true && check Tower.rules noConversionCheck context (program depth)
    (.head zero) (lowerCode depth)) && true) = true
  simpa only [Bool.true_and, Bool.and_true] using
    ZFSetReplayComputedArgumentControls.lower_checked depth

theorem upper_checked (depth : Nat) :
    check Tower.rules noConversionCheck context (term depth) (.head zero)
      (upperApplicationCode depth) = true := by
  change ((true && check Tower.rules noConversionCheck context (program depth)
    (.head one) (upperCode depth)) && true) = true
  simpa only [Bool.true_and, Bool.and_true] using
    ZFSetReplayComputedArgumentControls.upper_checked depth

theorem lower_qualified (depth : Nat) :
    (lowerApplicationCode depth).resultFormationsNeutral Tower.rules TowerDecisions.headTarget
      contextCode (term depth) (.head zero) = true := by
  change (true && (true && (lowerCode depth).resultFormationsNeutral Tower.rules
    TowerDecisions.headTarget contextCode (program depth) (.head zero))) = true
  simpa only [Bool.true_and] using lower_argument_qualified depth

theorem upper_qualified (depth : Nat) :
    (upperApplicationCode depth).resultFormationsNeutral Tower.rules TowerDecisions.headTarget
      contextCode (term depth) (.head zero) = true := by
  change (true && (true && (upperCode depth).resultFormationsNeutral Tower.rules
    TowerDecisions.headTarget contextCode (program depth) (.head one))) = true
  simpa only [Bool.true_and] using upper_argument_qualified depth

/-- The actual source argument is non-neutral from the first beta step on. -/
theorem computed_argument_not_neutral (depth : Nat) :
    (program (depth + 1)).neutral = false := rfl

/-- A variable certificate does not authorize the computed argument. -/
theorem erased_argument_rejected (depth : Nat) :
    check Tower.rules noConversionCheck context (term (depth + 1)) (.head zero)
      (.appElim (.head zero) (.head zero)
        (.lamIntro (.sort (.max (.succ Tower.zero) (.succ Tower.zero))) lowerFormation .var)
        (.var : Replay 1)) = false := by
  rfl

theorem lower_contracts (depth : Nat) :
    (lowerApplicationCode depth).contractBeta (.var 1) (program depth) (.head zero) =
      some (.var : Replay 1) := rfl

theorem upper_contracts (depth : Nat) :
    (upperApplicationCode depth).contractBeta (.var 1) (program depth) (.head zero) =
      some (.var : Replay 1) := rfl

/-- The two accepted executions agree on every admitted environment despite
their distinct Π-domains and arbitrarily deep computed arguments. -/
theorem checked_values_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    ∃ lower upper : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (lowerApplicationCode depth) (term depth) (.head zero) = some lower ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (upperApplicationCode depth) (term depth) (.head zero) = some upper ∧
      ∀ env : Environment.{u} 1, valid h env → lower.value env = upper.value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  obtain ⟨lower, atLower, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck (lowerApplicationCode depth) (lower_checked depth)
  obtain ⟨upper, atUpper, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck (upperApplicationCode depth) (upper_checked depth)
  refine ⟨lower, upper, atLower, atUpper, ?_⟩
  exact qualified_rootBeta_coherent_of_supported_reduct heads constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity successor_qualified
    (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
    (empty_constants_model heads constants) contextCode
    (lowerApplicationCode depth) (upperApplicationCode depth) lower upper
    context_checked (lower_checked depth) (upper_checked depth)
    (lower_qualified depth) (upper_qualified depth) (context_assembles h constants)
    atLower atUpper rfl

/-- The left checked program genuinely returns the outer variable. Its
computed argument still has to pass checking and domain admission. -/
theorem lower_returns_context_value (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat)
    (result : Meaning.{u} 1)
    (atResult : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (lowerApplicationCode depth) (term depth) (.head zero) = some result)
    (env : Environment.{u} 1) (admitted : valid h env) :
    result.value env = env 0 := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  obtain ⟨_, contracted, _, _, atContracted, preserved⟩ :=
    qualified_contractBeta heads constants Tower.rules TowerDecisions.headTarget
      FormationSensitive.towerUniverseRegularity successor_qualified
      (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
      (empty_constants_model heads constants) contextCode
      (lowerApplicationCode depth) result context_checked (lower_checked depth)
      (lower_qualified depth) (context_assembles h constants) atResult
  have atVariable : assemble heads constants (Code.var : Replay 1)
      (.var 0) (.head zero) = some (Meaning.plain (fun e : Environment.{u} 1 => e 0)) := rfl
  have same := assemble_supported_values heads constants
    (by rfl : ZFSetTypeExpressionInterpretation.supported
      (inst0 (program depth) (.var 1)) = true) atContracted atVariable
  calc
    result.value env = contracted.value env := preserved env admitted
    _ = env 0 := congrFun same env

/-- The compared behaviour is not a constant semantic value: two valid
set-valued inputs are distinguished by the checked program. -/
theorem lower_result_distinguishes_inputs (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat)
    (result : Meaning.{u} 1)
    (atResult : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (lowerApplicationCode depth) (term depth) (.head zero) = some result) :
    result.value (fun _ => ∅) ≠ result.value (fun _ => (twoCode h).1) := by
  rw [lower_returns_context_value h constants depth result atResult _
      ⟨True.intro, seed_mem_universeSet h ∅ (0 : Nat)⟩,
    lower_returns_context_value h constants depth result atResult _
      (ZFSetReplayApplicationComparisonControls.nonempty_input_valid h)]
  intro equal
  have member := ZFSetDependentProducts.Controls.empty_mem_two
  change (∅ : ZFSet.{u}) ∈ (twoCode h).1 at member
  rw [← equal] at member
  exact ZFSet.notMem_empty _ member

/-- A checked two-certificate consumer for every finite computation depth:
both paths return the outer input, and the input dependence is witnessed by
two distinct admissible set codes. -/
theorem checked_computed_argument_consumer (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    ∃ lower upper : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (lowerApplicationCode depth) (term depth) (.head zero) = some lower ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (upperApplicationCode depth) (term depth) (.head zero) = some upper ∧
      (∀ env : Environment.{u} 1, valid h env →
        lower.value env = upper.value env ∧ lower.value env = env 0) ∧
      lower.value (fun _ => ∅) ≠ lower.value (fun _ => (twoCode h).1) := by
  obtain ⟨lower, upper, atLower, atUpper, agree⟩ :=
    checked_values_agree h constants depth
  exact ⟨lower, upper, atLower, atUpper,
    (fun env admitted => ⟨agree env admitted,
      lower_returns_context_value h constants depth lower atLower env admitted⟩),
    lower_result_distinguishes_inputs h constants depth lower atLower⟩

#print axioms lower_checked
#print axioms upper_checked
#print axioms lower_qualified
#print axioms upper_qualified
#print axioms erased_argument_rejected
#print axioms lower_contracts
#print axioms upper_contracts
#print axioms checked_values_agree
#print axioms lower_returns_context_value
#print axioms lower_result_distinguishes_inputs
#print axioms checked_computed_argument_consumer

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedArgumentConstantReturn
