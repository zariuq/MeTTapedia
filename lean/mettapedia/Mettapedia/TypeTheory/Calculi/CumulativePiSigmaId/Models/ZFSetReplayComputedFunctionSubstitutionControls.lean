import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayFunctionSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayComputedArgumentControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayComputedArgumentConstantReturn

/-!
# Checked substitution into functions with distinct retained domains

An outer variable is replaced by an arbitrarily deep identity computation.
Two accepted lambda certificates retain different input universes, and their
bodies return the substituted outer value. The generic substitution theorem
checks both transformed certificates and transports the function relation,
formation domains, and exact computed output through the actual replay code.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedFunctionSubstitutionControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetTraceProducts (TraceFunctionRelated traceFunctionRelated_graph_iff
  traceLam traceApp traceApp_graph_beta tracePiSet)
open ZFSetDependentProducts (graph)
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayApplicationComparisonControls (context contextCode context_checked
  context_assembles valid)
open ZFSetReplayComputedArgumentControls (program programMeaning lowerCode lower_checked
  lower_assembles)
open ZFSetReplayComputedArgumentConstantReturn (lowerFormation upperFormation)

universe u

private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev two : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev lowerLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ Tower.zero))
private abbrev upperLevel : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.succ Tower.zero))
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n

def sourceLambda : Tower.Tm 1 := .lam (.var 1)
def lowerType : Tower.Tm 1 := .pi (.head zero) (.head zero)
def upperType : Tower.Tm 1 := .pi (.head one) (.head zero)
def lowerFunctionCode : Replay 1 := .lamIntro lowerLevel lowerFormation .var
def upperFunctionCode : Replay 1 := .lamIntro upperLevel upperFormation .var

noncomputable def lowerFormed (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  ⟨fun _ => tracePiSet (universeSet h ∅ 0) (fun _ => universeSet h ∅ 0),
    some (fun _ => universeSet h ∅ 0)⟩
noncomputable def upperFormed (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  ⟨fun _ => tracePiSet (universeSet h ∅ 1) (fun _ => universeSet h ∅ 0),
    some (fun _ => universeSet h ∅ 1)⟩
noncomputable def lowerMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  .plain (fun env => traceLam (graph (universeSet h ∅ 0) (fun _ => env 0)))
noncomputable def upperMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  .plain (fun env => traceLam (graph (universeSet h ∅ 1) (fun _ => env 0)))

def computedImage (depth : Nat) : Sub Tower.Head 1 1 := fun _ => program depth
def computedImageCode (depth : Nat) : Fin 1 → Replay 1 := fun _ => lowerCode depth
noncomputable def computedImageMeaning (h : CofinalInaccessibles.{u}) (depth : Nat) :
    Fin 1 → Meaning.{u} 1 := fun _ => programMeaning h 0 depth

theorem source_checked :
    check Tower.rules noConversionCheck context sourceLambda lowerType lowerFunctionCode = true ∧
    check Tower.rules noConversionCheck context sourceLambda upperType upperFunctionCode = true ∧
    check Tower.rules noConversionCheck context lowerType (.head lowerLevel)
      lowerFormation = true ∧
    check Tower.rules noConversionCheck context upperType (.head upperLevel)
      upperFormation = true := by
  decide +kernel

/-- A computed image cannot be replaced by the certificate of a variable. -/
theorem forged_computed_image_rejected (depth : Nat) :
    check Tower.rules noConversionCheck context (program (depth + 1)) (.head zero)
      (Code.var : Replay 1) = false := rfl

theorem source_relation (h : CofinalInaccessibles.{u})
    (leftEnv rightEnv : Environment.{u} 1) (same : leftEnv = rightEnv) :
    TraceFunctionRelated (universeSet h ∅ 0) (universeSet h ∅ 1) Eq Eq
      ((lowerMeaning h).value leftEnv) ((upperMeaning h).value rightEnv) := by
  subst rightEnv
  change TraceFunctionRelated (universeSet h ∅ 0) (universeSet h ∅ 1) Eq Eq
    (traceLam (graph (universeSet h ∅ 0) (fun _ => leftEnv 0)))
    (traceLam (graph (universeSet h ∅ 1) (fun _ => leftEnv 0)))
  apply (traceFunctionRelated_graph_iff _ _ Eq Eq _ _).mpr
  intro _ _ _ _ _
  rfl

/-- Even on an inhabited valid context, observational agreement does not
identify the two whole function sets: their retained domains differ. -/
theorem source_relation_does_not_imply_equality (h : CofinalInaccessibles.{u}) :
    ∃ env : Environment.{u} 1, valid h env ∧
      TraceFunctionRelated (universeSet h ∅ 0) (universeSet h ∅ 1) Eq Eq
        ((lowerMeaning h).value env) ((upperMeaning h).value env) ∧
      (lowerMeaning h).value env ≠ (upperMeaning h).value env := by
  let env : Environment.{u} 1 := fun _ => (twoCode h).1
  refine ⟨env, ZFSetReplayApplicationComparisonControls.nonempty_input_valid h,
    source_relation h env env rfl, ?_⟩
  intro equal
  have observed := congrArg (fun f => traceApp f (universeSet h ∅ 0)) equal
  have lower : traceApp ((lowerMeaning h).value env) (universeSet h ∅ 0) = ∅ := by
    change traceApp (traceLam (graph (universeSet h ∅ 0) (fun _ => env 0)))
      (universeSet h ∅ 0) = ∅
    exact ZFSetTraceProducts.traceApp_graph_outside _
      (universeSet_no_self_membership h ∅ 0)
  have upper : traceApp ((upperMeaning h).value env) (universeSet h ∅ 0) =
      (twoCode h).1 := by
    change traceApp (traceLam (graph (universeSet h ∅ 1) (fun _ => env 0)))
      (universeSet h ∅ 0) = (twoCode h).1
    rw [traceApp_graph_beta _ (universeSet_mem_next h ∅ 0)]
  rw [lower, upper] at observed
  have member := ZFSetDependentProducts.Controls.empty_mem_two
  change (∅ : ZFSet.{u}) ∈ (twoCode h).1 at member
  rw [← observed] at member
  exact ZFSet.notMem_empty _ member

/-- The image is a real checked computation of arbitrary finite depth. Its
value appears inside the returned functions, while the two retained domains
remain different. -/
theorem checked_computed_image_transports_functions
    (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
    let image := computedImage depth
    let codes := computedImageCode depth
    check Tower.rules noConversionCheck context (subst image sourceLambda)
      (subst image lowerType)
      (lowerFunctionCode.substitute noConversionRename noConversionSubstitute image codes
        sourceLambda lowerType) = true ∧
    check Tower.rules noConversionCheck context (subst image sourceLambda)
      (subst image upperType)
      (upperFunctionCode.substitute noConversionRename noConversionSubstitute image codes
        sourceLambda upperType) = true ∧
    check Tower.rules noConversionCheck context (subst image lowerType)
      (subst image (.head lowerLevel))
      (lowerFormation.substitute noConversionRename noConversionSubstitute image codes
        lowerType (.head lowerLevel)) = true ∧
    check Tower.rules noConversionCheck context (subst image upperType)
      (subst image (.head upperLevel))
      (upperFormation.substitute noConversionRename noConversionSubstitute image codes
        upperType (.head upperLevel)) = true ∧
    ∃ lower upper lowerProduct upperProduct : Meaning.{u} 1,
      assemble heads constants
        (lowerFunctionCode.substitute noConversionRename noConversionSubstitute image codes
          sourceLambda lowerType)
        (subst image sourceLambda) (subst image lowerType) = some lower ∧
      assemble heads constants
        (upperFunctionCode.substitute noConversionRename noConversionSubstitute image codes
          sourceLambda upperType)
        (subst image sourceLambda) (subst image upperType) = some upper ∧
      assemble heads constants
        (lowerFormation.substitute noConversionRename noConversionSubstitute image codes
          lowerType (.head lowerLevel))
        (subst image lowerType) (subst image (.head lowerLevel)) = some lowerProduct ∧
      assemble heads constants
        (upperFormation.substitute noConversionRename noConversionSubstitute image codes
          upperType (.head upperLevel))
        (subst image upperType) (subst image (.head upperLevel)) = some upperProduct ∧
      lowerProduct.productDomain? = some (fun _ => universeSet h ∅ 0) ∧
      upperProduct.productDomain? = some (fun _ => universeSet h ∅ 1) ∧
      ∀ env, valid h env →
        TraceFunctionRelated (universeSet h ∅ 0) (universeSet h ∅ 1) Eq Eq
          (lower.value env) (upper.value env) ∧
        traceApp (lower.value env) (env 0) = (programMeaning h 0 depth).value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  let image := computedImage depth
  let codes := computedImageCode depth
  let meanings := computedImageMeaning h depth
  have atImages : ∀ i, assemble heads constants (codes i) (image i)
      (subst image (context.lookup i)) = some (meanings i) := by
    intro i
    fin_cases i
    exact lower_assembles h constants depth
  have imagesChecked : ∀ i, check Tower.rules noConversionCheck context (image i)
      (subst image (context.lookup i)) (codes i) = true := by
    intro i
    fin_cases i
    exact lower_checked depth
  have sourceRelated : ∀ leftEnv rightEnv : Environment.{u} 1, leftEnv = rightEnv →
      TraceFunctionRelated (universeSet h ∅ 0) (universeSet h ∅ 1) Eq Eq
        ((lowerMeaning h).value leftEnv) ((upperMeaning h).value rightEnv) :=
    source_relation h
  obtain ⟨leftAccepted, rightAccepted, lowerFormationAccepted, upperFormationAccepted,
    lower, upper, lowerProduct, upperProduct, atLower, atUpper,
    atLowerProduct, atUpperProduct, leftValues, _, lowerDomain,
    upperDomain, related⟩ :=
    checked_function_relations_substitute noConversionRename noConversionSubstitute
      heads constants Tower.rules noConversionCheck
      (fun _ impossible => nomatch impossible)
      (fun _ impossible => nomatch impossible)
      context context context context lowerLevel upperLevel (.head zero) (.head one)
      (.head zero) (.head zero) sourceLambda sourceLambda lowerFunctionCode
      upperFunctionCode lowerFormation upperFormation (lowerMeaning h) (upperMeaning h)
      (lowerFormed h) (upperFormed h) (fun _ => universeSet h ∅ 0)
      (fun _ => universeSet h ∅ 1) source_checked.1 source_checked.2.1
      source_checked.2.2.1 source_checked.2.2.2 rfl rfl rfl rfl rfl rfl
      image image codes codes meanings meanings imagesChecked imagesChecked
      atImages atImages Eq Eq Eq Eq sourceRelated
      (by intro leftEnv rightEnv equal; subst rightEnv; rfl)
  refine ⟨leftAccepted, rightAccepted, lowerFormationAccepted, upperFormationAccepted,
    lower, upper, lowerProduct, upperProduct, atLower, atUpper,
    atLowerProduct, atUpperProduct, lowerDomain, upperDomain, ?_⟩
  intro env admitted
  have observed := related env env rfl
  have inside : env 0 ∈ universeSet h ∅ 0 := admitted.2
  have value : lower.value env = traceLam (graph (universeSet h ∅ 0)
      (fun _ => (programMeaning h 0 depth).value env)) := by
    rw [leftValues]
    rfl
  refine ⟨observed, ?_⟩
  rw [value, traceApp_graph_beta _ inside]

#print axioms source_checked
#print axioms forged_computed_image_rejected
#print axioms source_relation_does_not_imply_equality
#print axioms checked_computed_image_transports_functions

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedFunctionSubstitutionControls
