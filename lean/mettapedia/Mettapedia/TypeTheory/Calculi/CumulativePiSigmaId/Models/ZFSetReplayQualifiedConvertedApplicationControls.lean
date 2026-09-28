import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedConvertedApplication
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayQualifiedHeadConversionControls

/-!
# A computed dependent argument used after a retained head conversion

The program constructs a dependent pair, projects its first component, and
passes that computed result to an identity lambda. The argument certificate
is originally checked at one universe head; the application consumes it at a
different, extensionally equal head through a retained conversion receipt.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedConvertedApplicationControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.SetTheory
open ZFSetTypeExpressionInterpretation (Environment extend)
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayUniverseModel (universeModel empty_constants_model successor_qualified)
open ZFSetReplayApplicationComparisonControls
  (context contextCode context_checked context_assembles valid reduct)
open ZFSetReplaySupportedLambdaControls
  (computedArgument computedArgumentCode computed_argument_checked
    computed_argument_qualified computed_argument_supported)
open ZFSetReplayQualifiedHeadConversionControls
  (SourceHead TargetHead SourceLevel TargetLevel EmptyRoot noRootDecode heads_related)
open ZFSetUniverseClosure (CofinalInaccessibles)

universe u

local instance : DecidableRel Tower.rules.headEq := Tower.instDecidableHeadEq

private abbrev ProductLevel : Tower.Head :=
  .sort (.max (.succ (.max Tower.zero (.succ Tower.zero)))
    (.succ (.max Tower.zero (.succ Tower.zero))))

def productFormation : Code Tower.Head NoConversion 1 :=
  .piForm TargetLevel TargetLevel .headType .headType

def bodyCode : Code Tower.Head NoConversion 2 := .var

def convertedProgram : Tower.Tm 1 := .app (.lam (.var 0)) computedArgument

def convertedApplicationCode :
    Code Tower.Head (StructuralConversionCode.Code Tower.Head EmptyRoot) 1 :=
  .appElim (.head TargetHead) (.head TargetHead)
    (.lamIntro ProductLevel
      (productFormation.mapConversion (fun impossible => nomatch impossible))
      (bodyCode.mapConversion (fun impossible => nomatch impossible)))
    (headConvertedCode (RootCode := EmptyRoot) computedArgumentCode
      SourceHead TargetHead TargetLevel)

theorem product_formation_checked :
    check Tower.rules noConversionCheck context
      (.pi (.head TargetHead) (.head TargetHead)) (.head ProductLevel)
      productFormation = true := by decide +kernel

theorem body_checked :
    check Tower.rules noConversionCheck (.snoc context (.head TargetHead))
      (.var 0) (.head TargetHead) bodyCode = true := by decide +kernel

/-- The source certificate does not already check at the target syntax.
The retained conversion is necessary for this application. -/
theorem unconverted_argument_rejected_at_target :
    check Tower.rules noConversionCheck context computedArgument
      (.head TargetHead) computedArgumentCode = false := by decide +kernel

/-- The checked application uses the converted non-variable argument at the
product's retained domain and returns the live context value. -/
theorem converted_computed_application_returns_input
    (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
    ∃ result : Meaning.{u} 1,
      check Tower.rules (headStepCheck Tower.rules noRootDecode) context
        convertedProgram (.head TargetHead) convertedApplicationCode = true ∧
      assemble heads constants convertedApplicationCode convertedProgram
        (.head TargetHead) = some result ∧
      ∀ env : Environment.{u} 1, valid h env → result.value env = env 0 := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  obtain ⟨arg, result, bodyMeaning, checked, atArgument, atResult,
      atBody, value⟩ :=
    qualified_head_converted_lambda_application Tower.rules noRootDecode heads
      constants
      (fun left right related =>
        ZFSetReplayUniverseFormation.headEq_values h ∅ (twoCode h).1
          (fun _ => 0) related)
      TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
      successor_qualified
      (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
      (empty_constants_model heads constants)
      context contextCode (valid h) context_checked (context_assembles h constants)
      ProductLevel SourceHead TargetHead SourceLevel TargetLevel
      (.head TargetHead) (.var 0) computedArgument productFormation bodyCode
      computedArgumentCode (Tower.IsUniverse.sort _)
      product_formation_checked body_checked computed_argument_checked
      computed_argument_qualified (Tower.HeadTyping.sort _)
      (Tower.HeadTyping.sort _) (Tower.IsUniverse.sort _) heads_related
  have headInst : inst0 computedArgument (.head TargetHead) =
      (.head TargetHead : Tower.Tm 1) := rfl
  refine ⟨result, ?_, ?_, ?_⟩
  · change check Tower.rules (headStepCheck Tower.rules noRootDecode) context
        (.app (.lam (.var 0)) computedArgument)
        (.head TargetHead)
        (.appElim (.head TargetHead) (.head TargetHead)
          (.lamIntro ProductLevel
            (productFormation.mapConversion (fun impossible => nomatch impossible))
            (bodyCode.mapConversion (fun impossible => nomatch impossible)))
          (headConvertedCode (RootCode := EmptyRoot) computedArgumentCode
            SourceHead TargetHead TargetLevel)) = true
    rw [← headInst]
    exact checked
  · change assemble heads constants convertedApplicationCode convertedProgram
        (.head TargetHead) = some result
    rw [← headInst]
    exact atResult
  · intro env admitted
    have bodyValue := agrees_with_type_expressions heads constants
      (bodyCode.mapConversion
        (fun {n} (impossible : NoConversion n) =>
          (nomatch impossible : StructuralConversionCode.Code Tower.Head EmptyRoot n)))
      (.var 0) (.head TargetHead) bodyMeaning rfl atBody
      (extend env (arg.value env))
    have argumentValue := agrees_with_type_expressions heads constants
      (headConvertedCode (RootCode := EmptyRoot) computedArgumentCode
        SourceHead TargetHead TargetLevel)
      computedArgument (.head TargetHead) arg computed_argument_supported
      atArgument env
    calc
      result.value env = bodyMeaning.value (extend env (arg.value env)) :=
        value env admitted
      _ = arg.value env := by
        simpa [ZFSetTypeExpressionInterpretation.interpret,
          ZFSetTypeExpressionInterpretation.extend] using bodyValue
      _ = env 0 := by
        simpa [computedArgument, reduct,
          ZFSetTypeExpressionInterpretation.interpret,
          ZFSetOrderedPair.first_pair] using argumentValue

/-- The result type mentions the computed argument after substitution. -/
def dependentFamily : Tower.Tm 2 :=
  .id (.head TargetHead) (.var 0) (.var 0)

def proofBody : Tower.Tm 2 := .refl (.var 0)

def dependentProductFormation : Code Tower.Head NoConversion 1 :=
  .piForm TargetLevel TargetLevel .headType
    (.idForm TargetLevel .headType .var .var)

def proofBodyCode : Code Tower.Head NoConversion 2 :=
  .reflIntro (.head TargetHead) .var

def dependentProgram : Tower.Tm 1 := .app (.lam proofBody) computedArgument

def dependentApplicationCode :
    Code Tower.Head (StructuralConversionCode.Code Tower.Head EmptyRoot) 1 :=
  .appElim (.head TargetHead) dependentFamily
    (.lamIntro ProductLevel
      (dependentProductFormation.mapConversion
        (fun impossible => nomatch impossible))
      (proofBodyCode.mapConversion (fun impossible => nomatch impossible)))
    (headConvertedCode (RootCode := EmptyRoot) computedArgumentCode
      SourceHead TargetHead TargetLevel)

theorem dependent_formation_checked :
    check Tower.rules noConversionCheck context
      (.pi (.head TargetHead) dependentFamily) (.head ProductLevel)
      dependentProductFormation = true := by decide +kernel

theorem proof_body_checked :
    check Tower.rules noConversionCheck (.snoc context (.head TargetHead))
      proofBody dependentFamily proofBodyCode = true := by decide +kernel

/-- A converted computed projection is consumed by a dependent lambda, whose
result is a retained reflexivity proof at the instantiated identity type. -/
theorem dependent_converted_application_returns_proof
    (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) :
    let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
    ∃ result : Meaning.{u} 1,
      check Tower.rules (headStepCheck Tower.rules noRootDecode) context
        dependentProgram (inst0 computedArgument dependentFamily)
        dependentApplicationCode = true ∧
      assemble heads constants dependentApplicationCode dependentProgram
        (inst0 computedArgument dependentFamily) = some result ∧
      ∀ env : Environment.{u} 1, valid h env → result.value env = ∅ := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  obtain ⟨arg, result, bodyMeaning, checked, _, atResult, atBody, value⟩ :=
    qualified_head_converted_lambda_application Tower.rules noRootDecode heads
      constants
      (fun left right related =>
        ZFSetReplayUniverseFormation.headEq_values h ∅ (twoCode h).1
          (fun _ => 0) related)
      TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
      successor_qualified
      (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
      (empty_constants_model heads constants)
      context contextCode (valid h) context_checked (context_assembles h constants)
      ProductLevel SourceHead TargetHead SourceLevel TargetLevel
      dependentFamily proofBody computedArgument dependentProductFormation
      proofBodyCode computedArgumentCode (Tower.IsUniverse.sort _)
      dependent_formation_checked proof_body_checked computed_argument_checked
      computed_argument_qualified (Tower.HeadTyping.sort _)
      (Tower.HeadTyping.sort _) (Tower.IsUniverse.sort _) heads_related
  refine ⟨result, ?_, ?_, ?_⟩
  · change check Tower.rules (headStepCheck Tower.rules noRootDecode) context
        (.app (.lam proofBody) computedArgument)
        (inst0 computedArgument dependentFamily)
        (.appElim (.head TargetHead) dependentFamily
          (.lamIntro ProductLevel
            (dependentProductFormation.mapConversion
              (fun impossible => nomatch impossible))
            (proofBodyCode.mapConversion (fun impossible => nomatch impossible)))
          (headConvertedCode (RootCode := EmptyRoot) computedArgumentCode
            SourceHead TargetHead TargetLevel)) = true
    exact checked
  · change assemble heads constants dependentApplicationCode dependentProgram
        (inst0 computedArgument dependentFamily) = some result
    exact atResult
  · intro env admitted
    have bodyValue := agrees_with_type_expressions heads constants
      (proofBodyCode.mapConversion
        (fun {n} (impossible : NoConversion n) =>
          (nomatch impossible : StructuralConversionCode.Code Tower.Head EmptyRoot n)))
      proofBody dependentFamily bodyMeaning rfl atBody
      (extend env (arg.value env))
    calc
      result.value env = bodyMeaning.value (extend env (arg.value env)) :=
        value env admitted
      _ = ∅ := by
        simpa [proofBody, ZFSetTypeExpressionInterpretation.interpret] using bodyValue

#print axioms product_formation_checked
#print axioms body_checked
#print axioms unconverted_argument_rejected_at_target
#print axioms converted_computed_application_returns_input
#print axioms dependent_formation_checked
#print axioms proof_body_checked
#print axioms dependent_converted_application_returns_proof

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedConvertedApplicationControls
