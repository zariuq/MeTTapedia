import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLLeibnizNativeQualifiedHOTGIntegration
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLProofQualifiedExecutionCospan

/-!
# The retained HOL map-fusion proof at actual HOTG operations and native paths

This module closes the concrete square between the recursively compiled HOL
proof, its HOTG interpretation, dependent proof consumption, native beta/iota
execution, and generated modal observation.

The two HOTG functions are supplied as values of a displayed native context.
The native programs refer to those values by variables, so their reduction is
the ordinary open-term List computation already used by the general
proof-qualified execution cospan.  Instantiating the context with the actual
least-universe and powerset maps makes the extensional apex observation
literal in the same trace-coded set carrier as the compiled proof.

The extensional and operational readings remain deliberately different.  Both
programs reach one constructor spine and hence satisfy the same
equation-invariant possibility observation, while their exact chronological
histories have different lengths.  No quotient of histories or effectful
fusion principle is inferred.
-/

open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLLeibnizNativeQualifiedHOTGOperationalIntegration

open Presentation NativeIndexedFamilies IntrinsicNativeListMapComputation
open NativeHOLTraceRecursiveExtensionalCompilerSemantics
open NativeHOLRecursiveProofOperationalObservation
open NativeHOLProofFamilyOperationalQualification
open NativeHOLProofQualifiedExecutionCospan
open NativeHOLProofQualifiedOperationalCospan.MapFusionPrograms
open NativeHOLRecursiveProofNIKQualification.Controls
open HOLLeibnizNativeQualifiedHOTGIntegration
open Mettapedia.GSLT.Dynamics.ExecutionPathObservation
open Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniformListTraceTypeInterpretation
open ZFSetUniverseClosure ZFSetUniverseLift

universe u

/-! ## One displayed context for the actual HOTG instance -/

/-- Two function variables followed by one element variable.  The semantic
environment will assign the actual HOTG least-universe map, powerset map, and
input set respectively. -/
noncomputable def operationContext :
    NativeTraceLambdaSemantics.Context.{u + 1} 3 :=
  let first := NativeTraceLambdaSemantics.Context.nil.snoc
    (NativeHOLTraceDisplayedTerms.typeFamily carrierCode.{u}
      NativeTraceLambdaSemantics.Context.nil mapping)
  let second := first.snoc
    (NativeHOLTraceDisplayedTerms.typeFamily carrierCode.{u} first mapping)
  second.snoc
    (NativeHOLTraceDisplayedTerms.typeFamily carrierCode.{u} second element)

/-- The oldest variable is the least-universe map. -/
def universeTerm : Tower.Tm 3 := .var 2

/-- The middle variable is the powerset map. -/
def powerTerm : Tower.Tm 3 := .var 1

/-- The newest variable is the singleton input. -/
def inputTerm : Tower.Tm 3 := .var 0

noncomputable def universeMeaning :
    FunctionMeaning carrierCode.{u} operationContext :=
  operationContext.projection 2

noncomputable def powerMeaning :
    FunctionMeaning carrierCode.{u} operationContext :=
  operationContext.projection 1

noncomputable def inputMeaning :
    ElementMeaning carrierCode.{u} operationContext :=
  operationContext.projection 0

noncomputable def inputHeads : Heads carrierCode.{u} operationContext :=
  [(inputTerm, inputMeaning)]

/-- Assign the three variables their actual HOTG values. -/
noncomputable def operationEnvironment
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) : operationContext.Environment :=
  ⟨⟨⟨PUnit.unit,
      NativeHOLCompiledMapFusionHOTG.universeMap lower⟩,
      NativeHOLCompiledMapFusionHOTG.powerMap⟩,
    x⟩

@[simp] theorem operation_projection_universe
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    universeMeaning (operationEnvironment lower x) =
      NativeHOLCompiledMapFusionHOTG.universeMap lower :=
  rfl

@[simp] theorem operation_projection_power
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    powerMeaning (operationEnvironment lower x) =
      NativeHOLCompiledMapFusionHOTG.powerMap :=
  rfl

@[simp] theorem operation_projection_input
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    inputMeaning (operationEnvironment lower x) = x :=
  rfl

theorem universeTerm_denotes :
    NativeHOLTraceDisplayedTerms.Denotes carrierCode.{u} operationContext
      universeTerm universeMeaning := by
  exact NativeHOLTraceDisplayedTerms.Denotes.variable 2
    (NativeTraceLambdaSemantics.Denotes.var _ 2)

theorem powerTerm_denotes :
    NativeHOLTraceDisplayedTerms.Denotes carrierCode.{u} operationContext
      powerTerm powerMeaning := by
  exact NativeHOLTraceDisplayedTerms.Denotes.variable 1
    (NativeTraceLambdaSemantics.Denotes.var _ 1)

theorem inputTerm_denotes :
    NativeHOLTraceDisplayedTerms.Denotes carrierCode.{u} operationContext
      inputTerm inputMeaning := by
  exact NativeHOLTraceDisplayedTerms.Denotes.variable 0
    (NativeTraceLambdaSemantics.Denotes.var _ 0)

theorem inputHeads_denote :
    ∀ head ∈ inputHeads,
      NativeHOLTraceDisplayedTerms.Denotes carrierCode.{u} operationContext
        head.1 head.2 := by
  intro head member
  simp only [inputHeads, List.mem_singleton] at member
  subst head
  exact inputTerm_denotes

@[simp] theorem inputHeads_values
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    headValues inputHeads (operationEnvironment lower x) = [x] :=
  rfl

/-! ## The actual proof-qualified HOTG execution -/

/-- The concrete extensional output: first powerset, then the least universe
containing the result. -/
noncomputable def expectedOutput
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) : Value carrierCode.{u} sequence :=
  ZFSetList.encodeValue
    [app (NativeHOLCompiledMapFusionHOTG.universeMap lower)
      (app NativeHOLCompiledMapFusionHOTG.powerMap x)]

/-- Decoding the head of the common output gives the actual HOTG composite:
the least closed universe containing the powerset of the input. -/
theorem expected_head_decoding
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    carrierEquiv
        (app (NativeHOLCompiledMapFusionHOTG.universeMap lower)
          (app NativeHOLCompiledMapFusionHOTG.powerMap x)) =
      ZFSetUniverseClosure.univOf lower
        (ZFSet.powerset (carrierEquiv x)) := by
  rw [NativeHOLCompiledMapFusionHOTG.decode_universeMap,
    NativeHOLCompiledMapFusionHOTG.decode_powerMap]

theorem unfused_meaning_is_expected
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    ZFSetUniformListTraceProofBridge.beforeSection
        (universeMeaning (operationEnvironment lower x))
        (powerMeaning (operationEnvironment lower x))
        (ZFSetList.encodeValue
          (headValues inputHeads (operationEnvironment lower x)))
        PUnit.unit =
      expectedOutput lower x := by
  rw [operation_projection_universe, operation_projection_power,
    inputHeads_values, beforeSection_encodeValue]
  rfl

/-- The actual native program pair at the three variables of
`operationContext`. -/
def programs : NativeHOLProofQualifiedOperationalCospan.MapFusionPrograms 3 :=
  NativeHOLProofQualifiedOperationalCospan.nativeListPrograms
    universeTerm powerTerm [inputTerm]

/-- The observation is equality with the actual HOTG list result, interpreted
in the same trace-coded carrier used by the recursive compiler. -/
noncomputable def observation (level : LevelExpr Nat)
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :=
  semanticObservation level (operationEnvironment lower x)
    (fun output => output = expectedOutput lower x)

/-- One object now retains the source induction proof, exact compiler output,
formation-sensitive dependent typing, Aczel-trace denotation, both native
execution paths, and the common equation-invariant HOTG observation. -/
noncomputable def executionCospan (level : LevelExpr Nat)
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    ProofQualifiedExecutionCospan (reduction level 3)
      (ConnectedIntrinsicEvidence carrierCode.{u})
      (CompiledProofQualifies
        (NativeHOLProofFamilyOperationalQualification.MapFusion.specification
          level))
      (observation level lower x) programs.unfused programs.fused := by
  exact NativeHOLProofQualifiedExecutionCospan.MapFusion.recursiveExecutionCospan
    level universeTerm powerTerm universeMeaning powerMeaning
      universeTerm_denotes powerTerm_denotes inputHeads inputHeads_denote
      (operationEnvironment lower x)
      (fun output => output = expectedOutput lower x)
      (unfused_meaning_is_expected lower x)

/-- The operational object retains the original HOL induction tree, not only
its conclusion or an extensionally equal replacement proof. -/
theorem execution_retains_source (level : LevelExpr Nat)
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    (executionCospan level lower x).evidence.proof = retainedMapFusionProof :=
  NativeHOLProofQualifiedExecutionCospan.MapFusion.recursiveExecutionCospan_retains_source
    level universeTerm powerTerm universeMeaning powerMeaning
      universeTerm_denotes powerTerm_denotes inputHeads inputHeads_denote
      (operationEnvironment lower x)
      (fun output => output = expectedOutput lower x)
      (unfused_meaning_is_expected lower x)

/-- Endpoint qualification pins the evidence to the exact recursively emitted
closed native proof. -/
theorem execution_retains_native_compilation (level : LevelExpr Nat)
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    (executionCospan level lower x).evidence.native =
      HOLLeibnizMapFusionNative.nativeProof :=
  (executionCospan level lower x).qualification.2.1

/-- For the singleton input, the unfused and fused native executions take
eighteen and ten primitive beta/iota steps respectively. -/
theorem execution_path_lengths (level : LevelExpr Nat)
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    (executionCospan level lower x).leftPath.length = 18 ∧
      (executionCospan level lower x).rightPath.length = 10 := by
  change
    (NativeHOLProofQualifiedExecutionCospan.MapFusion.programPaths
      level programs).1.length = 18 ∧
    (NativeHOLProofQualifiedExecutionCospan.MapFusion.programPaths
      level programs).2.length = 10
  simpa [programs,
    NativeHOLProofQualifiedOperationalCospan.nativeListPrograms] using
    NativeHOLProofQualifiedExecutionCospan.MapFusion.programPath_lengths
      level programs

/-- The common extensional result does not collapse chronological
provenance. -/
theorem execution_histories_differ (level : LevelExpr Nat)
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    ofDiscipline
        (ProofQualifiedExecutionCospan.exactHistory (reduction level 3))
        (executionCospan level lower x).leftPath ≠
      ofDiscipline
        (ProofQualifiedExecutionCospan.exactHistory (reduction level 3))
        (executionCospan level lower x).rightPath :=
  NativeHOLProofQualifiedExecutionCospan.MapFusion.recursiveExecutionCospan_exact_histories_differ
    level universeTerm powerTerm universeMeaning powerMeaning
      universeTerm_denotes powerTerm_denotes inputHeads inputHeads_denote
      (operationEnvironment lower x)
      (fun output => output = expectedOutput lower x)
      (unfused_meaning_is_expected lower x)

/-- Both programs satisfy the same generated possibility observation on the
equation class of their common result. -/
theorem execution_semantic_diamonds (level : LevelExpr Nat)
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond
        (reduction level 3).closure (observation level lower x)
        programs.unfused ∧
      Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond
        (reduction level 3).closure (observation level lower x)
        programs.fused :=
  (executionCospan level lower x).semanticDiamonds

/-- The common HOTG result is exposed at the quotient level used by generated
modal logic.  This statement continues to make sense when a later
presentation replaces syntactic equality by nontrivial authored equations. -/
theorem execution_quotient_result_observed (level : LevelExpr Nat)
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    Mettapedia.OSLF.Framework.GSLTTypeSynthesis.descendPredicate
        (reduction level 3).closure (observation level lower x)
        (Quotient.mk (reduction level 3).closure.equations
          (executionCospan level lower x).apex) :=
  (executionCospan level lower x).quotient_apex_observed

/-! ## One visible theorem package, with the boundaries retained -/

/-- The literal commuting instance, stated without identifying the two
execution histories.  The dependent consumer and the operational cospan both
originate in the same retained source proof and actual HOTG specialization. -/
theorem connected_hotg_map_fusion (level : LevelExpr Nat)
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    (executionCospan level lower x).evidence.proof = retainedMapFusionProof ∧
      (executionCospan level lower x).evidence.native =
        HOLLeibnizMapFusionNative.nativeProof ∧
      (HOLLeibnizNativeQualifiedHOTGIntegration.HOTG.hotgConsumedEndpoint
        lower (ZFSetList.encodeValue [x])).1 =
        (HOLLeibnizNativeQualifiedHOTGIntegration.DependentConsumption.recursiveFusionIdentityPoint
          (NativeHOLCompiledMapFusionHOTG.universeMap lower)
          NativeHOLCompiledMapFusionHOTG.powerMap
          (ZFSetList.encodeValue [x])).1.1.2.1 ∧
      (executionCospan level lower x).leftPath.length = 18 ∧
      (executionCospan level lower x).rightPath.length = 10 ∧
      Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond
        (reduction level 3).closure (observation level lower x)
        programs.unfused ∧
      Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond
        (reduction level 3).closure (observation level lower x)
        programs.fused ∧
      ofDiscipline
          (ProofQualifiedExecutionCospan.exactHistory (reduction level 3))
          (executionCospan level lower x).leftPath ≠
        ofDiscipline
          (ProofQualifiedExecutionCospan.exactHistory (reduction level 3))
          (executionCospan level lower x).rightPath := by
  exact ⟨execution_retains_source level lower x,
    execution_retains_native_compilation level lower x,
    HOLLeibnizNativeQualifiedHOTGIntegration.HOTG.hotgConsumedEndpoint_value
      lower (ZFSetList.encodeValue [x]),
    (execution_path_lengths level lower x).1,
    (execution_path_lengths level lower x).2,
    (execution_semantic_diamonds level lower x).1,
    (execution_semantic_diamonds level lower x).2,
    execution_histories_differ level lower x⟩

/-- Universe closure is not hidden by the operational composition: a separate
higher-ambient assumption is still required to internalize the concrete proof
value. -/
theorem connected_proof_value_small
    (lower : CofinalInaccessibles.{u})
    (upper : CofinalInaccessibles.{u + 1})
    (x : Value carrierCode.{u} element) :
    (HOLLeibnizNativeQualifiedHOTGIntegration.HOTG.hotgFusionProofValue lower
      (ZFSetList.encodeValue [x])).1 ∈
      ZFSetInterpretation.universeSet upper
        (ZFSetIndexedClosure.seed carrierCode.{u}) 0 :=
  HOLLeibnizNativeQualifiedHOTGIntegration.HOTG.hotgFusionProofValue_small
    lower upper (ZFSetList.encodeValue [x])

/-- Negative boundary: the modal observation is equation-invariant, but exact
history still distinguishes the two executions. -/
theorem common_modal_result_does_not_identify_history (level : LevelExpr Nat)
    (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond
        (reduction level 3).closure (observation level lower x)
        programs.unfused ∧
      Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond
        (reduction level 3).closure (observation level lower x)
        programs.fused) ∧
      ofDiscipline
          (ProofQualifiedExecutionCospan.exactHistory (reduction level 3))
          (executionCospan level lower x).leftPath ≠
        ofDiscipline
          (ProofQualifiedExecutionCospan.exactHistory (reduction level 3))
          (executionCospan level lower x).rightPath :=
  ⟨execution_semantic_diamonds level lower x,
    execution_histories_differ level lower x⟩

#print axioms operation_projection_universe
#print axioms universeTerm_denotes
#print axioms expected_head_decoding
#print axioms unfused_meaning_is_expected
#print axioms execution_retains_source
#print axioms execution_retains_native_compilation
#print axioms execution_path_lengths
#print axioms execution_histories_differ
#print axioms execution_semantic_diamonds
#print axioms execution_quotient_result_observed
#print axioms connected_hotg_map_fusion
#print axioms connected_proof_value_small
#print axioms common_modal_result_does_not_identify_history

end HOLLeibnizNativeQualifiedHOTGOperationalIntegration
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
