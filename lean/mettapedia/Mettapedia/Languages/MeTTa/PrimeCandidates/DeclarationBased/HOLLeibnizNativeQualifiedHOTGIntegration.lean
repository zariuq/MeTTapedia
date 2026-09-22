import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLLeibnizNativeQualifiedIntegration
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeProofCoverage
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLCompiledMapFusionHOTG

/-!
# The qualified recursive HOL compiler composed with the HOTG interpretation

This module connects the general recursive compiler package to the existing
set-theoretic map-fusion interpretation.  The connection retains the original
HOL induction proof: on the constructive source fragment, the recursive
extensional compiler emits exactly the term emitted by the earlier
constructive compiler.  The established HOTG interpretation and dependent
consumer therefore receive the output of the general compiler, rather than a
separately authored replacement proof.

The two universe assumptions have distinct roles.  The lower assumption
constructs the least-universe map used as one of the two fused operations.  A
separate assumption one universe higher proves that the resulting proof value
is small in the ambient tower.  Literal agreement with the HOTG set carrier
cannot be stated at the same universe level.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLLeibnizNativeQualifiedHOTGIntegration

open Presentation Mettapedia.Logic
open HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section codedCwf)
open ZFSetUniformListTraceTypeInterpretation
open ZFSetContextualIdentity

namespace CompilerAgreement

/-- On every source tree accepted by the constructive compiler, the recursive
extensional compiler is a literal extension: it emits the same native term in
every object and hypothesis environment. -/
theorem constructive_compile_eq
    {gamma : HOLLeibnizNativeProofTranslation.SourceContext}
    {delta : List (HOLLeibnizNativeProofTranslation.Formula gamma)}
    {phi : HOLLeibnizNativeProofTranslation.Formula gamma}
    (source : HOL.ProofSyntax Symbol delta phi)
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n)
    (sourceSupported : HOLLeibnizNativeProofCoverage.supported source = true) :
    HOLLeibnizNativeRecursiveExtensionalCompiler.compile source objects hypotheses =
      HOLLeibnizNativeProofTranslation.compile source objects hypotheses := by
  induction source generalizing n <;>
    simp [HOLLeibnizNativeProofCoverage.supported,
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile,
      HOLLeibnizNativeProofTranslation.compile] at sourceSupported ⊢ <;>
    simp_all

/-- The retained object-HOL induction proof lies in the constructive source
fragment.  This is derived from the exact earlier compiler result rather than
from a second Boolean reduction of the large proof tree. -/
theorem retained_map_fusion_supported :
    HOLLeibnizNativeProofCoverage.supported
      (HOL.UniformListMapFusion.mapFusionProof (Γ := [])) = true :=
  (HOLLeibnizNativeProofCoverage.compile_some_iff_supported
    (HOL.UniformListMapFusion.mapFusionProof (Γ := []))
    (n := 5) Fin.elim0 (fun index => .var index)).mp
      ⟨NativeHOLCompiledMapFusionTrace.openNativeProof,
        NativeHOLCompiledMapFusionTrace.compiler_emits_openNativeProof⟩

/-- The exact open native term already interpreted by the map-fusion model is
also the output of the general recursive extensional compiler. -/
theorem recursive_compiler_emits_openNativeProof :
    HOLLeibnizNativeRecursiveExtensionalCompiler.compile
        (HOL.UniformListMapFusion.mapFusionProof (Γ := []))
        Fin.elim0 (fun index => .var index) =
      some NativeHOLCompiledMapFusionTrace.openNativeProof := by
  rw [constructive_compile_eq
    (HOL.UniformListMapFusion.mapFusionProof (Γ := []))
    Fin.elim0 (fun index => .var index) retained_map_fusion_supported]
  exact NativeHOLCompiledMapFusionTrace.compiler_emits_openNativeProof

/-- Assumption abstraction retains the same induction proof body, and the
recursive compiler emits exactly the existing closed native proof. -/
theorem closed_map_fusion_supported :
    HOLLeibnizNativeProofCoverage.supported
      HOLLeibnizMapFusionNative.closedProof = true :=
  (HOLLeibnizNativeProofCoverage.compile_some_iff_supported
    HOLLeibnizMapFusionNative.closedProof Fin.elim0 Fin.elim0).mp
      ⟨HOLLeibnizMapFusionNative.nativeProof,
        HOLLeibnizMapFusionNative.compiler_emits_nativeProof⟩

theorem recursive_compiler_emits_closed_map_fusion :
    HOLLeibnizNativeRecursiveExtensionalCompiler.compile
        HOLLeibnizMapFusionNative.closedProof Fin.elim0 Fin.elim0 =
      some HOLLeibnizMapFusionNative.nativeProof := by
  rw [constructive_compile_eq HOLLeibnizMapFusionNative.closedProof
    Fin.elim0 Fin.elim0 closed_map_fusion_supported]
  exact HOLLeibnizMapFusionNative.compiler_emits_nativeProof

theorem closed_map_fusion_recursively_supported :
    HOLLeibnizNativeQualifiedIntegration.Compiler.supported
      HOLLeibnizMapFusionNative.closedProof = true :=
  (HOLLeibnizNativeQualifiedIntegration.Compiler.compile_some_iff_supported
    HOLLeibnizMapFusionNative.closedProof Fin.elim0 Fin.elim0).mp
      ⟨HOLLeibnizMapFusionNative.nativeProof,
        recursive_compiler_emits_closed_map_fusion⟩

end CompilerAgreement

namespace ConnectedMapFusion

open NativeHOLTraceRecursiveExtensionalCompilerSemantics

universe u

/-- A nontrivial closed instance of the connected theorem.  Its source is the
five-times-abstracted retained induction proof, and the shared compiler output
is simultaneously a formation-sensitive dependent proof and a qualified
trace section. -/
theorem closed_typing_and_trace (a : ZFSet.{u}) :
    ∃ native code,
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile
          HOLLeibnizMapFusionNative.closedProof Fin.elim0 Fin.elim0 =
        some native ∧
      HOLLeibnizNativeQualifiedIntegration.Compiler.represent
          HOLLeibnizMapFusionNative.closedClaim = some code ∧
      Presentation.FormationSensitive.Judgment
          FormationSensitiveHOLExtensionalProfile.rules .nil native
          (FormationSensitiveHOLProofFamily.proof code) ∧
      ProofDenotes a NativeHOLTraceDisplayedTerms.Controls.emptyContext native
        (formulaMeaning HOLLeibnizMapFusionNative.closedClaim
          NativeHOLTraceDisplayedTerms.Controls.emptyContext
          (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation
            (a := a))) :=
  HOLLeibnizNativeQualifiedIntegration.Connected.compile_closed_preserves_typing_and_trace
      HOLLeibnizMapFusionNative.closedProof
      CompilerAgreement.closed_map_fusion_recursively_supported

/-- The open recursive compiler output receives the qualified trace meaning
needed for further proof composition. -/
theorem open_qualified_denotation (a : ZFSet.{u}) :
    ProofDenotes a
      (NativeHOLCompiledMapFusionTrace.proofContext a (theory (Γ := [])))
      NativeHOLCompiledMapFusionTrace.openNativeProof
      (formulaMeaning (HOL.UniformListMapFusion.mapFusion (Γ := []))
        (NativeHOLCompiledMapFusionTrace.proofContext a (theory (Γ := [])))
        (fun _ =>
          (ZFSetUniformListTraceTermInterpretation.emptyValuation :
            ZFSetUniformListTraceTermInterpretation.Valuation a []))) :=
  compile_denotes (HOL.UniformListMapFusion.mapFusionProof (Γ := []))
    (NativeHOLCompiledMapFusionTrace.emptyObjectsDenote a
      (NativeHOLCompiledMapFusionTrace.proofContext a (theory (Γ := []))))
    (HypothesesDenote.ofConstructive
      (NativeHOLCompiledMapFusionTrace.proofContext_hypotheses a
        (theory (Γ := []))))
    CompilerAgreement.recursive_compiler_emits_openNativeProof

/-- Wrong-target control: the same open compiler term cannot denote the
constantly false proposition, because the actual theory environment would
then supply an element of the empty truth code. -/
theorem open_proof_does_not_denote_false (a : ZFSet.{u}) :
    ¬ ProofDenotes a
      (NativeHOLCompiledMapFusionTrace.proofContext a (theory (Γ := [])))
      NativeHOLCompiledMapFusionTrace.openNativeProof (fun _ => False) := by
  intro falseMeaning
  obtain ⟨proofSection, _⟩ := falseMeaning
  exact ((ZFSetTraceProofDecoding.mem_truthCode False
    (proofSection (NativeHOLCompiledMapFusionTrace.theoryEnvironment a)).1).mp
      (proofSection (NativeHOLCompiledMapFusionTrace.theoryEnvironment a)).2).2

/-- The canonical proof section extracted from the recursive compiler's
qualified denotation. -/
noncomputable def recursiveOpenNativeProofSection (a : ZFSet.{u}) :
    Section (ZFSetTraceProofDecoding.truthFamily
      (formulaMeaning (HOL.UniformListMapFusion.mapFusion (Γ := []))
        (NativeHOLCompiledMapFusionTrace.proofContext a (theory (Γ := [])))
        (fun _ =>
          (ZFSetUniformListTraceTermInterpretation.emptyValuation :
            ZFSetUniformListTraceTermInterpretation.Valuation a [])))) :=
  Classical.choose (open_qualified_denotation a)

theorem recursiveOpenNativeProofSection_denoted (a : ZFSet.{u}) :
    NativeHOLTraceQualifiedExtensionalSemantics.Denotes a
      (NativeHOLCompiledMapFusionTrace.proofContext a (theory (Γ := [])))
      NativeHOLCompiledMapFusionTrace.openNativeProof
      (ZFSetTraceProofDecoding.truthFamily
        (formulaMeaning (HOL.UniformListMapFusion.mapFusion (Γ := []))
          (NativeHOLCompiledMapFusionTrace.proofContext a (theory (Γ := [])))
          (fun _ =>
            (ZFSetUniformListTraceTermInterpretation.emptyValuation :
              ZFSetUniformListTraceTermInterpretation.Valuation a []))))
      (recursiveOpenNativeProofSection a) :=
  Classical.choose_spec (open_qualified_denotation a)

/-- Proof irrelevance identifies the recursively obtained section with the
previous constructive section.  This is a comparison of the actual retained
values, not merely a statement that both propositions are inhabited. -/
theorem recursiveOpenNativeProofSection_eq_constructive (a : ZFSet.{u}) :
    recursiveOpenNativeProofSection a =
      NativeHOLCompiledMapFusionTrace.openNativeProofSection a :=
  NativeHOLTraceLeibnizProofSemantics.proofSection_unique _ _

/-- Supplying the five actual list-theory witnesses evaluates the recursive
compiler section to the universal map-fusion proof value. -/
noncomputable def recursiveCompiledMapFusionRoot (a : ZFSet.{u}) :
    Elements (ZFSetUniformListTraceProofBridge.truthFibre
      (HOL.UniformListMapFusion.mapFusion (Γ := []))
      (ZFSetUniformListTraceTermInterpretation.emptyValuation :
        ZFSetUniformListTraceTermInterpretation.Valuation a [])) :=
  recursiveOpenNativeProofSection a
    (NativeHOLCompiledMapFusionTrace.theoryEnvironment a)

theorem recursiveCompiledMapFusionRoot_eq_constructive (a : ZFSet.{u}) :
    recursiveCompiledMapFusionRoot a =
      NativeHOLCompiledMapFusionTrace.compiledMapFusionRoot a := by
  unfold recursiveCompiledMapFusionRoot
    NativeHOLCompiledMapFusionTrace.compiledMapFusionRoot
  rw [recursiveOpenNativeProofSection_eq_constructive]

/-- Three universal eliminations instantiate the retained recursive proof in
the source binder order. -/
noncomputable def recursiveCompiledFusionProofValue {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    Elements (ZFSetUniformListTraceProofBridge.truthFibre
      ZFSetUniformListTraceProofBridge.fusionBody
      (ZFSetUniformListTraceProofBridge.fusionValuation f g xs)) := by
  let root := recursiveCompiledMapFusionRoot a
  let atFunction := ZFSetUniformListTraceProofBridge.universalValueApp
    ZFSetUniformListTraceTermInterpretation.emptyValuation root f
  let atSecond := ZFSetUniformListTraceProofBridge.universalValueApp
    (ZFSetUniformListTraceTermInterpretation.extend
      ZFSetUniformListTraceTermInterpretation.emptyValuation f) atFunction g
  let atSequence := ZFSetUniformListTraceProofBridge.universalValueApp
    (ZFSetUniformListTraceTermInterpretation.extend
      (ZFSetUniformListTraceTermInterpretation.extend
        ZFSetUniformListTraceTermInterpretation.emptyValuation f) g)
    atSecond xs
  exact atSequence

theorem recursiveCompiledFusionProofValue_eq_constructive {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    recursiveCompiledFusionProofValue f g xs =
      NativeHOLCompiledMapFusionTrace.compiledFusionProofValue f g xs := by
  unfold recursiveCompiledFusionProofValue
    NativeHOLCompiledMapFusionTrace.compiledFusionProofValue
  rw [recursiveCompiledMapFusionRoot_eq_constructive]

end ConnectedMapFusion

namespace DependentConsumption

open ConnectedMapFusion

universe u

/-- The qualified recursive proof value becomes an inhabitant of the
contextual identity family for the two map-fusion endpoints. -/
noncomputable def recursiveFusionIdentityWitness {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    Elements (identityFamily
      (ZFSetUniformListTraceProofBridge.sequenceFamily a)
      (ZFSetUniformListTraceProofBridge.beforeSection f g xs)
      (ZFSetUniformListTraceProofBridge.afterSection f g xs) PUnit.unit) :=
  ⟨(recursiveCompiledFusionProofValue f g xs).1,
    ZFSetUniformListTraceProofBridge.fusion_fibre_identity f g xs ▸
      (recursiveCompiledFusionProofValue f g xs).2⟩

noncomputable def recursiveFusionIdentityPoint {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    formation.identityContext
      (ZFSetUniformListTraceProofBridge.sequenceFamily a) :=
  ⟨⟨⟨PUnit.unit,
      ZFSetUniformListTraceProofBridge.beforeSection f g xs PUnit.unit⟩,
      ZFSetUniformListTraceProofBridge.afterSection f g xs PUnit.unit⟩,
    recursiveFusionIdentityWitness f g xs⟩

/-- Full dependent identity elimination consumes the witness obtained from
the recursive compiler. -/
noncomputable def consumeRecursiveFusionEquality {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence)
    (motive : SetFamily
      (formation.identityContext
        (ZFSetUniformListTraceProofBridge.sequenceFamily a)))
    (base : Section (codedCwf.tySub motive
      (elimination.reflexivitySubstitution
        (ZFSetUniformListTraceProofBridge.sequenceFamily a)))) :
    Elements (motive (recursiveFusionIdentityPoint f g xs)) :=
  elimination.j motive base (recursiveFusionIdentityPoint f g xs)

noncomputable def recursiveConsumedEndpoint {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    Elements (ZFSetUniformListTraceProofBridge.endpointMotive
      (recursiveFusionIdentityPoint f g xs)) :=
  consumeRecursiveFusionEquality f g xs
    ZFSetUniformListTraceProofBridge.endpointMotive
    ZFSetUniformListTraceProofBridge.endpointBase

theorem recursiveConsumedEndpoint_value {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    (recursiveConsumedEndpoint f g xs).1 =
      (recursiveFusionIdentityPoint f g xs).1.1.2.1 :=
  ZFSetUniformListTraceProofBridge.endpointMotive_value
    (recursiveConsumedEndpoint f g xs)

end DependentConsumption

namespace HOTG

open ConnectedMapFusion DependentConsumption
open ZFSetUniverseClosure ZFSetInterpretation
open ZFSetUniverseLift ZFSetLiftedUniverseClosure
open ZFSetHenkinInterpretation ZFSetUniverseInterpretation
open ZFSetHOLTraceTypeInterpretation ZFSetHOLTraceTermInterpretation

universe u

/-- The exact source theory used by the retained proof: one induction
principle and four computation equations. -/
theorem source_theory_shape :
    theory (Γ := []) =
      [inductionPrinciple, mapNil, mapCons, lengthNil, lengthCons] := rfl

/-- The trace list model discharges every one of those source assumptions. -/
theorem source_theory_valid (a : ZFSet.{u})
    (formula : HOL.Formula HOL.UniformListInduction.Symbol [])
    (member : formula ∈ HOL.UniformListInduction.theory) :
    NativeHOLCompiledMapFusionTrace.closedFormulaMeaning a formula :=
  NativeHOLCompiledMapFusionTrace.uniformTheory_valid a formula member

/-- The two concrete operations are the actual HOTG least-universe and
powerset maps, with their decoded set-theoretic behavior stated together. -/
theorem actual_operation_decoding (lower : CofinalInaccessibles.{u})
    (x : Value carrierCode.{u} element) :
    carrierEquiv
        (ZFSetUniformListTraceTypeInterpretation.app
          (NativeHOLCompiledMapFusionHOTG.universeMap lower) x) =
          univOf lower
            (carrierEquiv x) ∧
    carrierEquiv
        (ZFSetUniformListTraceTypeInterpretation.app
          NativeHOLCompiledMapFusionHOTG.powerMap x) =
          ZFSet.powerset (carrierEquiv x) :=
  ⟨NativeHOLCompiledMapFusionHOTG.decode_universeMap lower x,
    NativeHOLCompiledMapFusionHOTG.decode_powerMap x⟩

/-- The recursively compiled proof specialized to the actual HOTG
least-universe and powerset operations. -/
noncomputable def hotgFusionProofValue (lower : CofinalInaccessibles.{u})
    (xs : Value carrierCode.{u} sequence) :=
  recursiveCompiledFusionProofValue
    (NativeHOLCompiledMapFusionHOTG.universeMap lower)
    NativeHOLCompiledMapFusionHOTG.powerMap xs

/-- This new route is literally the previously verified HOTG proof value,
because the recursive compiler retained the constructive output. -/
theorem hotgFusionProofValue_eq_existing
    (lower : CofinalInaccessibles.{u})
    (xs : Value carrierCode.{u} sequence) :
    hotgFusionProofValue lower xs =
      NativeHOLCompiledMapFusionHOTG.hotgFusionProofValue lower xs :=
  recursiveCompiledFusionProofValue_eq_constructive
    (NativeHOLCompiledMapFusionHOTG.universeMap lower)
    NativeHOLCompiledMapFusionHOTG.powerMap xs

/-- A dependent consumer receives that HOTG-specialized recursive witness. -/
noncomputable def hotgConsumedEndpoint (lower : CofinalInaccessibles.{u})
    (xs : Value carrierCode.{u} sequence) :=
  recursiveConsumedEndpoint
    (NativeHOLCompiledMapFusionHOTG.universeMap lower)
    NativeHOLCompiledMapFusionHOTG.powerMap xs

theorem hotgConsumedEndpoint_value (lower : CofinalInaccessibles.{u})
    (xs : Value carrierCode.{u} sequence) :
    (hotgConsumedEndpoint lower xs).1 =
      (recursiveFusionIdentityPoint
        (NativeHOLCompiledMapFusionHOTG.universeMap lower)
        NativeHOLCompiledMapFusionHOTG.powerMap xs).1.1.2.1 :=
  recursiveConsumedEndpoint_value
    (NativeHOLCompiledMapFusionHOTG.universeMap lower)
    NativeHOLCompiledMapFusionHOTG.powerMap xs

/-- The upper assumption is separate: it places the lower model's concrete
proof value inside the bottom level of the larger ambient tower. -/
theorem hotgFusionProofValue_small
    (lower : CofinalInaccessibles.{u})
    (upper : CofinalInaccessibles.{u + 1})
    (xs : Value carrierCode.{u} sequence) :
    (hotgFusionProofValue lower xs).1 ∈
      universeSet upper
        (ZFSetIndexedClosure.seed carrierCode.{u}) 0 := by
  rw [hotgFusionProofValue_eq_existing]
  exact NativeHOLCompiledMapFusionHOTG.hotgFusionProofValue_small
    lower upper xs

/-- Elementary finite closure is strictly weaker than the universe
assumption needed to internalize the whole list type. -/
theorem finite_closure_is_insufficient :
    ∃ U a : ZFSet.{u}, Closed U ∧ a ∈ U ∧
      ZFSetList.listCode a ⊆ U ∧ ZFSetList.listCode a ∉ U :=
  NativeHOLCompiledMapFusionUniverse.finiteClosure_does_not_supply_list_smallness

/-- Literal agreement with the entire ambient set carrier cannot be moved to
the same universe level. -/
theorem same_level_literal_code_is_impossible :
    ¬ ∃ code : ZFSet.{u}, Nonempty (Elements code ≃ ZFSet.{u}) :=
  NativeHOLCompiledMapFusionHOTG.no_same_level_full_set_code

end HOTG

#print axioms CompilerAgreement.constructive_compile_eq
#print axioms CompilerAgreement.retained_map_fusion_supported
#print axioms CompilerAgreement.recursive_compiler_emits_openNativeProof
#print axioms CompilerAgreement.closed_map_fusion_recursively_supported
#print axioms ConnectedMapFusion.closed_typing_and_trace
#print axioms ConnectedMapFusion.open_qualified_denotation
#print axioms ConnectedMapFusion.open_proof_does_not_denote_false
#print axioms ConnectedMapFusion.recursiveOpenNativeProofSection_denoted
#print axioms ConnectedMapFusion.recursiveOpenNativeProofSection_eq_constructive
#print axioms ConnectedMapFusion.recursiveCompiledFusionProofValue_eq_constructive
#print axioms DependentConsumption.recursiveConsumedEndpoint_value
#print axioms HOTG.source_theory_shape
#print axioms HOTG.source_theory_valid
#print axioms HOTG.actual_operation_decoding
#print axioms HOTG.hotgFusionProofValue_eq_existing
#print axioms HOTG.hotgConsumedEndpoint_value
#print axioms HOTG.hotgFusionProofValue_small
#print axioms HOTG.finite_closure_is_insufficient
#print axioms HOTG.same_level_literal_code_is_impossible

end HOLLeibnizNativeQualifiedHOTGIntegration
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
