import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceLeibnizCompilerSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizMapFusionNative
import Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceProofBridge

/-!
# The compiled map-fusion proof consumed by dependent identity

The exact output of the Leibniz proof compiler is interpreted in a semantic
telescope containing the five ordered assumptions of the uniform-list theory.
After supplying the model's witnesses for those assumptions, the resulting
retained trace proof is instantiated at two functions and one list.  Its final
equality fibre is then consumed by contextual identity elimination.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLCompiledMapFusionTrace

open Presentation Mettapedia.Logic HOL.UniformListInduction
open HOL.UniformListMapFusion
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section codedCwf)
open ZFSetUniformListTraceTypeInterpretation
open ZFSetUniformListTraceTermInterpretation
open ZFSetContextualIdentity
open NativeTraceLambdaSemantics
open NativeHOLTraceLeibnizProofSemantics
open NativeHOLTraceLeibnizCompilerSemantics

universe u

def closedFormulaMeaning (a : ZFSet.{u}) (formula : HOL.Formula Symbol []) : Prop :=
  ZFSetHOLTypeInterpretation.holds
    (ZFSetUniformListTraceTermInterpretation.interpret formula
      (ZFSetUniformListTraceTermInterpretation.emptyValuation :
        ZFSetUniformListTraceTermInterpretation.Valuation a []))

/-- A semantic telescope whose de Bruijn variables are the ordered source
proof assumptions. -/
noncomputable def proofContext (a : ZFSet.{u}) :
    (delta : List (HOL.Formula Symbol [])) → Context.{u} delta.length
  | [] => Context.nil
  | formula :: tail =>
      let prior := proofContext a tail
      prior.snoc (fun _ =>
        ZFSetTraceProofDecoding.truthCode (closedFormulaMeaning a formula))

theorem proofContext_family (a : ZFSet.{u})
    (delta : List (HOL.Formula Symbol [])) (index : Fin delta.length)
    (environment : (proofContext a delta).Environment) :
    (proofContext a delta).family index environment =
      ZFSetTraceProofDecoding.truthCode
        (closedFormulaMeaning a (delta.get index)) := by
  induction delta with
  | nil => exact Fin.elim0 index
  | cons formula tail inductionHypothesis =>
      refine Fin.cases ?_ (fun prior => ?_) index
      · rfl
      · exact inductionHypothesis prior environment.1

theorem proofContext_hypotheses (a : ZFSet.{u})
    (delta : List (HOL.Formula Symbol [])) :
    HypothesesDenote (a := a) (proofContext a delta)
      (fun _ => (ZFSetUniformListTraceTermInterpretation.emptyValuation :
        ZFSetUniformListTraceTermInterpretation.Valuation a []))
      (fun index => (.var index : Tower.Tm delta.length)) := by
  intro index
  let context := proofContext a delta
  have familyEquality : context.family index =
      ZFSetTraceProofDecoding.truthFamily
        (formulaMeaning (delta.get index) context
          (fun _ => (ZFSetUniformListTraceTermInterpretation.emptyValuation :
            ZFSetUniformListTraceTermInterpretation.Valuation a []))) := by
    funext environment
    exact proofContext_family a delta index environment
  have variableMeaning := NativeHOLTraceMixedTermSemantics.Denotes.variable
    (a := a) context index
  exact ⟨_, variableMeaning.cast_family familyEquality⟩

theorem emptyObjectsDenote (a : ZFSet.{u}) {n : Nat}
    (context : Context.{u} n) :
    ObjectsDenote (a := a) (gamma := []) context Fin.elim0
      (fun _ => (ZFSetUniformListTraceTermInterpretation.emptyValuation :
        ZFSetUniformListTraceTermInterpretation.Valuation a [])) := by
  intro type index
  exact nomatch index

/-- The exact compiler output before assumption abstraction. -/
def openNativeProof : Tower.Tm 5 :=
  (HOLLeibnizNativeProofTranslation.compile
    (HOL.UniformListMapFusion.mapFusionProof (Γ := []))
    (n := 5) Fin.elim0 (fun index => .var index)).get
      HOLLeibnizMapFusionNative.original_compiles

theorem compiler_emits_openNativeProof :
    HOLLeibnizNativeProofTranslation.compile
      (HOL.UniformListMapFusion.mapFusionProof (Γ := []))
      Fin.elim0 (fun index => .var index) = some openNativeProof :=
  (Option.some_get HOLLeibnizMapFusionNative.original_compiles).symm

/-- The actual open compiler output denotes the original map-fusion formula
under its exact five-entry source theory context. -/
theorem openNativeProof_denotes (a : ZFSet.{u}) :
    ProofDenotes a (proofContext a (theory (Γ := []))) openNativeProof
      (formulaMeaning (HOL.UniformListMapFusion.mapFusion (Γ := []))
        (proofContext a (theory (Γ := [])))
        (fun _ => (ZFSetUniformListTraceTermInterpretation.emptyValuation :
          ZFSetUniformListTraceTermInterpretation.Valuation a []))) :=
  compile_denotes (HOL.UniformListMapFusion.mapFusionProof (Γ := []))
    (emptyObjectsDenote a (proofContext a (theory (Γ := []))))
    (proofContext_hypotheses a (theory (Γ := [])))
    compiler_emits_openNativeProof

/-- An environment of actual trace witnesses for every source theory
assumption. -/
noncomputable def proofContextEnvironment (a : ZFSet.{u}) :
    (delta : List (HOL.Formula Symbol [])) →
      (∀ formula ∈ delta, closedFormulaMeaning a formula) →
        (proofContext a delta).Environment
  | [], _ => PUnit.unit
  | formula :: tail, valid =>
      let priorValid : ∀ entry ∈ tail, closedFormulaMeaning a entry :=
        fun entry member => valid entry (List.mem_cons_of_mem formula member)
      let prior := proofContextEnvironment a tail priorValid
      let witness : Elements
          (ZFSetTraceProofDecoding.truthCode (closedFormulaMeaning a formula)) :=
        ⟨∅, (ZFSetTraceProofDecoding.mem_truthCode _ ∅).mpr
          ⟨rfl, valid formula (by simp)⟩⟩
      ⟨prior, witness⟩

theorem uniformTheory_valid (a : ZFSet.{u})
    (formula : HOL.Formula Symbol []) (member : formula ∈ theory) :
    closedFormulaMeaning a formula := by
  unfold closedFormulaMeaning
  apply (ZFSetUniformListTraceProofBridge.formula_agreement formula
    (ZFSetUniformListTraceTermInterpretation.emptyValuation :
      ZFSetUniformListTraceTermInterpretation.Valuation a [])).mpr
  refine Eq.mp ?_ (ZFSetUniformListModel.theory_valid a formula member)
  unfold HOL.HenkinModel.models HOL.PreModel.models
  apply congrArg ULift.down
  apply congrArg (HOL.PreModel.denote (ZFSetUniformListModel.model a).toPreModel formula)
  funext type index
  exact nomatch index

noncomputable def theoryEnvironment (a : ZFSet.{u}) :
    (proofContext a (theory (Γ := []))).Environment :=
  proofContextEnvironment a theory (uniformTheory_valid a)

noncomputable def openNativeProofSection (a : ZFSet.{u}) :
    Section (ZFSetTraceProofDecoding.truthFamily
      (formulaMeaning (HOL.UniformListMapFusion.mapFusion (Γ := []))
        (proofContext a (theory (Γ := [])))
        (fun _ => (ZFSetUniformListTraceTermInterpretation.emptyValuation :
          ZFSetUniformListTraceTermInterpretation.Valuation a [])))) :=
  Classical.choose (openNativeProof_denotes a)

theorem openNativeProofSection_denoted (a : ZFSet.{u}) :
    NativeHOLTraceMixedTermSemantics.Denotes a
      (proofContext a (theory (Γ := []))) openNativeProof
      (ZFSetTraceProofDecoding.truthFamily
        (formulaMeaning (HOL.UniformListMapFusion.mapFusion (Γ := []))
          (proofContext a (theory (Γ := [])))
          (fun _ => (ZFSetUniformListTraceTermInterpretation.emptyValuation :
            ZFSetUniformListTraceTermInterpretation.Valuation a []))))
      (openNativeProofSection a) :=
  Classical.choose_spec (openNativeProof_denotes a)

/-- Evaluation of the retained section at the concrete assumption witnesses
produces the root proof value for universal map fusion. -/
noncomputable def compiledMapFusionRoot (a : ZFSet.{u}) :
    Elements (ZFSetUniformListTraceProofBridge.truthFibre
      (HOL.UniformListMapFusion.mapFusion (Γ := []))
      (ZFSetUniformListTraceTermInterpretation.emptyValuation :
        ZFSetUniformListTraceTermInterpretation.Valuation a [])) :=
  openNativeProofSection a (theoryEnvironment a)

/-- Three universal eliminations instantiate the compiled proof in source
binder order. -/
noncomputable def compiledFusionProofValue {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    Elements (ZFSetUniformListTraceProofBridge.truthFibre
      ZFSetUniformListTraceProofBridge.fusionBody
      (ZFSetUniformListTraceProofBridge.fusionValuation f g xs)) := by
  let root := compiledMapFusionRoot a
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

noncomputable def compiledFusionIdentityWitness {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    Elements (identityFamily (ZFSetUniformListTraceProofBridge.sequenceFamily a)
      (ZFSetUniformListTraceProofBridge.beforeSection f g xs)
      (ZFSetUniformListTraceProofBridge.afterSection f g xs) PUnit.unit) :=
  ⟨(compiledFusionProofValue f g xs).1,
    ZFSetUniformListTraceProofBridge.fusion_fibre_identity f g xs ▸
      (compiledFusionProofValue f g xs).2⟩

noncomputable def compiledFusionIdentityPoint {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    formation.identityContext (ZFSetUniformListTraceProofBridge.sequenceFamily a) :=
  ⟨⟨⟨PUnit.unit, ZFSetUniformListTraceProofBridge.beforeSection f g xs PUnit.unit⟩,
      ZFSetUniformListTraceProofBridge.afterSection f g xs PUnit.unit⟩,
    compiledFusionIdentityWitness f g xs⟩

/-- Full dependent identity elimination consumes the proof value obtained
from the actual compiler output. -/
noncomputable def consumeCompiledFusionEquality {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence)
    (motive : SetFamily
      (formation.identityContext (ZFSetUniformListTraceProofBridge.sequenceFamily a)))
    (base : Section (codedCwf.tySub motive
      (elimination.reflexivitySubstitution
        (ZFSetUniformListTraceProofBridge.sequenceFamily a)))) :
    Elements (motive (compiledFusionIdentityPoint f g xs)) :=
  elimination.j motive base (compiledFusionIdentityPoint f g xs)

noncomputable def compiledConsumedEndpoint {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    Elements (ZFSetUniformListTraceProofBridge.endpointMotive
      (compiledFusionIdentityPoint f g xs)) :=
  consumeCompiledFusionEquality f g xs
    ZFSetUniformListTraceProofBridge.endpointMotive
    ZFSetUniformListTraceProofBridge.endpointBase

theorem compiledConsumedEndpoint_value {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    (compiledConsumedEndpoint f g xs).1 =
      (compiledFusionIdentityPoint f g xs).1.1.2.1 :=
  ZFSetUniformListTraceProofBridge.endpointMotive_value
    (compiledConsumedEndpoint f g xs)

#print axioms proofContext_family
#print axioms proofContext_hypotheses
#print axioms compiler_emits_openNativeProof
#print axioms openNativeProof_denotes
#print axioms openNativeProofSection_denoted
#print axioms compiledMapFusionRoot
#print axioms compiledFusionProofValue
#print axioms consumeCompiledFusionEquality
#print axioms compiledConsumedEndpoint_value

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLCompiledMapFusionTrace
