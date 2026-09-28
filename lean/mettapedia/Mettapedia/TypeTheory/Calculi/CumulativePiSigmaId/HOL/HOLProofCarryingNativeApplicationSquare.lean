import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLProofCarryingPairTraceSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceContextualApplicationAgreement
import Mettapedia.Logic.HOL.ProofCarryingIdentityOperation

/-!
# Native application inside a retained-proof HOL program

One source proof-carrying operation applies an object function and constructs
the next proof. The generic proof compiler already retains that proof in a
dependent pair. This module shows that the first field of the same compiled
pair is the actual native dependent application of the represented operation
and current value, with no independent object interpretation selected for
that application.

The source proof and semantic section remain explicit. This is not an NIK
admission theorem or a CeTTa runtime correspondence claim.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLProofCarryingNativeApplicationSquare

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.FormationSensitive Mettapedia.Logic HOL.UniformListInduction
open HOLNativeGenericProofCompiler HOLImpredicativeProofCompilation
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (Section)
open ZFSetUniformListTraceTermInterpretation (interpret)
open ZFSetUniformListTraceTypeInterpretation (app)
open NativeHOLTraceQualifiedExtensionalSemantics (Denotes)

universe u

variable {a : ZFSet.{u}} {Γ : HOL.Ctx BaseSort}
  {Δ : List (HOL.Formula Symbol Γ)} {σ : HOL.Ty BaseSort}
  {n : Nat} {objects : Sub Tower.Head Γ.length n}

/-- The translated source operation step is literally native application,
and its value is derived through the native dependent application rule. -/
theorem operation_term_native
    {predicate : HOL.Term Symbol Γ (.arr σ .prop)}
    (operation : HOL.ProofCarryingPipeline.Operation predicate Δ)
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    (state : UniformListSemantics.State a objects) :
    NativeHOLTraceMixedTermSemantics.Denotes a state.context
      (Presentation.subst objects
        (HOLImpredicativeRepresentation.translate
          FormationSensitiveHOLLeibnizInterface.signature
          (operation.apply value).term))
      (NativeHOLTraceDisplayedTerms.typeFamily a state.context σ)
      (fun environment => interpret (operation.apply value).term
        (state.valuation environment)) := by
  have functionMeaning := HOLProofCarryingPairTraceSemantics.translate_denotes
    operation.term state
  have argumentMeaning := HOLProofCarryingPairTraceSemantics.translate_denotes
    value.term state
  have native := NativeHOLTraceContextualApplicationAgreement.object_application_is_native
    functionMeaning argumentMeaning
  simpa only [HOL.ProofCarryingPipeline.Operation.apply,
    HOLImpredicativeRepresentation.translate_app, Presentation.subst,
    ZFSetUniformListTraceTermInterpretation.interpret] using native

/-- One retained-proof source step forms a dependent native pair; its first
projection reduces to the same native application independently justified by
the dependent application rule. The second field remains the compiled source
proof's section, not a reconstructed certificate. -/
theorem operation_pack_native_square
    {predicate : HOL.Term Symbol Γ (.arr σ .prop)}
    (operation : HOL.ProofCarryingPipeline.Operation predicate Δ)
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    (state : UniformListSemantics.State a objects)
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length →
      Tower.Tm n}
    (hypothesesMeaning : GenericSemantics.Hypotheses
      (UniformListSemantics.algebra a) state hypotheses) :
    let next := operation.apply value
    let packed := HOLProofCarryingPairs.pack
      FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations uniformList_total next objects hypotheses
    let result := Presentation.subst objects
      (HOLImpredicativeRepresentation.translate
        FormationSensitiveHOLLeibnizInterface.signature next.term)
    Step UniformList.operations.target.headEq (.fst packed) result
        UniformList.operations.target.computation ∧
      ∃ evidence : Section (fun environment =>
          HOLProofCarryingPairTraceSemantics.invariantFamily state predicate
            ⟨environment, interpret next.term (state.valuation environment)⟩),
        Denotes a state.context packed
          (ZFSetContextualInterpretation.sigmaFamily
            (NativeHOLTraceDisplayedTerms.typeFamily a state.context σ)
            (HOLProofCarryingPairTraceSemantics.invariantFamily state predicate))
          (ZFSetContextualInterpretation.pair
            (fun environment => interpret next.term (state.valuation environment))
            evidence) ∧
        NativeHOLTraceMixedTermSemantics.Denotes a state.context result
          (NativeHOLTraceDisplayedTerms.typeFamily a state.context σ)
          (fun environment => interpret next.term (state.valuation environment)) := by
  have reduced :=
    (HOLProofCarryingPairTraceSemantics.pack_first_square
      (operation.apply value) state hypothesesMeaning).1
  obtain ⟨evidence, packedMeaning⟩ :=
    HOLProofCarryingPairTraceSemantics.pack_denotes
      (operation.apply value) state hypothesesMeaning
  exact ⟨reduced, evidence, packedMeaning,
    operation_term_native operation value state⟩

namespace Controls

open HOLProofCarryingPairs.Controls (zeroPredicate certifiedZero)

def identityZero : HOL.ProofCarryingPipeline.Operation zeroPredicate [] :=
  Mettapedia.Logic.HOL.ProofCarryingIdentityOperation.identityOperation zeroPredicate

/-- The source program's identity step really returns the encoded zero; this
is value computation, separately from its retained closure proof. -/
theorem identity_zero_trace_value (a : ZFSet.{u})
    (environment : (UniformListSemantics.Controls.assumptionState a []).context.Environment) :
    interpret (identityZero.apply certifiedZero).term
      ((UniformListSemantics.Controls.assumptionState a []).valuation environment) =
      ZFSetUniformListTraceTypeInterpretation.constant a Symbol.zero := by
  change ZFSetUniformListTraceTypeInterpretation.app
    (ZFSetUniformListTraceTypeInterpretation.lam
      (fun x : ZFSetUniformListTraceTypeInterpretation.Value a count => x))
    (ZFSetUniformListTraceTypeInterpretation.constant a Symbol.zero) = _
  exact ZFSetUniformListTraceTypeInterpretation.app_lam _ _

/-- The closed certified-zero program takes a real, proof-producing source
identity step. The compiled dependent pair retains that proof, its first
projection reduces to the compiled result, and that result is native
application with the encoded-zero trace value. -/
theorem certified_zero_identity_step (a : ZFSet.{u}) :
    let state := UniformListSemantics.Controls.assumptionState a []
    let next := identityZero.apply certifiedZero
    let packed := HOLProofCarryingPairs.pack
      FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations uniformList_total next Fin.elim0 Fin.elim0
    let result := HOLImpredicativeRepresentation.translate
      FormationSensitiveHOLLeibnizInterface.signature next.term
    Step UniformList.operations.target.headEq (.fst packed) result
        UniformList.operations.target.computation ∧
      ∃ evidence : Section (fun environment =>
          HOLProofCarryingPairTraceSemantics.invariantFamily state zeroPredicate
            ⟨environment, interpret next.term (state.valuation environment)⟩),
        Denotes a state.context packed
          (ZFSetContextualInterpretation.sigmaFamily
            (NativeHOLTraceDisplayedTerms.typeFamily a state.context count)
            (HOLProofCarryingPairTraceSemantics.invariantFamily state zeroPredicate))
          (ZFSetContextualInterpretation.pair
            (fun environment => interpret next.term (state.valuation environment))
            evidence) ∧
        NativeHOLTraceMixedTermSemantics.Denotes a state.context result
          (NativeHOLTraceDisplayedTerms.typeFamily a state.context count)
          (fun _ => ZFSetUniformListTraceTypeInterpretation.constant a Symbol.zero) := by
  let state := UniformListSemantics.Controls.assumptionState a []
  have square := operation_pack_native_square identityZero certifiedZero state
    (hypotheses := (Fin.elim0 : Fin 0 → Tower.Tm 0))
    (fun index => Fin.elim0 index)
  obtain ⟨reduced, evidence, packedMeaning, nativeMeaning⟩ := square
  refine ⟨reduced, evidence, packedMeaning, ?_⟩
  apply nativeMeaning.change_value
  funext environment
  exact identity_zero_trace_value a environment

/-- A dependent native program subsequently consumes the proof-bearing pair
constructed by the identity step. Its result type mentions that same pair
twice, so replacing it by an unrelated accepted Boolean would not typecheck. -/
theorem certified_zero_identity_consumer_typed :
    let next := identityZero.apply certifiedZero
    let packed := HOLProofCarryingPairs.pack
      FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations uniformList_total next Fin.elim0 Fin.elim0
    Typing UniformList.operations.target .nil
      (inst0 packed (.refl (.var 0)))
      (.id (HOLProofCarryingPairs.pairType
          FormationSensitiveHOLLeibnizInterface.signature
          UniformList.proofName zeroPredicate Fin.elim0)
        packed packed) := by
  have pairTyped :
      Typing UniformList.operations.target .nil
        (HOLProofCarryingPairs.pack
          FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
          UniformList.operations uniformList_total
          (identityZero.apply certifiedZero) Fin.elim0 Fin.elim0)
        (HOLProofCarryingPairs.pairType
          FormationSensitiveHOLLeibnizInterface.signature
          UniformList.proofName zeroPredicate Fin.elim0) :=
    HOLProofCarryingPairs.pack_typed
    FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
    UniformList.operations uniformList_total
    (identityZero.apply certifiedZero)
    (fun index => Fin.elim0 index) (fun index => Fin.elim0 index)
  simpa only [inst0, subst, subst0, Fin.cases_zero] using
    Typing.reflIntro pairTyped

end Controls

#print axioms operation_term_native
#print axioms operation_pack_native_square
#print axioms Controls.identityZero
#print axioms Controls.identity_zero_trace_value
#print axioms Controls.certified_zero_identity_step
#print axioms Controls.certified_zero_identity_consumer_typed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLProofCarryingNativeApplicationSquare
