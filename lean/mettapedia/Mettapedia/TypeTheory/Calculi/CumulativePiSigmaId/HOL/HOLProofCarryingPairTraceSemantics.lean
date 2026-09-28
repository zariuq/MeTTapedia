import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLProofCarryingPairs
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerUniformListSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceMixedSubstitution

/-!
# Set interpretation of compiled HOL proof-carrying pairs

The pair emitted by the total HOL compiler has the value of the original
source expression and a section of its predicate's truth family. Derived
connective expansion is interpreted by the existing trace/Henkin comparison;
the result is about the original source predicate, not only its expansion.

Both projections are the native operational rules and retain the same set
sections. The second projection's family is aligned by the first projection
law. This instantiates the existing uniform-List trace model, including its
qualified extensional proof rules; it is not a model of arbitrary signatures
or an adequacy theorem for an imported HOTG document.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLProofCarryingPairTraceSemantics

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Mettapedia.Logic HOL.UniformListInduction
open HOLNativeGenericProofCompiler HOLImpredicativeProofCompilation
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (SetFamily Section Extension)
open ZFSetUniformListTraceTypeInterpretation (Value)
open ZFSetUniformListTraceTermInterpretation (interpret interpret_expand)
open NativeHOLTraceQualifiedExtensionalSemantics (Denotes ProofDenotes)
open NativeHOLTraceDisplayedTerms (typeFamily)

universe u
variable {a : ZFSet.{u}} {Γ : HOL.Ctx BaseSort}
  {Δ : List (HOL.Formula Symbol Γ)} {σ : HOL.Ty BaseSort}
  {n : Nat} {objects : Sub Tower.Head Γ.length n}

/-- The semantic second field depends on the actual value in the first. -/
noncomputable def invariantFamily (state : UniformListSemantics.State a objects)
    (predicate : HOL.Term Symbol Γ (.arr σ .prop)) :
    SetFamily (Extension (typeFamily a state.context σ)) :=
  ZFSetTraceProofDecoding.truthFamily (fun point =>
    ZFSetHOLTypeInterpretation.holds
      (ZFSetUniformListTraceTypeInterpretation.app
        (interpret predicate (state.valuation point.1)) point.2))

/-- Total translation, including derived connectives, has the original
source's value in the existing displayed object relation. -/
theorem translate_denotes (term : HOL.Term Symbol Γ σ)
    (state : UniformListSemantics.State a objects) :
    NativeHOLTraceDisplayedTerms.Denotes a state.context
      (subst objects (HOLImpredicativeRepresentation.translate
        FormationSensitiveHOLLeibnizInterface.signature term))
      (fun environment => interpret term (state.valuation environment)) := by
  have meaning := NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
    (HOL.ImpredicativeConnectives.expand term)
    (HOLImpredicativeRepresentation.translate_eq
      FormationSensitiveHOLLeibnizInterface.signature term)
    state.context objects state.valuation state.objectsDenote
  simpa only [interpret_expand] using meaning

/-- The actual compiled source proof, not a new semantic witness selected
instead of it, denotes the truth family of the original conclusion. -/
theorem translateProof_denotes_original {φ : HOL.Formula Symbol Γ}
    (source : HOL.ProofSyntax Symbol Δ φ)
    (state : UniformListSemantics.State a objects)
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (hypothesesMeaning : GenericSemantics.Hypotheses
      (UniformListSemantics.algebra a) state hypotheses) :
    ProofDenotes a state.context
      (translateProof FormationSensitiveHOLLeibnizInterface.signature
        UniformList.proofName UniformList.operations uniformList_total source objects hypotheses)
      (fun environment => ZFSetHOLTypeInterpretation.holds
        (interpret φ (state.valuation environment))) := by
  have meaning := translateProof_denotes FormationSensitiveHOLLeibnizInterface.signature
    UniformList.proofName UniformList.operations uniformList_total
    (UniformListSemantics.algebra a) source state hypothesesMeaning
  change ProofDenotes a state.context _
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
      (HOL.ImpredicativeConnectives.expand φ) state.context state.valuation) at meaning
  apply meaning.cast_proposition
  funext environment
  change ZFSetHOLTypeInterpretation.holds
    (interpret (HOL.ImpredicativeConnectives.expand φ) (state.valuation environment)) = _
  rw [interpret_expand]

theorem pack_denotes {predicate : HOL.Term Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    (state : UniformListSemantics.State a objects)
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (hypothesesMeaning : GenericSemantics.Hypotheses
      (UniformListSemantics.algebra a) state hypotheses) :
    ∃ evidence : Section (fun environment => invariantFamily state predicate
        ⟨environment, interpret value.term (state.valuation environment)⟩),
      Denotes a state.context
        (HOLProofCarryingPairs.pack FormationSensitiveHOLLeibnizInterface.signature
          UniformList.proofName UniformList.operations uniformList_total value objects hypotheses)
        (ZFSetContextualInterpretation.sigmaFamily (typeFamily a state.context σ)
          (invariantFamily state predicate))
        (ZFSetContextualInterpretation.pair
          (fun environment => interpret value.term (state.valuation environment)) evidence) := by
  obtain ⟨evidence, proofMeaning⟩ := translateProof_denotes_original value.evidence state hypothesesMeaning
  exact ⟨evidence, Denotes.pair (codomain := invariantFamily state predicate)
    (.mixed (.object (translate_denotes value.term state))) proofMeaning⟩

/-- Extracting the first field commutes with the source interpretation. -/
theorem pack_first_square {predicate : HOL.Term Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    (state : UniformListSemantics.State a objects)
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (hypothesesMeaning : GenericSemantics.Hypotheses
      (UniformListSemantics.algebra a) state hypotheses) :
    let packed := HOLProofCarryingPairs.pack FormationSensitiveHOLLeibnizInterface.signature
      UniformList.proofName UniformList.operations uniformList_total value objects hypotheses
    let result := subst objects (HOLImpredicativeRepresentation.translate
      FormationSensitiveHOLLeibnizInterface.signature value.term)
    Step UniformList.operations.target.headEq (.fst packed) result
        UniformList.operations.target.computation ∧
      Denotes a state.context (.fst packed) (typeFamily a state.context σ)
        (fun environment => interpret value.term (state.valuation environment)) ∧
      Denotes a state.context result (typeFamily a state.context σ)
        (fun environment => interpret value.term (state.valuation environment)) := by
  obtain ⟨evidence, pairMeaning⟩ := pack_denotes value state hypothesesMeaning
  exact ⟨.betaSigmaFst _ _,
    (Denotes.first pairMeaning).change_value (ZFSetContextualInterpretation.fst_pair _ _),
    .mixed (.object (translate_denotes value.term state))⟩

/-- Extracting the second field retains the compiled proof's section. Its
family is transported along the proven first-projection equation. -/
theorem pack_second_square {predicate : HOL.Term Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    (state : UniformListSemantics.State a objects)
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (hypothesesMeaning : GenericSemantics.Hypotheses
      (UniformListSemantics.algebra a) state hypotheses) :
    let packed := HOLProofCarryingPairs.pack FormationSensitiveHOLLeibnizInterface.signature
      UniformList.proofName UniformList.operations uniformList_total value objects hypotheses
    let compiled := translateProof FormationSensitiveHOLLeibnizInterface.signature
      UniformList.proofName UniformList.operations uniformList_total value.evidence objects hypotheses
    let family := fun environment => invariantFamily state predicate
      ⟨environment, interpret value.term (state.valuation environment)⟩
    Step UniformList.operations.target.headEq (.snd packed) compiled
        UniformList.operations.target.computation ∧
      ∃ evidence : Section family,
        Denotes a state.context (.snd packed) family evidence ∧
        Denotes a state.context compiled family evidence := by
  obtain ⟨evidence, proofMeaning⟩ := translateProof_denotes_original value.evidence state hypothesesMeaning
  exact ⟨.betaSigmaSnd _ _, evidence,
    Denotes.second_pair (codomain := invariantFamily state predicate)
      (.mixed (.object (translate_denotes value.term state))) proofMeaning, proofMeaning⟩

/-- A finite retained-proof run agrees with left-to-right application of the
same trace-coded operations. -/
theorem interpret_run {predicate : HOL.Term Symbol Γ (.arr σ .prop)}
    (operations : List (HOL.ProofCarryingPipeline.Operation predicate Δ))
    (initial : HOL.ProofCarryingPipeline.Value predicate Δ)
    (valuation : ZFSetUniformListTraceTermInterpretation.Valuation a Γ) :
    interpret (HOL.ProofCarryingPipeline.run operations initial).term valuation =
      operations.foldl (fun value (operation : HOL.ProofCarryingPipeline.Operation predicate Δ) =>
        ZFSetUniformListTraceTypeInterpretation.app (interpret operation.term valuation) value)
        (interpret initial.term valuation) := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih => exact ih (operation.apply initial)

/-- Compiling and then projecting a whole proof-carrying run has the same
meaning as directly executing the source operations in the trace model. -/
theorem run_first_denotes {predicate : HOL.Term Symbol Γ (.arr σ .prop)}
    (operations : List (HOL.ProofCarryingPipeline.Operation predicate Δ))
    (initial : HOL.ProofCarryingPipeline.Value predicate Δ)
    (state : UniformListSemantics.State a objects)
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (hypothesesMeaning : GenericSemantics.Hypotheses
      (UniformListSemantics.algebra a) state hypotheses) :
    Denotes a state.context
      (.fst (HOLProofCarryingPairs.pack FormationSensitiveHOLLeibnizInterface.signature
        UniformList.proofName UniformList.operations uniformList_total
        (HOL.ProofCarryingPipeline.run operations initial) objects hypotheses))
      (typeFamily a state.context σ)
      (fun environment => operations.foldl
        (fun value (operation : HOL.ProofCarryingPipeline.Operation predicate Δ) =>
          ZFSetUniformListTraceTypeInterpretation.app
            (interpret operation.term (state.valuation environment)) value)
        (interpret initial.term (state.valuation environment))) := by
  have meaning := (pack_first_square (HOL.ProofCarryingPipeline.run operations initial)
    state hypothesesMeaning).2.1
  exact meaning.change_value (funext (fun environment => interpret_run operations initial
    (state.valuation environment)))

/-- The invariant of any set-coded certified pair follows by decoding its
second component. This does not run the source proof compiler again. -/
theorem decoded_invariant (state : UniformListSemantics.State a objects)
    (predicate : HOL.Term Symbol Γ (.arr σ .prop))
    (value : Section (ZFSetContextualInterpretation.sigmaFamily
      (typeFamily a state.context σ) (invariantFamily state predicate)))
    (environment : state.context.Environment) :
    ZFSetHOLTypeInterpretation.holds
      (ZFSetUniformListTraceTypeInterpretation.app
        (interpret predicate (state.valuation environment))
        (ZFSetContextualInterpretation.fst value environment)) :=
  ((ZFSetTraceProofDecoding.mem_truthCode _ _).mp
    (ZFSetContextualInterpretation.snd value environment).2).2

namespace Controls

open HOLProofCarryingPairs.Controls

theorem certified_zero_has_meaning (a : ZFSet.{u}) :
    ∃ evidence,
      Denotes a NativeTraceLambdaSemantics.Context.nil
        (HOLProofCarryingPairs.pack FormationSensitiveHOLLeibnizInterface.signature
          UniformList.proofName UniformList.operations uniformList_total certifiedZero
          Fin.elim0 Fin.elim0)
        (ZFSetContextualInterpretation.sigmaFamily
          (typeFamily a NativeTraceLambdaSemantics.Context.nil count)
          (invariantFamily (UniformListSemantics.Controls.assumptionState a []) zeroPredicate))
        (ZFSetContextualInterpretation.pair
          (fun _ => ZFSetUniformListTraceTypeInterpretation.constant a Symbol.zero) evidence) :=
  pack_denotes certifiedZero (UniformListSemantics.Controls.assumptionState a [])
    (fun index => Fin.elim0 index)

/-- Changing the certified first value from zero to its successor cannot
be hidden by retaining a proof of the old predicate. The target fibre has
no such pair, independently of how one might attempt to compile its proof. -/
theorem successor_cannot_carry_zero_certificate (a : ZFSet.{u}) :
    ¬ ∃ value : Section (ZFSetContextualInterpretation.sigmaFamily
        (typeFamily a NativeTraceLambdaSemantics.Context.nil count)
        (invariantFamily (UniformListSemantics.Controls.assumptionState a []) zeroPredicate)),
      ZFSetContextualInterpretation.fst value = fun _ =>
        ZFSetUniformListTraceTypeInterpretation.app
          (ZFSetUniformListTraceTypeInterpretation.constant a Symbol.succ)
          (ZFSetUniformListTraceTypeInterpretation.constant a Symbol.zero) := by
  rintro ⟨value, firstEqual⟩
  have invariant := decoded_invariant (UniformListSemantics.Controls.assumptionState a [])
    zeroPredicate value PUnit.unit
  have invariant := (congrArg (fun (first : Section
      (typeFamily a NativeTraceLambdaSemantics.Context.nil count)) =>
    ZFSetHOLTypeInterpretation.holds (ZFSetUniformListTraceTypeInterpretation.app
      (interpret zeroPredicate
        ((UniformListSemantics.Controls.assumptionState a []).valuation PUnit.unit))
      (first PUnit.unit))) firstEqual).mp invariant
  simp only [zeroPredicate, interpret, ZFSetUniformListTraceTypeInterpretation.constant,
    ZFSetUniformListTraceTypeInterpretation.app_lam,
    ZFSetUniformListTraceTermInterpretation.extend, ZFSetHOLTypeInterpretation.holds_truth,
    ZFSetUniformListModel.decode_encodeCount] at invariant
  have impossible := congrArg ZFSetUniformListModel.decodeCount invariant
  simp only [ZFSetUniformListModel.decode_encodeCount] at impossible
  cases impossible

end Controls

#print axioms translate_denotes
#print axioms translateProof_denotes_original
#print axioms pack_denotes
#print axioms pack_first_square
#print axioms pack_second_square
#print axioms interpret_run
#print axioms run_first_denotes
#print axioms decoded_invariant
#print axioms Controls.certified_zero_has_meaning
#print axioms Controls.successor_cannot_carry_zero_certificate

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLProofCarryingPairTraceSemantics
