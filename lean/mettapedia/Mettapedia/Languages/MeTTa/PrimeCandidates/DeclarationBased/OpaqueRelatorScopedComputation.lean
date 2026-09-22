import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.OpaqueRelatorExtension
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeRelatorCompatibility
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationContextViews

/-!
# The existing scoped handler in extended native List/J/relator environments

The operation handler and independently authored primitive world lists remain
unchanged. Their result contract is proved for arbitrary admitted arguments
under the combined native rules, including contexts and substitutions that
use newly declared terms. Consequently every computation admitted under those
same combined rules has admitted interpreted results.

Positive operation qualification does not require opacity: each marking call
returns its actual argument, and reflexivity returns native reflexivity at
that argument. Opacity is needed separately when using the old conversion
theory to reject a wrong dependent index. Neither statement establishes the
consistency of arbitrary added declarations or chooses an evaluation strategy.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedComputation

variable {Head Operation : Type} {n : Nat}

/-- Installing declarations preserves formation of an authored operation
signature; this is distinct from qualification of its runtime handler. -/
theorem OperationFormation.includeSignature {base : Rules Head}
    {operations : OperationSignature Head Operation} {operation : Operation}
    (formed : OperationFormation base operations operation)
    (declarations : Declaration.Signature Head) :
    OperationFormation (Declaration.extendRules base declarations) operations operation := by
  obtain ⟨⟨u, universeU, input⟩, ⟨v, universeV, output⟩⟩ := formed
  exact ⟨⟨u, universeU, input.includeSignature declarations⟩,
    ⟨v, universeV, output.includeSignature declarations⟩⟩

/-- The existing computation derivation is replayed through ordinary native
signature inclusion, including formation and conversion premises. -/
theorem Typing.includeSignature {base : Rules Head}
    {operations : OperationSignature Head Operation} {context : Ctx Head n}
    {code : Code Head Operation n} {type : Tm Head n}
    (typed : Typing base operations context code type)
    (declarations : Declaration.Signature Head) :
    Typing (Declaration.extendRules base declarations) operations context code type := by
  induction typed with
  | returnValue admitted => exact .returnValue (admitted.includeSignature declarations)
  | sequence firstFormed firstUniverse resultFormed resultUniverse _ _ firstIH bodyIH =>
      exact .sequence (firstFormed.includeSignature declarations) firstUniverse
        (resultFormed.includeSignature declarations) resultUniverse firstIH bodyIH
  | sequenceSigma formed universeWitness _ _ firstIH bodyIH =>
      exact .sequenceSigma (formed.includeSignature declarations) universeWitness firstIH bodyIH
  | choose _ _ firstIH secondIH => exact .choose firstIH secondIH
  | call formed admitted =>
      exact .call (formed.includeSignature declarations) (admitted.includeSignature declarations)
  | conv _ formed universeWitness conversion ih =>
      exact .conv ih (formed.includeSignature declarations) universeWitness
        (Declaration.Conv.includeSignature base declarations conversion)

theorem Judgment.includeSignature {base : Rules Head}
    {operations : OperationSignature Head Operation} {context : Ctx Head n}
    {code : Code Head Operation n} {type : Tm Head n}
    (admitted : Judgment base operations context code type)
    (declarations : Declaration.Signature Head) :
    Judgment (Declaration.extendRules base declarations) operations context code type :=
  ⟨admitted.context.includeSignature declarations,
    admitted.typing.includeSignature declarations⟩

#print axioms OperationFormation.includeSignature
#print axioms Typing.includeSignature
#print axioms FormationSensitive.ContextFormation.includeSignature
#print axioms Judgment.includeSignature

end ScopedComputation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace OpaqueRelatorScopedComputation

open Presentation Presentation.Declaration NativeIndexedFamilies
open Presentation.ScopedComputation
open Presentation.ScopedComputation.NativeExamples
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

variable {n m : Nat} {Γ : Tower.Ctx n} {Δ : Tower.Ctx m}

/-- The primitive result argument is independent of the installed native
rules. It accepts arbitrary terms admitted under those rules, not just terms
whose derivations can be reflected to the unextended Tower. -/
theorem native_primitive_typing (nativeRules : Rules Tower.Head)
    (operation : NativeExamples.Operation) (argument : Tower.Tm n)
    (state : Bool) (branch : BranchTrace) (output : WorldResult Bool (Tower.Tm n) Nat)
    (admitted : FormationSensitive.Typing nativeRules Γ argument
      (liftClosed (signature.input operation)))
    (returned : output ∈ primitiveWorlds operation argument state branch) :
    FormationSensitive.Typing nativeRules Γ output.answer (signature.result operation argument) := by
  cases operation with
  | markTrue =>
      simp only [primitiveWorlds, List.mem_singleton] at returned
      subst output
      exact admitted
  | markFalse =>
      simp only [primitiveWorlds, List.mem_singleton] at returned
      subst output
      exact admitted
  | reflexivity =>
      simp only [primitiveWorlds, List.mem_singleton] at returned
      subst output
      exact .reflIntro admitted

theorem primitive_preserves (declarations : Signature Tower.Head) :
    PrimitivePreserves (OpaqueRelatorExtension.rules declarations) signature Γ primitiveWorlds := by
  intro operation argument state branch output _ admitted returned
  exact native_primitive_typing _ operation argument state branch output admitted returned

/-- The same raw implementation satisfies both requirements in every target
scope and every combined-rule context. No opacity or old-context premise is
needed for this operation-specific qualification. -/
theorem qualified (declarations : Signature Tower.Head) (scope : Nat) :
    (ImplementationStudy.specification (OpaqueRelatorExtension.rules declarations) signature).Satisfies
      (ImplementationStudy.Native.implementation scope) := by
  apply (ImplementationStudy.satisfies_iff _ _ _).mpr
  exact ⟨handler_realizes, fun _ => primitive_preserves declarations⟩

/-- Every combined-admitted source computation is qualified under every
combined-admitted refined substitution into a formed target context. -/
theorem admitted_program_results (declarations : Signature Tower.Head)
    {code : Code Tower.Head NativeExamples.Operation n} {type : Tower.Tm n}
    (judgment : Judgment (OpaqueRelatorExtension.rules declarations) signature Γ code type)
    {environment : Sub Tower.Head n m}
    (target : FormationSensitive.ContextFormation (OpaqueRelatorExtension.rules declarations) Δ)
    (typed : FormationSensitive.CtxMor (OpaqueRelatorExtension.rules declarations) Γ Δ environment)
    {state : Bool} {branch : BranchTrace} {output : WorldResult Bool (Tower.Tm m) Nat}
    (returned : output ∈ runWorldsAt (Code.interpret handler environment code) state branch) :
    FormationSensitive.Judgment (OpaqueRelatorExtension.rules declarations) Δ output.answer
      (subst environment type) :=
  ImplementationStudy.qualified_interpretation (ImplementationStudy.Native.implementation m)
    (qualified declarations m) judgment target typed returned

/-- Inclusion of old source judgments supplies genuine combined-rule
derivations; the preservation theorem above is not restricted to their image. -/
theorem include_native_judgment (declarations : Signature Tower.Head)
    {code : Code Tower.Head NativeExamples.Operation n} {type : Tower.Tm n}
    (judgment : Judgment Tower.rules signature Γ code type) :
    Judgment (OpaqueRelatorExtension.rules declarations) signature Γ code type :=
  (judgment.includeSignature IntrinsicRelator.rawSignature).includeSignature declarations

theorem operation_formation (declarations : Signature Tower.Head) (operation : NativeExamples.Operation) :
    OperationFormation (OpaqueRelatorExtension.rules declarations) signature operation :=
  ((NativeExamples.operation_formation operation).includeSignature IntrinsicRelator.rawSignature).includeSignature
    declarations

theorem context_formed (declarations : Signature Tower.Head) :
    FormationSensitive.ContextFormation (OpaqueRelatorExtension.rules declarations) context :=
  (include_native_judgment declarations source_judgment).context

theorem source_judgments (declarations : Signature Tower.Head) :
    Judgment (OpaqueRelatorExtension.rules declarations) signature context first ground ∧
      Judgment (OpaqueRelatorExtension.rules declarations) signature context source
        (.sigma ground identityFamily) :=
  ⟨include_native_judgment declarations ⟨NativeExamples.context_formed, first_typing⟩,
    include_native_judgment declarations source_judgment⟩

theorem producer_judgments (declarations : Signature Tower.Head) :
    Judgment (OpaqueRelatorExtension.rules declarations) signature context
        ObservationStudy.Native.trueProducer ground ∧
      Judgment (OpaqueRelatorExtension.rules declarations) signature context
        ObservationStudy.Native.falseProducer ground :=
  ⟨include_native_judgment declarations ObservationStudy.Native.producers_judgments.1,
    include_native_judgment declarations ObservationStudy.Native.producers_judgments.2⟩

theorem resumption_judgments (declarations : Signature Tower.Head) :
    Judgment (OpaqueRelatorExtension.rules declarations) signature context
        ObservationStudy.Native.trueResumption (.sigma ground identityFamily) ∧
      Judgment (OpaqueRelatorExtension.rules declarations) signature context
        ObservationStudy.Native.falseResumption (.sigma ground identityFamily) :=
  ⟨include_native_judgment declarations ObservationStudy.Native.resumptions_judgments.1,
    include_native_judgment declarations ObservationStudy.Native.resumptions_judgments.2⟩

private theorem native_result (declarations : Signature Tower.Head)
    {code : Code Tower.Head NativeExamples.Operation 2} {type : Tower.Tm 2}
    (judgment : Judgment (OpaqueRelatorExtension.rules declarations) signature context code type)
    {output : WorldResult Bool (Tower.Tm 2) Nat}
    (returned : output ∈ Code.worlds primitiveWorlds ids code false []) :
    FormationSensitive.Judgment (OpaqueRelatorExtension.rules declarations) context output.answer type := by
  have typed : FormationSensitive.CtxMor (OpaqueRelatorExtension.rules declarations) context context ids := by
    intro index
    simpa only [ids, subst_ids] using
      (FormationSensitive.Typing.var (R := OpaqueRelatorExtension.rules declarations) (Γ := context) index)
  have interpreted : output ∈ runWorldsAt (Code.interpret handler ids code) false [] := by
    rw [Code.interpret_worlds handler primitiveWorlds handler_realizes]
    exact returned
  simpa only [subst_ids] using
    admitted_program_results declarations judgment (context_formed declarations) typed interpreted

/-- Native admission is re-established under the extended rules for the
actual world lists used by the unchanged contextual-view protocol. -/
theorem contextual_resumption_results (declarations : Signature Tower.Head)
    (entry : Nat × WorldResult Bool (Tower.Tm 2) Nat)
    (returned : entry ∈ ContextViews.resume ObservationStudy.Native.trueWorlds ++
      ContextViews.resume ObservationStudy.Native.falseWorlds) :
    FormationSensitive.Judgment (OpaqueRelatorExtension.rules declarations) context entry.2.answer
      (.sigma ground identityFamily) := by
  have erased : entry.2 ∈ (ContextViews.resume ObservationStudy.Native.trueWorlds ++
      ContextViews.resume ObservationStudy.Native.falseWorlds).map Prod.snd :=
    List.mem_map.mpr ⟨entry, returned, rfl⟩
  rw [List.map_append, ContextViews.Native.admitted_resumption_erasure.1,
    ContextViews.Native.admitted_resumption_erasure.2] at erased
  rcases List.mem_append.mp erased with fromTrue | fromFalse
  · exact native_result declarations (resumption_judgments declarations).1 fromTrue
  · exact native_result declarations (resumption_judgments declarations).2 fromFalse

/-- Qualification and resumed result admission concern the same unchanged
implementation and world lists as the exact operation-stable readout. -/
theorem contextual_operation_contract (declarations : Signature Tower.Head) :
    (ImplementationStudy.specification (OpaqueRelatorExtension.rules declarations) signature).Satisfies
        (ImplementationStudy.Native.implementation 2) ∧
    (∀ entry ∈ ContextViews.resume ObservationStudy.Native.trueWorlds ++
        ContextViews.resume ObservationStudy.Native.falseWorlds,
      FormationSensitive.Judgment (OpaqueRelatorExtension.rules declarations) context entry.2.answer
        (.sigma ground identityFamily)) ∧
    (∀ scope (first second : ContextViews.State scope),
      (ContextViews.observations scope).PolicyEquivalent first second ↔
        ContextViews.readout scope first = ContextViews.readout scope second) ∧
    (∀ worlds, ContextViews.readout .resumed (ContextViews.resume worlds) =
      ContextViews.resumeReadout (ContextViews.readout .producer worlds)) :=
  ⟨qualified declarations 2, contextual_resumption_results declarations,
    ContextViews.equivalent_iff_readout, ContextViews.readout_resume⟩

/-- Agreement with the supplied world semantics is not created by admitting
more native declarations. The existing altered handler still fails to realize
the unchanged primitive worlds, although those worlds preserve native types. -/
theorem wrong_handler_control (declarations : Signature Tower.Head) :
    ImplementationStudy.Preserves (OpaqueRelatorExtension.rules declarations) signature
        ImplementationStudy.Native.unrealized ∧
      ¬ (ImplementationStudy.specification (OpaqueRelatorExtension.rules declarations) signature).Satisfies
        ImplementationStudy.Native.unrealized := by
  refine ⟨fun _ => primitive_preserves declarations, ?_⟩
  intro qualified
  exact ImplementationStudy.Native.unrealized_not_realizes
    ((ImplementationStudy.satisfies_iff _ _ _).mp qualified).1

private theorem refl_generation {nativeRules : Rules Tower.Head}
    {term type : Tower.Tm n} (typed : FormationSensitive.Typing nativeRules Γ term type) :
    ∀ {value : Tower.Tm n}, term = .refl value →
      ∃ carrier, FormationSensitive.Typing nativeRules Γ value carrier ∧
        TypeAdjustment nativeRules (.id carrier value value) type := by
  induction typed with
  | reflIntro admitted _ =>
      intro value same
      cases same
      exact ⟨_, admitted, .refl _⟩
  | cumul _ order ih =>
      intro value same
      obtain ⟨carrier, admitted, adjustment⟩ := ih same
      exact ⟨carrier, admitted, .trans adjustment (.cumulative order)⟩
  | conv _ _ _ conversion ih _ =>
      intro value same
      obtain ⟨carrier, admitted, adjustment⟩ := ih same
      exact ⟨carrier, admitted, .trans adjustment (.conversion conversion)⟩
  | _ => intro value same; cases same

private theorem identity_index_shape {carrier target : Tower.Tm n} {index : Fin n}
    (steps : NativeRelatorConversionParallel.ParStar (.id carrier (.var index) (.var index)) target) :
    ∃ carrier', target = .id carrier' (.var index) (.var index) := by
  induction steps with
  | refl => exact ⟨_, rfl⟩
  | tail previous finalStep ih =>
      obtain ⟨_, rfl⟩ := ih
      cases finalStep with
      | id _ left right =>
          cases left
          cases right
          exact ⟨_, rfl⟩

private theorem identity_index_head_disjoint {declarations : Signature Tower.Head}
    (opaqueDeclarations : OpaqueRelatorExtension.Opacity declarations)
    (carrier : Tower.Tm n) (index : Fin n) (head : Tower.Head) :
    ¬ Conv (OpaqueRelatorExtension.rules declarations).headEq
      (.id carrier (.var index) (.var index)) (.head head)
      (OpaqueRelatorExtension.rules declarations).computation := by
  intro conversion
  obtain ⟨common, identitySteps, headSteps⟩ := NativeRelatorConversionParallel.conversion_join
    ((OpaqueRelatorExtension.conversion_iff opaqueDeclarations).mp conversion)
  obtain ⟨_, identityShape⟩ := identity_index_shape identitySteps
  obtain ⟨_, headShape⟩ := NativeRelatorConversionParallel.parStar_head_shape headSteps
  rw [identityShape] at headShape
  cases headShape

/-- Opaque declarations do not let reflexivity at the other variable acquire
the selected index's family, even with conversion and cumulativity tails. -/
theorem wrong_selected_index_not_admitted {declarations : Signature Tower.Head}
    (opaqueDeclarations : OpaqueRelatorExtension.Opacity declarations) :
    ¬ FormationSensitive.Typing (OpaqueRelatorExtension.rules declarations) context
      (.refl older) (signature.result .reflexivity newer) := by
  intro typed
  obtain ⟨carrier, _, adjustment⟩ := refl_generation typed rfl
  have conversion := adjustment.toConvOfSourceDisjointHeads
    (identity_index_head_disjoint opaqueDeclarations carrier (1 : Fin 2))
  obtain ⟨common, olderSteps, newerSteps⟩ := NativeRelatorConversionParallel.conversion_join
    ((OpaqueRelatorExtension.conversion_iff opaqueDeclarations).mp conversion)
  obtain ⟨_, olderShape⟩ := identity_index_shape olderSteps
  obtain ⟨_, newerShape⟩ := identity_index_shape newerSteps
  have impossible := olderShape.symm.trans newerShape
  cases impossible

/-- The altered handler realizes its separately authored altered worlds, yet
those same worlds violate the extended-rule dependent result requirement. -/
theorem wrong_result_control {declarations : Signature Tower.Head}
    (opaqueDeclarations : OpaqueRelatorExtension.Opacity declarations) :
    ImplementationStudy.Realizes ImplementationStudy.Native.misindexed ∧
      ¬ (ImplementationStudy.specification (OpaqueRelatorExtension.rules declarations) signature).Satisfies
        ImplementationStudy.Native.misindexed := by
  refine ⟨ImplementationStudy.Native.misindexed_realizes, ?_⟩
  intro qualified
  have preserves := ((ImplementationStudy.satisfies_iff _ _ _).mp qualified).2 context
  have returned :
      ({ branch := [], answer := .refl older, state := false, intents := [40] } :
        WorldResult Bool (Tower.Tm 2) Nat) ∈ misindexedWorlds .reflexivity newer false [] :=
    List.mem_singleton_self _
  exact wrong_selected_index_not_admitted opaqueDeclarations
    (preserves .reflexivity newer false [] _ (operation_formation declarations .reflexivity)
      (.var 0) returned)

namespace Common

/-- This telescope genuinely contains the common native List HOLSequence /
wire Data payload type, in addition to the two original ground variables. -/
def context : Tower.Ctx 3 :=
  .snoc NativeExamples.context HOLNativeRelatorCompatibility.mixedPayloadType

theorem context_formed : FormationSensitive.ContextFormation HOLNativeRelatorCompatibility.rules context :=
  .snoc (OpaqueRelatorScopedComputation.context_formed HOLNativeRelatorCompatibility.signature)
    (HOLNativeRelatorCompatibility.mixed_payload_type_formed NativeExamples.context) (.sort _)

/-- Each native ground argument retains the new payload syntactically in a
pair projection. The scoped evaluator does not normalize away that payload. -/
def environment : Sub Tower.Head 2 3 :=
  fun index => .fst (.pair (.var index.succ) (.var 0))

private theorem old_argument (index : Fin 2) :
    FormationSensitive.Typing HOLNativeRelatorCompatibility.rules context
      (.var index.succ) ground := by
  fin_cases index <;> exact .var _

private theorem payload_argument :
    FormationSensitive.Typing HOLNativeRelatorCompatibility.rules context (.var 0)
      HOLNativeRelatorCompatibility.mixedPayloadType := by
  simpa [context, HOLNativeRelatorCompatibility.mixedPayloadType,
    HOLNativeRelatorCompatibility.holSequenceType, Intrinsic.listApp,
    NativeWireData.dataType, rename] using
      (FormationSensitive.Typing.var (R := HOLNativeRelatorCompatibility.rules) (Γ := context) 0)

private theorem argument_pair_formed :
    FormationSensitive.Typing HOLNativeRelatorCompatibility.rules context
      (.sigma ground HOLNativeRelatorCompatibility.mixedPayloadType)
      (sortTm (.max Tower.zero (.max Intrinsic.elementLevel Tower.zero))) :=
  .sigmaForm (.headType .legacyGround) (.sort _)
    (HOLNativeRelatorCompatibility.mixed_payload_type_formed (.snoc context ground))
    (.sort _) (.sorts _ _)

private theorem argument_typed (index : Fin 2) :
    FormationSensitive.Typing HOLNativeRelatorCompatibility.rules context (environment index) ground := by
  apply FormationSensitive.Typing.fstElim
  apply FormationSensitive.Typing.pairIntro argument_pair_formed (.sort _) (old_argument index)
  simpa [HOLNativeRelatorCompatibility.mixedPayloadType,
    HOLNativeRelatorCompatibility.holSequenceType, Intrinsic.listApp,
    NativeWireData.dataType, inst0, subst] using payload_argument

theorem environment_typed :
    FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules NativeExamples.context context environment := by
  intro index
  fin_cases index <;> exact argument_typed _

/-- This source judgment is in the genuinely extended telescope and contains
its new payload in both actually substituted producer arguments. -/
theorem source_judgment :
    Judgment HOLNativeRelatorCompatibility.rules signature context (source.substitute environment)
      (subst environment (.sigma ground identityFamily)) :=
  ((source_judgments HOLNativeRelatorCompatibility.signature).2).substitute
    context_formed environment_typed

theorem source_results {state : Bool} {branch : BranchTrace}
    {output : WorldResult Bool (Tower.Tm 3) Nat}
    (returned : output ∈ runWorldsAt (Code.interpret handler environment source) state branch) :
    FormationSensitive.Judgment HOLNativeRelatorCompatibility.rules context output.answer
      (subst environment (.sigma ground identityFamily)) :=
  admitted_program_results HOLNativeRelatorCompatibility.signature
    (source_judgments HOLNativeRelatorCompatibility.signature).2
    context_formed environment_typed returned

/-- The two independently admitted payload-bearing arguments occur in the
actual dependent answers; no type erasure or native payload evaluation occurs. -/
theorem source_worlds (state : Bool) (branch : BranchTrace) :
    runWorldsAt (Code.interpret handler environment source) state branch =
      [{ branch := false :: branch, answer := .pair (environment 1) (.refl (environment 1)),
         state := true, intents := [10, 30] },
       { branch := true :: branch, answer := .pair (environment 0) (.refl (environment 0)),
         state := false, intents := [20, 40] }] := by
  rw [Code.interpret_worlds handler primitiveWorlds handler_realizes]
  rfl

def fillPayload (wire : NativeWireData.Wire) : Sub Tower.Head 3 2 :=
  consSub (HOLNativeRelatorCompatibility.mixedPayload wire) ids

theorem fillPayload_typed (wire : NativeWireData.Wire) :
    FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules context NativeExamples.context
      (fillPayload wire) := by
  apply extendEnvironment
  · intro index
    simpa only [ids, subst_ids] using
      (FormationSensitive.Typing.var (R := HOLNativeRelatorCompatibility.rules)
        (Γ := NativeExamples.context) index)
  · simpa only [subst_ids] using
      HOLNativeRelatorCompatibility.mixed_payload_typed NativeExamples.context wire

/-- Compose the actual native substitutions: the new context variable is
filled by the existing common HOL-list/wire-data term. -/
def filledEnvironment (wire : NativeWireData.Wire) : Sub Tower.Head 2 2 :=
  subComp (fillPayload wire) environment

theorem filledEnvironment_typed (wire : NativeWireData.Wire) :
    FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules NativeExamples.context
      NativeExamples.context (filledEnvironment wire) := by
  intro index
  have admitted := (environment_typed index).substitute (fillPayload_typed wire)
  rw [subst_comp] at admitted
  exact admitted

theorem filledEnvironment_value (wire : NativeWireData.Wire) (index : Fin 2) :
    filledEnvironment wire index =
      .fst (.pair (.var index) (HOLNativeRelatorCompatibility.mixedPayload wire)) := by
  simp [filledEnvironment, subComp, environment, fillPayload, subst, consSub, ids]

theorem filled_source_results (wire : NativeWireData.Wire)
    {state : Bool} {branch : BranchTrace} {output : WorldResult Bool (Tower.Tm 2) Nat}
    (returned : output ∈
      runWorldsAt (Code.interpret handler (filledEnvironment wire) source) state branch) :
    FormationSensitive.Judgment HOLNativeRelatorCompatibility.rules NativeExamples.context output.answer
      (subst (filledEnvironment wire) (.sigma ground identityFamily)) :=
  admitted_program_results HOLNativeRelatorCompatibility.signature
    (source_judgments HOLNativeRelatorCompatibility.signature).2
    (OpaqueRelatorScopedComputation.context_formed HOLNativeRelatorCompatibility.signature)
    (filledEnvironment_typed wire) returned

/-- Both ground-valued source arguments now contain an actual newly declared
HOL nil and native wire payload, and their exact selected-dependent results
are produced by the original operation handler. -/
theorem filled_source_worlds (wire : NativeWireData.Wire) (state : Bool) (branch : BranchTrace) :
    runWorldsAt (Code.interpret handler (filledEnvironment wire) source) state branch =
      [{ branch := false :: branch,
         answer := .pair (.fst (.pair older (HOLNativeRelatorCompatibility.mixedPayload wire)))
           (.refl (.fst (.pair older (HOLNativeRelatorCompatibility.mixedPayload wire)))),
         state := true, intents := [10, 30] },
       { branch := true :: branch,
         answer := .pair (.fst (.pair newer (HOLNativeRelatorCompatibility.mixedPayload wire)))
           (.refl (.fst (.pair newer (HOLNativeRelatorCompatibility.mixedPayload wire)))),
         state := false, intents := [20, 40] }] := by
  rw [Code.interpret_worlds handler primitiveWorlds handler_realizes]
  rfl

/-- The actual payload-bearing workload uses the unchanged contextual view
and resumption, with every resumed answer admitted in the common rules. -/
theorem filled_contextual_protocol (wire : NativeWireData.Wire) (state : Bool) (branch : BranchTrace) :
    let producerWorlds := Code.worlds primitiveWorlds (filledEnvironment wire) first state branch
    (ContextViews.resume producerWorlds).map Prod.snd =
        runWorldsAt (Code.interpret handler (filledEnvironment wire) source) state branch ∧
    ContextViews.readout .resumed (ContextViews.resume producerWorlds) =
        ContextViews.resumeReadout (ContextViews.readout .producer producerWorlds) ∧
    (∀ entry ∈ ContextViews.resume producerWorlds,
      FormationSensitive.Judgment HOLNativeRelatorCompatibility.rules NativeExamples.context
        entry.2.answer (subst (filledEnvironment wire) (.sigma ground identityFamily))) := by
  dsimp only
  have erased :
      (ContextViews.resume
        (Code.worlds primitiveWorlds (filledEnvironment wire) first state branch)).map Prod.snd =
      runWorldsAt (Code.interpret handler (filledEnvironment wire) source) state branch := by
    rw [Code.interpret_worlds handler primitiveWorlds handler_realizes]
    rfl
  refine ⟨erased, ContextViews.readout_resume _, ?_⟩
  intro entry returned
  apply filled_source_results wire (output := entry.2)
  rw [← erased]
  exact List.mem_map.mpr ⟨entry, returned, rfl⟩

end Common

#print axioms native_primitive_typing
#print axioms primitive_preserves
#print axioms qualified
#print axioms admitted_program_results
#print axioms include_native_judgment
#print axioms operation_formation
#print axioms context_formed
#print axioms source_judgments
#print axioms producer_judgments
#print axioms resumption_judgments
#print axioms native_result
#print axioms contextual_resumption_results
#print axioms contextual_operation_contract
#print axioms wrong_handler_control
#print axioms refl_generation
#print axioms identity_index_shape
#print axioms identity_index_head_disjoint
#print axioms wrong_selected_index_not_admitted
#print axioms wrong_result_control
#print axioms Common.context
#print axioms Common.context_formed
#print axioms Common.environment
#print axioms Common.old_argument
#print axioms Common.payload_argument
#print axioms Common.argument_pair_formed
#print axioms Common.argument_typed
#print axioms Common.environment_typed
#print axioms Common.source_judgment
#print axioms Common.source_results
#print axioms Common.source_worlds
#print axioms Common.fillPayload
#print axioms Common.fillPayload_typed
#print axioms Common.filledEnvironment
#print axioms Common.filledEnvironment_typed
#print axioms Common.filledEnvironment_value
#print axioms Common.filled_source_results
#print axioms Common.filled_source_worlds
#print axioms Common.filled_contextual_protocol

end OpaqueRelatorScopedComputation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
