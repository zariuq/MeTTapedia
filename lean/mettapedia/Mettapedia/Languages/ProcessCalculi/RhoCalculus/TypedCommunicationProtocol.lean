import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReductionProtocolComparison
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness

/-!
# A typed strict-core communication protocol for rho

The full rho reduction relation is intentionally larger than the fragment for
which native subject preservation has been proved.  This file therefore does
not attach a global typing claim to every rho step.  It isolates direct COMM
instances satisfying the existing strict-core and quote-opacity conditions,
derives their target typing modulo the established subject equivalence, and
turns those instances into a proof-relevant subprotocol of rho reduction.

The source is typed exactly.  The live semantic contractum is typed up to
`ProcResidualEquiv`, equivalently in the saturation of the exact typing
predicate.  This is the strongest theorem supplied by the existing native
typing development without an additional agreement hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationProtocol

open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Dynamics.ProofRelevantRelationProtocol
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReductionProtocolComparison
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness

/-! ## The exact native typing obligation -/

/-- The common process type used by the strict COMM fragment. -/
def processTruth : NativeType :=
  ⟨"Proc", fun _ => True, by simp⟩

/-- A channel capable of carrying quotations of `processTruth` payloads. -/
def communicationName : NativeType :=
  ⟨"Name", rawStepFuture (fun _ => True), by simp⟩

/-- Native typing data sufficient for the existing strict-core semantic COMM
preservation theorem.  The context and residual parallel processes remain
parameters; only the result predicate is fixed to truth because rho parallel
composition requires that public process type. -/
structure CommTypingData (context : TypingContext) where
  channel : Pattern
  body : Pattern
  payload : Pattern
  rest : List Pattern
  excluded : List String
  channelTyped : HasType context channel communicationName
  bodyTyped : ∀ name, name ∉ excluded ->
    HasType (context.extend name communicationName)
      (openBVar 0 (.fvar name) body) processTruth
  payloadTyped : HasType context payload processTruth
  restTyped : ∀ process ∈ rest, HasType context process processTruth
  payloadLocallyClosed : lc payload = true
  bodyStrict : strictCoreCommBody body = true

namespace CommTypingData

/-- The complete COMM redex is exactly typed. -/
theorem sourceTyped {context : TypingContext}
    (data : CommTypingData context) :
    HasType context
      (.collection .hashBag
        ([.apply "PInput" [data.channel, .lambda none data.body],
          .apply "POutput" [data.channel, data.payload]] ++ data.rest) none)
      processTruth := by
  have inputTyped :
      HasType context
        (.apply "PInput" [data.channel, .lambda none data.body])
        processTruth := by
    simpa [processTruth, communicationName] using
      (HasType.input data.excluded data.channelTyped data.bodyTyped)
  have outputTyped :
      HasType context (.apply "POutput" [data.channel, data.payload])
        processTruth := by
    simpa [processTruth, communicationName] using
      (HasType.output data.channelTyped data.payloadTyped)
  apply HasType.par
  intro process membership
  rcases List.mem_append.mp membership with headMembership | restMembership
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at headMembership
    rcases headMembership with rfl | rfl
    · exact inputTyped
    · exact outputTyped
  · exact data.restTyped process restMembership

/-- The live semantic COMM residual has the strongest currently established
native typing: exact typing modulo process subject equivalence. -/
theorem resultTypedUpToSubjectEquiv {context : TypingContext}
    (data : CommTypingData context) :
    HasTypeUpToSubjectEquiv context
      (semanticCommSubst data.body data.payload) processTruth := by
  simpa [processTruth, communicationName] using
    (comm_preserves_type_semantic_upToSubjectEquiv_of_strictCoreCommBody
      data.bodyTyped data.payloadTyped data.payloadLocallyClosed data.bodyStrict)

/-- Subject equivalence is stable under the surrounding parallel collection,
so the complete COMM contractum is typed up to the same relation. -/
theorem targetTypedUpToSubjectEquiv {context : TypingContext}
    (data : CommTypingData context) :
    HasTypeUpToSubjectEquiv context
      (.collection .hashBag
        (semanticCommSubst data.body data.payload :: data.rest) none)
      processTruth := by
  rcases data.resultTypedUpToSubjectEquiv with
    ⟨representative, subjectEquivalent, representativeTyped⟩
  have residualEquivalent :
      ProcResidualEquiv
        (semanticCommSubst data.body data.payload) representative := by
    simpa [processTruth, TypeSubjectEquiv] using subjectEquivalent
  refine ⟨.collection .hashBag (representative :: data.rest) none, ?_, ?_⟩
  · apply TypeSubjectEquiv.of_proc
    refine ProcResidualEquiv.collection_cong .hashBag
      (semanticCommSubst data.body data.payload :: data.rest)
      (representative :: data.rest) none rfl ?_
    intro index sourceBound targetBound
    cases index with
    | zero => simpa using residualEquivalent
    | succ tailIndex =>
        simp only [List.get_cons_succ]
        exact ProcResidualEquiv.refl _
  · apply HasType.par
    intro process membership
    simp only [List.mem_cons] at membership
    rcases membership with rfl | restMembership
    · exact representativeTyped
    · exact data.restTyped process restMembership

end CommTypingData

/-! ## Closed, structurally valid COMM instances -/

/-- A direct COMM instance carrying both the declaration-derived closedness
evidence needed by the rho GSLT and the independent native typing evidence
needed by the subject theorem. -/
structure ClosedCommData extends CommTypingData TypingContext.empty where
  channelSorted :
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty [] channel
  channelSafe : binderSafeAt "NQuote" 0 channel = true
  bodySorted :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      [rhoReflectivePresentation.nameSort] body
  bodySafe : binderSafeAt "NQuote" 1 body = true
  payloadSorted :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] payload
  payloadSafe : binderSafeAt "NQuote" 0 payload = true
  restSorted :
    ProcListWellSorted rhoReflectivePresentation FreeSortContext.empty [] rest
  restSafe : binderSafeListAt "NQuote" 0 rest = true

namespace ClosedCommData

/-- Closed source process determined by one typed COMM instance. -/
def source (data : ClosedCommData) : RhoProcess :=
  ⟨.collection .hashBag
      ([.apply "PInput" [data.channel, .lambda none data.body],
        .apply "POutput" [data.channel, data.payload]] ++ data.rest) none,
    (rhoClosedTermWellSorted_process_iff _).mpr ⟨
      .parallel
        (.cons (.input data.channelSorted data.bodySorted)
          (.cons (.output data.channelSorted data.payloadSorted)
            data.restSorted)),
      by
        simpa [binderSafeAt, binderSafeListAt] using
          ⟨⟨data.channelSafe, data.bodySafe⟩,
            ⟨⟨data.channelSafe, data.payloadSafe⟩, data.restSafe⟩⟩⟩⟩

/-- The declaration-derived direct COMM step. -/
def rawStep (data : ClosedCommData) :
    RhoStep data.source.1
      (.collection .hashBag
        (semanticCommSubst data.body data.payload :: data.rest) none) :=
  RhoStep.comm data.channel data.body data.payload data.rest
    data.bodySorted data.payloadSorted

/-- Closed target process obtained from the proved closedness of `rawStep`. -/
def target (data : ClosedCommData) : RhoProcess :=
  data.source.stepTarget data.rawStep

/-- The direct typed COMM instance is an exact occurrence of the established
equation-saturated rho system. -/
noncomputable def occurrence (data : ClosedCommData) :
    RewriteOccurrence data.source data.target where
  redex := data.source
  contractum := data.target
  sourceEquation := rfl
  derivedStep := data.rawStep
  rawReceipt := Classical.choice
    (rhoRewriteSystem_reduces_sound data.rawStep)
  targetEquation := rfl

theorem sourceNativeTyped (data : ClosedCommData) :
    HasType TypingContext.empty data.source.1 processTruth := by
  simpa [source] using data.toCommTypingData.sourceTyped

theorem targetNativeTypedUpToSubjectEquiv (data : ClosedCommData) :
    HasTypeUpToSubjectEquiv TypingContext.empty data.target.1 processTruth := by
  change HasTypeUpToSubjectEquiv TypingContext.empty
    (.collection .hashBag
      (semanticCommSubst data.body data.payload :: data.rest) none)
    processTruth
  exact data.toCommTypingData.targetTypedUpToSubjectEquiv

end ClosedCommData

/-! ## The typed subprotocol and its rho erasure -/

/-- Exact direct-COMM receipts whose typing preservation is derived rather
than postulated. -/
inductive StrictCoreCommOccurrence : RhoProcess -> RhoProcess -> Type where
  | intro (data : ClosedCommData) :
      StrictCoreCommOccurrence data.source data.target

namespace StrictCoreCommOccurrence

/-- Forget the typed-fragment evidence to the full rho occurrence. -/
noncomputable def toRewriteOccurrence {source target : RhoProcess} :
    StrictCoreCommOccurrence source target ->
      RewriteOccurrence source target
  | .intro data => data.occurrence

/-- Every typed-fragment receipt carries exact source typing and derived
target typing modulo the established subject equivalence. -/
theorem preservesNativeTyping {source target : RhoProcess}
    (occurrence : StrictCoreCommOccurrence source target) :
    HasType TypingContext.empty source.1 processTruth /\
      HasTypeUpToSubjectEquiv TypingContext.empty target.1 processTruth := by
  cases occurrence with
  | intro data =>
      exact ⟨data.sourceNativeTyped, data.targetNativeTypedUpToSubjectEquiv⟩

end StrictCoreCommOccurrence

/-- Canonical indexed protocol for the proved typed direct-COMM fragment. -/
abbrev typedCommProtocol := protocol StrictCoreCommOccurrence

/-- Its literal-equality endpoint GSLT. -/
abbrev typedCommSystem := lts typedCommProtocol

/-- Every typed COMM protocol step is an established rho GSLT step. -/
theorem typedComm_step_sound {source target : RhoProcess} :
    typedCommSystem.Step source target ->
      rhoLanguageDefGSLT.Step source target := by
  intro typedStep
  obtain ⟨occurrence⟩ :=
    (lts_step_iff StrictCoreCommOccurrence).1 typedStep
  exact occurrence.toRewriteOccurrence.toStep

/-! ## Positive and negative controls -/

/-- The existing closed nil communication satisfies every structural and
native typing obligation of the strict fragment. -/
def closedNilCommData : ClosedCommData where
  channel := closedNilName.1
  body := .apply "PZero" []
  payload := .apply "PZero" []
  rest := []
  excluded := []
  channelTyped := by
    change HasType TypingContext.empty
      (.apply "NQuote" [.apply "PZero" []]) communicationName
    simpa [communicationName, processTruth] using
      (HasType.quote (Γ := TypingContext.empty) HasType.nil)
  bodyTyped := by
    intro name _
    simpa [openBVar, processTruth] using
      (HasType.nil (Γ := TypingContext.empty.extend name communicationName))
  payloadTyped := by
    simpa [processTruth] using (HasType.nil (Γ := TypingContext.empty))
  restTyped := by simp
  payloadLocallyClosed := by decide
  bodyStrict := by decide
  channelSorted := .quote .unit
  channelSafe := by decide
  bodySorted := .unit
  bodySafe := by decide
  payloadSorted := .unit
  payloadSafe := by decide
  restSorted := .nil
  restSafe := by decide

noncomputable def closedNilCommOccurrence :
    StrictCoreCommOccurrence closedNilCommData.source
      closedNilCommData.target :=
  .intro closedNilCommData

theorem closedNilCommData_source_eq :
    closedNilCommData.source = closedCommSource := by
  apply Subtype.ext
  rfl

theorem closedNilCommData_target_eq :
    closedNilCommData.target = closedCommTarget := by
  apply Subtype.ext
  change
    (closedNilCommData.source.stepTarget
      closedNilCommData.rawStep).toPattern = closedCommTarget.toPattern
  rw [RhoClosedTerm.stepTarget_toPattern]
  simp [closedNilCommData, closedCommTarget, RhoClosedTerm.toPattern,
    semanticCommSubst, semanticSubstProc, semanticNormalizeProc]

theorem closedNilComm_protocol_control :
    typedCommSystem.Step closedNilCommData.source closedNilCommData.target /\
      HasType TypingContext.empty closedNilCommData.source.1 processTruth /\
      HasTypeUpToSubjectEquiv TypingContext.empty
        closedNilCommData.target.1 processTruth := by
  refine ⟨(lts_step_iff StrictCoreCommOccurrence).2
    ⟨closedNilCommOccurrence⟩, ?_⟩
  exact closedNilCommOccurrence.preservesNativeTyping

/-- The positive typed protocol control is the existing closed rho COMM
example, not a separate fixture. -/
theorem existingClosedComm_typed_protocol_control :
    typedCommSystem.Step closedCommSource closedCommTarget /\
      HasType TypingContext.empty closedCommSource.1 processTruth /\
      HasTypeUpToSubjectEquiv TypingContext.empty
        closedCommTarget.1 processTruth := by
  simpa [closedNilCommData_source_eq, closedNilCommData_target_eq] using
    closedNilComm_protocol_control

/-- A structurally meaningful process body whose bound channel occurs below
quotation.  Ordinary opening can type it, but the quote-opacity guard rejects
it from the strict semantic COMM fragment. -/
def quotedBinderBody : Pattern :=
  .apply "POutput"
    [.bvar 0,
      .apply "PDrop"
        [.apply "NQuote"
          [.apply "POutput" [.bvar 0, .apply "PZero" []]]]]

theorem quotedBinderBody_structurally_sorted :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      [rhoReflectivePresentation.nameSort] quotedBinderBody := by
  apply ProcWellSorted.output
  · exact NameWellSorted.bvar (by simp [rhoReflectivePresentation])
  · exact ProcWellSorted.drop
      (NameWellSorted.quote
        (ProcWellSorted.output
          (NameWellSorted.bvar (by simp [rhoReflectivePresentation]))
          ProcWellSorted.unit))

theorem quotedBinderBody_open_typed (name : String) :
    HasType (TypingContext.empty.extend name communicationName)
      (openBVar 0 (.fvar name) quotedBinderBody) processTruth := by
  have channelTyped :
      HasType (TypingContext.empty.extend name communicationName)
        (.fvar name) communicationName :=
    HasType.fvar lookup_extend_eq
  have nilTyped :
      HasType (TypingContext.empty.extend name communicationName)
        (.apply "PZero" []) processTruth := by
    simpa [processTruth] using
      (HasType.nil
        (Γ := TypingContext.empty.extend name communicationName))
  have innerOutput :
      HasType (TypingContext.empty.extend name communicationName)
        (.apply "POutput" [.fvar name, .apply "PZero" []]) processTruth := by
    simpa [processTruth, communicationName] using
      (HasType.output channelTyped nilTyped)
  have quoted :
      HasType (TypingContext.empty.extend name communicationName)
        (.apply "NQuote"
          [.apply "POutput" [.fvar name, .apply "PZero" []]])
        communicationName := by
    simpa [processTruth, communicationName] using HasType.quote innerOutput
  have dropped := HasType.drop quoted
  have outer := HasType.output channelTyped dropped
  simpa [quotedBinderBody, processTruth, communicationName, openBVar] using outer

theorem quotedBinderBody_not_strict :
    strictCoreCommBody quotedBinderBody = false := by
  decide

/-- Structural sorting and ordinary opened typing do not imply admission to
the quote-safe semantic COMM fragment. -/
theorem quotedBinderBody_boundary :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
        [rhoReflectivePresentation.nameSort] quotedBinderBody /\
      (forall name,
        HasType (TypingContext.empty.extend name communicationName)
          (openBVar 0 (.fvar name) quotedBinderBody) processTruth) /\
      strictCoreCommBody quotedBinderBody = false :=
  ⟨quotedBinderBody_structurally_sorted,
    quotedBinderBody_open_typed,
    quotedBinderBody_not_strict⟩

/-! ## Axiom audit -/

#print axioms CommTypingData.sourceTyped
#print axioms CommTypingData.resultTypedUpToSubjectEquiv
#print axioms CommTypingData.targetTypedUpToSubjectEquiv
#print axioms ClosedCommData.occurrence
#print axioms StrictCoreCommOccurrence.preservesNativeTyping
#print axioms typedComm_step_sound
#print axioms closedNilComm_protocol_control
#print axioms existingClosedComm_typed_protocol_control
#print axioms quotedBinderBody_boundary

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationProtocol
