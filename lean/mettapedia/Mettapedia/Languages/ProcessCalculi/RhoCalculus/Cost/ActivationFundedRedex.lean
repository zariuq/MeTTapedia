import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCanonicalSubstitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedOccurrenceRHS
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationRuntime

/-!
# A funded redex fires

The runtime sees a configuration as a bag of components. This module proves one statement about
images of generated syntax: if the bag of an image is a funded redex at the image of a closed
channel together with any frame, the runtime fires there.

* `Funding` is how the redex is paid for: one purse under the signed pair (`whole`), or one purse
  under each of the two separately signed endpoints (`split`).
* `ConfigImage.funded_redex_runtime`: the runtime has the declarative step of the funded redex
  beside the frame.
* `ConfigImage.funded_redex_fires` is the statement: a candidate of the runtime at the channel,
  spending the keys of the signatures; a path of one step from the normalized configuration; and
  what the runtime observes afterwards is the image of the generated substitution, the rest of
  each purse, and the frame.
* `ConfigImage.funded_redex_fires_readback` adds the readouts of the generated source and of any
  generated target with that bag.

The shape of the generated syntax does not occur in the statement. An isolated contact, a contact
in a bag, two contacts with one purse each, and a contact inside an outer funded contact are all
instances; the files that state them come after this one.

Two facts make the statement independent of the shape: the canonical configuration of a term, and
what the runtime observes of it, are functions of its bag of components
(`decodeRawConfig_normalizeConfig_literal`, `structuralDenote_literal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-- Combine exact covers at one location without merging their physical purse cells. -/
def LocatedTokenCover.combine {Ground : Type u} {location : CostName Ground}
    {leftDemand rightDemand : CostSig Ground}
    {leftAvailable rightAvailable leftResidual rightResidual : Multiset (LocatedPurse Ground)}
    (left : LocatedTokenCover location leftDemand leftAvailable leftResidual)
    (right : LocatedTokenCover location rightDemand rightAvailable rightResidual) :
    LocatedTokenCover location (leftDemand + rightDemand)
      (leftAvailable + rightAvailable) (leftResidual + rightResidual) where
  chosen := left.chosen + right.chosen
  untouched := left.untouched + right.untouched
  available_eq := by
    calc
      leftAvailable + rightAvailable =
          (left.chosen.map (fun choice => ⟨location, .cons choice.head choice.tail⟩) + left.untouched) +
          (right.chosen.map (fun choice => ⟨location, .cons choice.head choice.tail⟩) + right.untouched) :=
        congrArg₂ (· + ·) left.available_eq right.available_eq
      _ = _ := by rw [Multiset.map_add]; ac_rfl
  residual_eq := by
    calc
      leftResidual + rightResidual =
          (left.chosen.map (fun choice => ⟨location, choice.tail⟩) + left.untouched) +
          (right.chosen.map (fun choice => ⟨location, choice.tail⟩) + right.untouched) :=
        congrArg₂ (· + ·) left.residual_eq right.residual_eq
      _ = _ := by rw [Multiset.map_add]; ac_rfl
  demand_eq := by
    calc
      leftDemand + rightDemand =
          (left.chosen.map SelectedPurseHead.head).sum + (right.chosen.map SelectedPurseHead.head).sum :=
        congrArg₂ (· + ·) left.demand_eq right.demand_eq
      _ = _ := by rw [Multiset.map_add, Multiset.sum_add]

namespace ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-! ## The raw encoding of an image is accepted by the runtime -/

mutual
  theorem NameImage.literal_runtimeBinderSafeAt {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage depth source name) :
      (literalEncodeName name).runtimeBinderSafeAt depth = true := by
    cases image with
    | bvar bound => simpa [literalEncodeName, CostName.relabel, encodeCostName,
        RawCostName.runtimeBinderSafeAt] using bound
    | baseZeroQuote => rfl
    | quote code => exact code.literal_runtimeBinderSafeAt

  theorem CodeImage.literal_runtimeBinderSafeAt {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) :
      (literalEncodeTerm term).runtimeBinderSafeAt depth = true := by
    cases image with
    | zero => rfl
    | drop name => exact name.literal_runtimeBinderSafeAt
    | signed signature accepted process => exact process.literal_runtimeBinderSafeAt
    | collection codes => exact codes.literal_runtimeBinderSafeAt

  theorem ProcImage.literal_runtimeBinderSafeAt {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage depth source process) :
      (literalEncodeProc process).runtimeBinderSafeAt depth = true := by
    cases image with
    | zero => rfl
    | send name code =>
      change ((literalEncodeName _).runtimeBinderSafeAt depth &&
        (literalEncodeTerm _).runtimeBinderSafeAt depth) = true
      rw [name.literal_runtimeBinderSafeAt, code.literal_runtimeBinderSafeAt]
      rfl
    | recv name code =>
      change ((literalEncodeName _).runtimeBinderSafeAt depth &&
        (literalEncodeTerm _).runtimeBinderSafeAt (depth + 1)) = true
      rw [name.literal_runtimeBinderSafeAt, code.literal_runtimeBinderSafeAt]
      rfl
    | pair left right =>
      change ((literalEncodeProc _).runtimeBinderSafeAt depth &&
        (literalEncodeProc _).runtimeBinderSafeAt depth) = true
      rw [left.literal_runtimeBinderSafeAt, right.literal_runtimeBinderSafeAt]
      rfl

  theorem CodeListImage.literal_runtimeBinderSafeAt {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
      (literalEncodeTerm term).runtimeBinderSafeAt depth = true := by
    cases image with
    | nil => rfl
    | cons head tail =>
      change ((literalEncodeTerm _).runtimeBinderSafeAt depth &&
        (literalEncodeTerm _).runtimeBinderSafeAt depth) = true
      rw [head.literal_runtimeBinderSafeAt, tail.literal_runtimeBinderSafeAt]
      rfl
end

mutual
  theorem ConfigImage.literal_wellFormed {location : CostName LiteralAuthority}
      {source : Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigImage location source term)
      (locationValid : (literalEncodeName location).wellFormed = true) :
      (literalEncodeTerm term).wellFormed = true := by
    cases image with
    | zero => rfl
    | drop name => exact name.literal_wellFormed
    | signed signature accepted process =>
      exact (CodeImage.signed signature accepted process).literal_wellFormed
    | contact code stack =>
      change ((literalEncodeTerm _).wellFormed &&
        ((literalEncodeName location).wellFormed &&
          (literalEncodeStack _).all RawCostSig.valid)) = true
      rw [code.literal_wellFormed locationValid, locationValid, stack.literal_wellFormed]
      rfl
    | collection codes => exact codes.literal_wellFormed locationValid

  theorem ConfigListImage.literal_wellFormed {location : CostName LiteralAuthority}
      {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigListImage location sources term)
      (locationValid : (literalEncodeName location).wellFormed = true) :
      (literalEncodeTerm term).wellFormed = true := by
    cases image with
    | nil => rfl
    | cons head tail =>
      change ((literalEncodeTerm _).wellFormed && (literalEncodeTerm _).wellFormed) = true
      rw [head.literal_wellFormed locationValid, tail.literal_wellFormed locationValid]
      rfl
end

mutual
  theorem ConfigImage.literal_runtimeBinderSafeAt {location : CostName LiteralAuthority}
      {source : Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigImage location source term)
      (locationSafe : (literalEncodeName location).runtimeBinderSafeAt 0 = true) :
      (literalEncodeTerm term).runtimeBinderSafeAt 0 = true := by
    cases image with
    | zero => rfl
    | drop name => exact name.literal_runtimeBinderSafeAt
    | signed signature accepted process =>
      exact (CodeImage.signed signature accepted process).literal_runtimeBinderSafeAt
    | contact code stack =>
      change ((literalEncodeTerm _).runtimeBinderSafeAt 0 &&
        (literalEncodeName location).runtimeBinderSafeAt 0) = true
      rw [code.literal_runtimeBinderSafeAt locationSafe, locationSafe]
      rfl
    | collection codes => exact codes.literal_runtimeBinderSafeAt locationSafe

  theorem ConfigListImage.literal_runtimeBinderSafeAt {location : CostName LiteralAuthority}
      {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigListImage location sources term)
      (locationSafe : (literalEncodeName location).runtimeBinderSafeAt 0 = true) :
      (literalEncodeTerm term).runtimeBinderSafeAt 0 = true := by
    cases image with
    | nil => rfl
    | cons head tail =>
      change ((literalEncodeTerm _).runtimeBinderSafeAt 0 &&
        (literalEncodeTerm _).runtimeBinderSafeAt 0) = true
      rw [head.literal_runtimeBinderSafeAt locationSafe, tail.literal_runtimeBinderSafeAt locationSafe]
      rfl
end

/-- The encoding of a configuration image at the image of a closed channel is an input the
runtime accepts. -/
theorem ConfigImage.literal_supported {channelSource source : Pattern}
    {location : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term) :
    (literalEncodeTerm term).supported = true := by
  rw [RawCostTerm.supported, Bool.and_eq_true]
  exact ⟨image.literal_wellFormed channelImage.literal_wellFormed,
    image.literal_runtimeBinderSafeAt channelImage.literal_runtimeBinderSafeAt⟩

/-! ## From a complete runtime step to a path of one step -/

theorem stableKeySort_pair_orders {Alpha : Type} (key : Alpha → String) (left right : Alpha) :
    stableKeySort key [left, right] = [left, right] ∨
      stableKeySort key [left, right] = [right, left] := by
  simp only [stableKeySort, stableSortBy, List.foldl_cons, List.foldl_nil, stableInsertBy]
  split <;> simp

theorem initialTraceComponents_terms (source : RawCostTerm) :
    (initialTraceComponents source).map RawTraceComponent.term = source.normalizeConfig := by
  simp [initialTraceComponents, Function.comp_def]

theorem canonical_runtime_complete_path {source : RawCostTerm}
    (sourceValid : source.wellFormed = true) {location : CostName String}
    {spend : CostSig String} {target : CostConfig String}
    (complete : RuntimeCostStepComplete source.normalizeConfig location spend target) :
    ∃ step,
      step ∈ runtimeCostCandidatesFromConfig source.normalizeConfig ∧
      decodeCostName step.location = location ∧ decodeCostSig step.spend = spend ∧
      step.FrameExactFor source.normalizeConfig ∧
      (∃ path : CostPath 0 (initialTraceComponents source) 1
          (applyTracedStep (initialTraceComponents source) step 0), path.depth = 1) ∧
      rawConfigStructuralDenote ((applyTracedStep (initialTraceComponents source) step 0).map
        RawTraceComponent.term) = rawConfigStructuralDenote (encodeCostConfig target) := by
  obtain ⟨step, enabled, located, spent, residual, frame⟩ := complete
  have supported := initialTraceComponents_wellFormed sourceValid
  have bounded := initialTraceComponents_before source
  have tracedEnabled : step ∈ runtimeCostCandidatesFromConfig
      ((initialTraceComponents source).map RawTraceComponent.term) := by
    rw [initialTraceComponents_terms]
    exact enabled
  let path : CostPath 0 (initialTraceComponents source) 1
      (applyTracedStep (initialTraceComponents source) step 0) :=
    .fire supported bounded step tracedEnabled
      (.done (applyTracedStep_wellFormed supported tracedEnabled 0)
        (applyTracedStep_before bounded step))
  refine ⟨step, enabled, located, spent, frame, ⟨path, rfl⟩, ?_⟩
  have decoded := applyTracedStep_decode_normalizedResidual (initialTraceComponents_canonical source) tracedEnabled 0
  have observed := congrArg (fun config : CostConfig String =>
    rawConfigStructuralDenote (encodeCostConfig config)) decoded
  rw [rawConfigStructuralDenote_encode_decode, rawConfigStructuralDenote_encode_decode] at observed
  exact observed.trans residual

/-! ## The redex alone, whole funding -/

def locatedWholeEntryTerm (location : RawCostName) (body payload : RawCostTerm)
    (authority : String) (tail : RawCostStack) : RawCostTerm :=
  .par (.signed (.par (.recv location body) (.send location payload)) [authority])
    (.purse location ([authority] :: tail))

theorem locatedWholeEntry_authored_readout (location : CostName LiteralAuthority)
    (body payload : CostTerm LiteralAuthority) {signatureSource : Pattern}
    (signature : TypedSignature signatureSource) (tail : CostStack LiteralAuthority) :
    locatedWholeEntryTerm (literalEncodeName location) (literalEncodeTerm body)
      (literalEncodeTerm payload) (literalAuthorityKey signatureSource) (literalEncodeStack tail) =
      literalEncodeTerm (decodedReceiverSource location body payload signature.val tail) := by
  unfold locatedWholeEntryTerm literalEncodeTerm literalEncodeName decodedReceiverSource locatedContact
  simp only [CostTerm.relabel, CostProc.relabel, CostStack.relabel,
    encodeCostTerm, encodeCostProc, encodeCostStack]
  rw [signature.property.1, literalEncodeSig_singleton]
  rfl

theorem locatedWholeEntry_wellFormed
    {location : RawCostName} {body payload : RawCostTerm} {authority : String} {tail : RawCostStack}
    (locationValid : location.wellFormed = true)
    (bodyValid : body.wellFormed = true) (payloadValid : payload.wellFormed = true)
    (tailValid : tail.all RawCostSig.valid = true) :
    (locatedWholeEntryTerm location body payload authority tail).wellFormed = true := by
  simp [locatedWholeEntryTerm, RawCostTerm.wellFormed, RawCostProc.wellFormed,
    RawCostSig.valid, locationValid, bodyValid, payloadValid, tailValid]

theorem locatedWholeEntry_runtimeScope
    {location : RawCostName} {body payload : RawCostTerm} {authority : String} {tail : RawCostStack}
    (locationSafe : location.runtimeBinderSafeAt 0 = true)
    (bodySafe : body.runtimeBinderSafeAt 1 = true)
    (payloadSafe : payload.runtimeBinderSafeAt 0 = true) :
    (locatedWholeEntryTerm location body payload authority tail).runtimeBinderSafe = true := by
  simp [locatedWholeEntryTerm, RawCostTerm.runtimeBinderSafe, RawCostTerm.runtimeBinderSafeAt,
    RawCostProc.runtimeBinderSafeAt, locationSafe, bodySafe, payloadSafe]

def locatedCanonicalWholeTarget (location : RawCostName) (body payload : RawCostTerm)
    (tail : RawCostStack) : CostConfig String :=
  decodeRawConfig ((body.normalize.commSubst payload.normalize).components ++
    [.purse location.normalize (tail.map RawCostSig.normalize)])

theorem locatedCanonicalWholeTarget_readout (location : RawCostName) (body payload : RawCostTerm)
    (tail : RawCostStack) :
    rawConfigStructuralDenote (encodeCostConfig (locatedCanonicalWholeTarget location body payload tail)) =
      RawTermStructuralDenotation.combine
        (body.normalize.commSubst payload.normalize).structuralDenote
        (RawCostTerm.purse location tail).structuralDenote := by
  unfold locatedCanonicalWholeTarget
  rw [rawConfigStructuralDenote_encode_decode]
  rw [← Multiset.coe_add, rawConfigStructuralDenote_add,
    rawConfigStructuralDenote_components]
  rw [Multiset.coe_singleton, rawConfigStructuralDenote_singleton]
  simp only [RawCostTerm.structuralDenote, RawCostName.structuralDenote_normalize,
    RawCostStack.structuralFrames_map_normalize]

theorem locatedWholeEntry_normalized_pair (location : RawCostName) (body payload : RawCostTerm) :
    (RawCostProc.par (.recv location body) (.send location payload)).normalize =
      .par (.recv location.normalize body.normalize) (.send location.normalize payload.normalize) ∨
    (RawCostProc.par (.recv location body) (.send location payload)).normalize =
      .par (.send location.normalize payload.normalize) (.recv location.normalize body.normalize) := by
  have orders := stableKeySort_pair_orders RawCostProc.key
    (.recv location.normalize body.normalize) (.send location.normalize payload.normalize)
  simp only [RawCostProc.normalize, RawCostProc.components] at orders ⊢
  rcases orders with first | second
  · exact Or.inl (congrArg RawCostProc.fromComponents first)
  · exact Or.inr (congrArg RawCostProc.fromComponents second)

theorem locatedWholeEntry_canonical_declarative (location : RawCostName)
    (body payload : RawCostTerm) (authority : String) (tail : RawCostStack) :
    CostStep (decodeRawConfig (locatedWholeEntryTerm location body payload authority tail).normalizeConfig)
      (decodeCostName location.normalize) {authority}
      (locatedCanonicalWholeTarget location body payload tail) := by
  unfold locatedWholeEntryTerm
  rw [raw_normalConfig_par, raw_normalConfig_components, raw_normalConfig_components]
  have positive : ({authority} : CostSig String).RuntimeValid := by simp [CostSig.RuntimeValid]
  unfold locatedCanonicalWholeTarget
  rw [decodeRawConfig_append, decodeRawConfig_components, decodeCostTerm_commSubst]
  have cover := LocatedTokenCover.singleHead (decodeCostName location.normalize) {authority} positive
    (decodeCostStack (tail.map RawCostSig.normalize))
  rcases locatedWholeEntry_normalized_pair location body payload with first | second
  · simp only [RawCostTerm.normalize, first]
    simpa [decodeCostTerm, decodeCostProc, decodeCostSig, RawCostSig.normalize,
      stableSortBy, stableInsertBy, decodeCostStack, CostTerm.components,
      LocatedPurse.configComponents, LocatedPurse.toTerm, decodeRawConfig] using
      CostStep.wholeRecvSend (context := 0) (body := decodeCostTerm body.normalize)
        (payload := decodeCostTerm payload.normalize) positive cover
  · simp only [RawCostTerm.normalize, second]
    simpa [decodeCostTerm, decodeCostProc, decodeCostSig, RawCostSig.normalize,
      stableSortBy, stableInsertBy, decodeCostStack, CostTerm.components,
      LocatedPurse.configComponents, LocatedPurse.toTerm, decodeRawConfig] using
      CostStep.wholeSendRecv (context := 0) (body := decodeCostTerm body.normalize)
        (payload := decodeCostTerm payload.normalize) positive cover

theorem locatedWholeEntry_canonical_runtime
    {location : RawCostName} {body payload : RawCostTerm} {authority : String} {tail : RawCostStack}
    (locationValid : location.wellFormed = true)
    (bodyValid : body.wellFormed = true) (payloadValid : payload.wellFormed = true)
    (tailValid : tail.all RawCostSig.valid = true) :
    RuntimeCostStepComplete (locatedWholeEntryTerm location body payload authority tail).normalizeConfig
      (decodeCostName location.normalize) {authority}
      (locatedCanonicalWholeTarget location body payload tail) :=
  runtimeCostCandidates_complete_up_to_struct
    (locatedWholeEntry_wellFormed locationValid bodyValid payloadValid tailValid)
    (locatedWholeEntry_canonical_declarative location body payload authority tail)

/-! ## The redex alone, split funding -/

def decodedSplitReceiver (location : CostName LiteralAuthority)
    (body payload : CostTerm LiteralAuthority) (recvSignature sendSignature : CostSig LiteralAuthority)
    (recvTail sendTail : CostStack LiteralAuthority) : CostTerm LiteralAuthority :=
  .par (locatedContact location (.signed (.recv location body) recvSignature) (.cons recvSignature recvTail))
    (.par (locatedContact location (.signed (.send location payload) sendSignature)
      (.cons sendSignature sendTail)) .nil)

def locatedSplitEntryTerm (location : RawCostName) (body payload : RawCostTerm)
    (recvAuthority sendAuthority : String) (recvTail sendTail : RawCostStack) : RawCostTerm :=
  .par (.par (.signed (.recv location body) [recvAuthority]) (.purse location ([recvAuthority] :: recvTail)))
    (.par (.par (.signed (.send location payload) [sendAuthority])
      (.purse location ([sendAuthority] :: sendTail))) .nil)

theorem locatedSplitEntry_authored_readout (location : CostName LiteralAuthority)
    (body payload : CostTerm LiteralAuthority) {recvSignatureSource sendSignatureSource : Pattern}
    (recvSignature : TypedSignature recvSignatureSource) (sendSignature : TypedSignature sendSignatureSource)
    (recvTail sendTail : CostStack LiteralAuthority) :
    locatedSplitEntryTerm (literalEncodeName location) (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey recvSignatureSource) (literalAuthorityKey sendSignatureSource)
      (literalEncodeStack recvTail) (literalEncodeStack sendTail) =
      literalEncodeTerm (decodedSplitReceiver location body payload recvSignature.val sendSignature.val recvTail sendTail) := by
  unfold locatedSplitEntryTerm literalEncodeTerm decodedSplitReceiver locatedContact
  simp only [CostTerm.relabel, CostProc.relabel, CostStack.relabel, encodeCostTerm, encodeCostProc, encodeCostStack]
  rw [recvSignature.property.1, sendSignature.property.1, literalEncodeSig_singleton, literalEncodeSig_singleton]
  rfl

def locatedSplitCanonicalTarget (location : RawCostName) (body payload : RawCostTerm)
    (recvTail sendTail : RawCostStack) : CostConfig String :=
  decodeRawConfig (RawCostTerm.par (.par .nil (.purse location sendTail)) .nil).normalizeConfig +
    locatedCanonicalWholeTarget location body payload recvTail

theorem locatedSplitEntry_canonical_declarative (location : RawCostName) (body payload : RawCostTerm)
    (recvAuthority sendAuthority : String) (recvTail sendTail : RawCostStack) :
    CostStep (decodeRawConfig (locatedSplitEntryTerm location body payload recvAuthority sendAuthority recvTail sendTail).normalizeConfig)
      (decodeCostName location.normalize) ({recvAuthority} + {sendAuthority})
      (locatedSplitCanonicalTarget location body payload recvTail sendTail) := by
  have recvPositive : ({recvAuthority} : CostSig String).RuntimeValid := Multiset.singleton_ne_zero _
  have sendPositive : ({sendAuthority} : CostSig String).RuntimeValid := Multiset.singleton_ne_zero _
  have cover := (LocatedTokenCover.singleHead (decodeCostName location.normalize) {recvAuthority} recvPositive
      (decodeCostStack (recvTail.map RawCostSig.normalize))).combine
    (LocatedTokenCover.singleHead (decodeCostName location.normalize) {sendAuthority} sendPositive
      (decodeCostStack (sendTail.map RawCostSig.normalize)))
  have fired := CostStep.split (context := 0) (body := decodeCostTerm body.normalize)
    (payload := decodeCostTerm payload.normalize) recvPositive sendPositive cover
  unfold locatedSplitEntryTerm locatedSplitCanonicalTarget locatedCanonicalWholeTarget
  rw [raw_normalConfig_par, raw_normalConfig_par, raw_normalConfig_par, raw_normalConfig_nil,
    add_zero, raw_normalConfig_par, raw_normalConfig_components, raw_normalConfig_components,
    raw_normalConfig_components, raw_normalConfig_components]
  rw [raw_normalConfig_par, raw_normalConfig_par, raw_normalConfig_nil,
    zero_add, add_zero, raw_normalConfig_components, decodeRawConfig_append,
    decodeRawConfig_components, decodeCostTerm_commSubst]
  simpa [decodeCostTerm, decodeCostProc, decodeCostSig, RawCostTerm.normalize, RawCostProc.normalize,
    RawCostSig.normalize, stableSortBy, stableInsertBy, decodeCostStack, CostTerm.components,
    LocatedPurse.configComponents, LocatedPurse.toTerm, decodeRawConfig, ← Multiset.singleton_add,
    add_assoc, add_comm, add_left_comm] using fired

theorem locatedSplitEntry_canonical_runtime
    {location : RawCostName} {body payload : RawCostTerm} {recvAuthority sendAuthority : String}
    {recvTail sendTail : RawCostStack}
    (locationValid : location.wellFormed = true)
    (bodyValid : body.wellFormed = true) (payloadValid : payload.wellFormed = true)
    (recvTailValid : recvTail.all RawCostSig.valid = true) (sendTailValid : sendTail.all RawCostSig.valid = true) :
    RuntimeCostStepComplete
      (locatedSplitEntryTerm location body payload recvAuthority sendAuthority recvTail sendTail).normalizeConfig
      (decodeCostName location.normalize) ({recvAuthority} + {sendAuthority})
      (locatedSplitCanonicalTarget location body payload recvTail sendTail) := by
  have sourceValid :
      (locatedSplitEntryTerm location body payload recvAuthority sendAuthority recvTail sendTail).wellFormed = true := by
    simp [locatedSplitEntryTerm, RawCostTerm.wellFormed, RawCostProc.wellFormed,
      RawCostSig.valid, locationValid, bodyValid, payloadValid, recvTailValid, sendTailValid]
  exact runtimeCostCandidates_complete_up_to_struct sourceValid
    (locatedSplitEntry_canonical_declarative location body payload recvAuthority sendAuthority recvTail sendTail)

/-! ## The canonical configuration and its observation depend only on the bag -/

/-- The decoded canonical configuration of a term is a function of its bag of components. -/
theorem decodeRawConfig_normalizeConfig_literal : ∀ term : CostTerm LiteralAuthority,
    decodeRawConfig (literalEncodeTerm term).normalizeConfig =
      term.components.bind fun component =>
        decodeRawConfig (literalEncodeTerm component).normalizeConfig
  | .nil => by simp [CostTerm.components, literalEncodeTerm, CostTerm.relabel, encodeCostTerm,
      decodeRawConfig]
  | .par left right => by
      change decodeRawConfig (RawCostTerm.par (literalEncodeTerm left)
        (literalEncodeTerm right)).normalizeConfig = _
      rw [raw_normalConfig_par, decodeRawConfig_normalizeConfig_literal left,
        decodeRawConfig_normalizeConfig_literal right]
      simp [CostTerm.components, Multiset.add_bind]
  | .signed process signature => by simp [CostTerm.components]
  | .drop name => by simp [CostTerm.components]
  | .purse location stack => by simp [CostTerm.components]

/-- What the runtime observes of a term is a function of its bag of components. -/
theorem structuralDenote_literal : ∀ term : CostTerm LiteralAuthority,
    (literalEncodeTerm term).structuralDenote =
      rawConfigStructuralDenote (term.components.map literalEncodeTerm)
  | .nil => rfl
  | .par left right => by
      change RawTermStructuralDenotation.combine (literalEncodeTerm left).structuralDenote
        (literalEncodeTerm right).structuralDenote = _
      rw [structuralDenote_literal left, structuralDenote_literal right]
      simp [CostTerm.components, rawConfigStructuralDenote_add]
  | .signed process signature => by
      simp [CostTerm.components, rawConfigStructuralDenote_singleton]
  | .drop name => by simp [CostTerm.components, rawConfigStructuralDenote_singleton]
  | .purse location stack => by simp [CostTerm.components, rawConfigStructuralDenote_singleton]

theorem encodeCostConfig_add (left right : CostConfig String) :
    encodeCostConfig (left + right) = encodeCostConfig left + encodeCostConfig right := by
  simp [encodeCostConfig]

/-- A bag of components, each brought to its canonical configuration, is observed as the bag. -/
theorem rawConfigStructuralDenote_normal_bag (bag : CostConfig LiteralAuthority) :
    rawConfigStructuralDenote (encodeCostConfig (bag.bind fun component =>
      decodeRawConfig (literalEncodeTerm component).normalizeConfig)) =
      rawConfigStructuralDenote (bag.map literalEncodeTerm) := by
  induction bag using Multiset.induction_on with
  | empty => rfl
  | cons component bag ih =>
    rw [Multiset.cons_bind, encodeCostConfig_add, rawConfigStructuralDenote_add, ih,
      rawConfigStructuralDenote_encode_decode, rawConfigStructuralDenote_normalizeConfig,
      Multiset.map_cons, ← Multiset.singleton_add, rawConfigStructuralDenote_add,
      rawConfigStructuralDenote_singleton]

/-- What the runtime observes after a communication on the encodings of images is what it
observes of the image of the generated substitution. -/
theorem commSubst_observation {bodySource payloadSource : Pattern}
    {body payload result : CostTerm LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (same : (literalEncodeTerm (CostTerm.substitute payload 0 body)).normalize =
      (literalEncodeTerm result).normalize) :
    ((literalEncodeTerm body).normalize.commSubst (literalEncodeTerm payload).normalize).structuralDenote =
      (literalEncodeTerm result).structuralDenote := by
  have canonicalComm := RawCostTerm.commSubst_normalize_structural 1
    bodyImage.literal_runtimeBinderSafeAt payloadImage.literal_runtimeBinderSafeAt
  unfold RawCostTerm.StructurallyEquivalent at canonicalComm
  simp only [RawCostTerm.structuralDenote_normalize] at canonicalComm
  rw [canonicalComm]
  have literalComm : ((literalEncodeTerm body).commSubst (literalEncodeTerm payload)).normalize =
      (literalEncodeTerm result).normalize := by
    rw [← literalEncodeTerm_commSubst]
    exact same
  have commObservation := congrArg RawCostTerm.structuralDenote literalComm
  simp only [RawCostTerm.structuralDenote_normalize] at commObservation
  exact commObservation

/-- The canonical successor of a whole-funded redex is observed as the image of the generated
substitution beside the rest of the purse. -/
theorem locatedCanonicalWholeTarget_observation {bodySource payloadSource : Pattern}
    {body payload result : CostTerm LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (same : (literalEncodeTerm (CostTerm.substitute payload 0 body)).normalize =
      (literalEncodeTerm result).normalize)
    (location : CostName LiteralAuthority) (tail : CostStack LiteralAuthority) :
    rawConfigStructuralDenote (encodeCostConfig
      (locatedCanonicalWholeTarget (literalEncodeName location) (literalEncodeTerm body)
        (literalEncodeTerm payload) (literalEncodeStack tail))) =
      rawConfigStructuralDenote ((result.components + {CostTerm.purse location tail}).map literalEncodeTerm) := by
  rw [locatedCanonicalWholeTarget_readout, commSubst_observation bodyImage payloadImage same,
    structuralDenote_literal, Multiset.map_add, rawConfigStructuralDenote_add, Multiset.map_singleton,
    rawConfigStructuralDenote_singleton]
  rfl

/-! ## How a redex is paid for -/

/-- How a redex is paid for. `whole`: receive and send are signed together and one purse pays;
its head is that signature. `split`: they are signed separately and two purses pay, one head for
each signature. The stacks are what is left of the purses. -/
inductive Funding : Type where
  | whole {source : Pattern} (signature : TypedSignature source) (tail : CostStack LiteralAuthority)
  | split {recvSource sendSource : Pattern} (recvSignature : TypedSignature recvSource)
      (sendSignature : TypedSignature sendSource) (recvTail sendTail : CostStack LiteralAuthority)

/-- The redex with its purses, all at one channel. -/
def Funding.redex (location : CostName LiteralAuthority) (body payload : CostTerm LiteralAuthority) :
    Funding → CostTerm LiteralAuthority
  | .whole signature tail => decodedReceiverSource location body payload signature.val tail
  | .split recvSignature sendSignature recvTail sendTail =>
      decodedSplitReceiver location body payload recvSignature.val sendSignature.val recvTail sendTail

/-- What the firing spends: the key of each signature. -/
def Funding.spend : Funding → CostSig String
  | .whole (source := source) _ _ => {literalAuthorityKey source}
  | .split (recvSource := recv) (sendSource := send) _ _ _ _ =>
      {literalAuthorityKey recv} + {literalAuthorityKey send}

/-- What is at the place afterwards: the result of the communication and the rest of each purse. -/
def Funding.residue (location : CostName LiteralAuthority) (result : CostTerm LiteralAuthority) :
    Funding → CostConfig LiteralAuthority
  | .whole _ tail => result.components + {CostTerm.purse location tail}
  | .split _ _ recvTail sendTail =>
      result.components + {CostTerm.purse location recvTail} + {CostTerm.purse location sendTail}

/-- The canonical successor of the redex alone, as the declarative step computes it. -/
def Funding.canonicalTarget (location : CostName LiteralAuthority) (body payload : CostTerm LiteralAuthority) :
    Funding → CostConfig String
  | .whole _ tail =>
      locatedCanonicalWholeTarget (literalEncodeName location) (literalEncodeTerm body)
        (literalEncodeTerm payload) (literalEncodeStack tail)
  | .split _ _ recvTail sendTail =>
      locatedSplitCanonicalTarget (literalEncodeName location) (literalEncodeTerm body)
        (literalEncodeTerm payload) (literalEncodeStack recvTail) (literalEncodeStack sendTail)

/-- The redex alone steps declaratively at its channel, spending the keys of its signatures. -/
theorem Funding.redex_declarative (location : CostName LiteralAuthority)
    (body payload : CostTerm LiteralAuthority) : ∀ funding : Funding,
    CostStep (decodeRawConfig (literalEncodeTerm (funding.redex location body payload)).normalizeConfig)
      (decodeCostName (literalEncodeName location).normalize) funding.spend
      (funding.canonicalTarget location body payload)
  | .whole signature tail => by
      rw [Funding.redex, ← locatedWholeEntry_authored_readout]
      exact locatedWholeEntry_canonical_declarative _ _ _ _ _
  | .split recvSignature sendSignature recvTail sendTail => by
      rw [Funding.redex, ← locatedSplitEntry_authored_readout]
      exact locatedSplitEntry_canonical_declarative _ _ _ _ _ _ _

/-- The canonical successor of the redex alone is observed as its residue. -/
theorem Funding.canonicalTarget_observation {bodySource payloadSource : Pattern}
    {body payload result : CostTerm LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (same : (literalEncodeTerm (CostTerm.substitute payload 0 body)).normalize =
      (literalEncodeTerm result).normalize)
    (location : CostName LiteralAuthority) : ∀ funding : Funding,
    rawConfigStructuralDenote (encodeCostConfig (funding.canonicalTarget location body payload)) =
      rawConfigStructuralDenote ((funding.residue location result).map literalEncodeTerm)
  | .whole _ tail => locatedCanonicalWholeTarget_observation bodyImage payloadImage same location tail
  | .split _ _ recvTail sendTail => by
      rw [Funding.canonicalTarget, locatedSplitCanonicalTarget, encodeCostConfig_add,
        rawConfigStructuralDenote_add, locatedCanonicalWholeTarget_observation bodyImage payloadImage same,
        rawConfigStructuralDenote_encode_decode, rawConfigStructuralDenote_normalizeConfig, Funding.residue,
        Multiset.map_add _ _ {CostTerm.purse location sendTail}, rawConfigStructuralDenote_add]
      apply RawTermStructuralDenotation.ext <;>
        simp [RawCostTerm.structuralDenote, RawTermStructuralDenotation.combine,
          RawTermStructuralDenotation.empty, rawConfigStructuralDenote_singleton, literalEncodeTerm,
          literalEncodeName, literalEncodeStack, CostTerm.relabel, encodeCostTerm, add_comm]

/-! ## The right side of the generated rule -/

/-- The image of the right side of the generated rule at a channel: the result of the
substitution beside the rest of the purse. -/
theorem receiver_contractum_image {bodySource payloadSource tailSource : Pattern}
    {location : CostName LiteralAuthority} {result : CostTerm LiteralAuthority}
    {tail : CostStack LiteralAuthority}
    (resultImage : CodeImage 0 (substituteReflective wrappedRhoDeclaration 0
      (generatedReplacement payloadSource) bodySource) result)
    (tailImage : StackImage tailSource tail) :
    ConfigImage location (receiverContractum bodySource payloadSource tailSource)
      (locatedContact location (.par result .nil) tail) :=
  .contact (.collection (.cons (resultImage.toConfigImage location) .nil)) tailImage

theorem receiver_contractum_components (location : CostName LiteralAuthority)
    (result : CostTerm LiteralAuthority) (tail : CostStack LiteralAuthority) :
    (locatedContact location (.par result .nil) tail).components =
      result.components + {CostTerm.purse location tail} := by
  simp [locatedContact, CostTerm.components]

/-! ## A funded redex fires -/

/-- The runtime has the declarative step of a funded redex beside any frame, on the encoding of
any image whose bag is that redex and that frame. -/
theorem ConfigImage.funded_redex_runtime {channelSource source : Pattern}
    {location : CostName LiteralAuthority} {term body payload : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term)
    (funding : Funding) (frame : CostConfig LiteralAuthority)
    (place : term.components = (funding.redex location body payload).components + frame) :
    RuntimeCostStepComplete (literalEncodeTerm term).normalizeConfig
      (decodeCostName (literalEncodeName location).normalize) funding.spend
      ((frame.bind fun component => decodeRawConfig (literalEncodeTerm component).normalizeConfig) +
        funding.canonicalTarget location body payload) := by
  apply runtimeCostCandidates_complete_up_to_struct
    ((RawCostTerm.supported_iff _).mp (image.literal_supported channelImage)).1
  have framed := (funding.redex_declarative location body payload).add_frame
    (frame.bind fun component => decodeRawConfig (literalEncodeTerm component).normalizeConfig)
  rwa [decodeRawConfig_normalizeConfig_literal, add_comm, ← Multiset.add_bind, ← place,
    ← decodeRawConfig_normalizeConfig_literal] at framed

/-- A funded redex fires. Take any image of generated syntax at the image of a closed channel. If
its bag of components is a funded redex at that channel together with a frame, then the runtime,
started on it as it starts on anything, has a firing at that channel spending the keys of the
signatures; there is a path of one step; and what the runtime observes afterwards is the image of
the generated substitution, the rest of each purse, and the frame. -/
theorem ConfigImage.funded_redex_fires
    {channelSource source bodySource payloadSource : Pattern}
    {location : CostName LiteralAuthority} {term body payload : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (image : ConfigImage location source term)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (funding : Funding) (frame : CostConfig LiteralAuthority)
    (place : term.components = (funding.redex location body payload).components + frame) :
    ∃ result step,
      CodeImage 0 (substituteReflective wrappedRhoDeclaration 0
        (generatedReplacement payloadSource) bodySource) result ∧
      runtimeCostCandidates (literalEncodeTerm term) =
        some (runtimeCostCandidatesFromConfig (literalEncodeTerm term).normalizeConfig) ∧
      step ∈ runtimeCostCandidatesFromConfig (literalEncodeTerm term).normalizeConfig ∧
      decodeCostName step.location = decodeCostName (literalEncodeName location).normalize ∧
      decodeCostSig step.spend = funding.spend ∧
      step.FrameExactFor (literalEncodeTerm term).normalizeConfig ∧
      (∃ path : CostPath 0 (initialTraceComponents (literalEncodeTerm term)) 1
          (applyTracedStep (initialTraceComponents (literalEncodeTerm term)) step 0),
        path.depth = 1) ∧
      rawConfigStructuralDenote ((applyTracedStep (initialTraceComponents (literalEncodeTerm term))
          step 0).map RawTraceComponent.term) =
        rawConfigStructuralDenote ((funding.residue location result + frame).map literalEncodeTerm) := by
  obtain ⟨result, resultImage, same⟩ := bodyImage.substitute_raw_readout payloadImage
  have supported := image.literal_supported channelImage
  obtain ⟨step, enabled, located, spent, exact, path, observed⟩ :=
    canonical_runtime_complete_path ((RawCostTerm.supported_iff _).mp supported).1
      (image.funded_redex_runtime channelImage funding frame place)
  refine ⟨result, step, resultImage, by rw [runtimeCostCandidates, supported]; rfl,
    enabled, located, spent, exact, path, observed.trans ?_⟩
  rw [encodeCostConfig_add, rawConfigStructuralDenote_add, rawConfigStructuralDenote_normal_bag,
    funding.canonicalTarget_observation bodyImage payloadImage same location, Multiset.map_add,
    rawConfigStructuralDenote_add]
  apply RawTermStructuralDenotation.ext <;>
    simp [RawTermStructuralDenotation.combine, add_comm]

/-- `funded_redex_fires` with the readouts of the generated source and of a generated target whose
bag is the residue and the frame. -/
theorem ConfigImage.funded_redex_fires_readback
    {channelSource source bodySource payloadSource targetSource : Pattern}
    {location : CostName LiteralAuthority} {term body payload : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (image : ConfigImage location source term)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (funding : Funding) (frame : CostConfig LiteralAuthority)
    (place : term.components = (funding.redex location body payload).components + frame)
    (target : CostTerm LiteralAuthority → CostTerm LiteralAuthority)
    (targetImage : ∀ {result}, CodeImage 0 (substituteReflective wrappedRhoDeclaration 0
        (generatedReplacement payloadSource) bodySource) result →
      ConfigImage location targetSource (target result))
    (targetPlace : ∀ result, (target result).components = funding.residue location result + frame) :
    ∃ sourceFuel step targetTerm fuel,
      (config? location channelImage.purseInventory_zero channelImage.runtimeSupported sourceFuel
        source).map Subtype.val = some term ∧
      runtimeCostCandidates (literalEncodeTerm term) =
        some (runtimeCostCandidatesFromConfig (literalEncodeTerm term).normalizeConfig) ∧
      (config? location channelImage.purseInventory_zero channelImage.runtimeSupported fuel
        targetSource).map Subtype.val = some targetTerm ∧
      step ∈ runtimeCostCandidatesFromConfig (literalEncodeTerm term).normalizeConfig ∧
      decodeCostName step.location = decodeCostName (literalEncodeName location).normalize ∧
      decodeCostSig step.spend = funding.spend ∧
      step.FrameExactFor (literalEncodeTerm term).normalizeConfig ∧
      (∃ path : CostPath 0 (initialTraceComponents (literalEncodeTerm term)) 1
          (applyTracedStep (initialTraceComponents (literalEncodeTerm term)) step 0),
        path.depth = 1) ∧
      rawConfigStructuralDenote ((applyTracedStep (initialTraceComponents (literalEncodeTerm term))
          step 0).map RawTraceComponent.term) =
        rawConfigStructuralDenote (literalEncodeTerm targetTerm).normalizeConfig := by
  obtain ⟨result, step, resultImage, candidates, enabled, located, spent, exact, path, observed⟩ :=
    image.funded_redex_fires channelImage bodyImage payloadImage funding frame place
  obtain ⟨sourceFuel, sourceReadback⟩ :=
    image.parser_eventually channelImage.purseInventory_zero channelImage.runtimeSupported
  obtain ⟨fuel, readback⟩ :=
    (targetImage resultImage).parser_eventually channelImage.purseInventory_zero channelImage.runtimeSupported
  refine ⟨sourceFuel, step, target result, fuel, sourceReadback sourceFuel le_rfl, candidates,
    readback fuel le_rfl, enabled, located, spent, exact, path, observed.trans ?_⟩
  rw [rawConfigStructuralDenote_normalizeConfig, structuralDenote_literal, targetPlace]

end ActivationGenerated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
