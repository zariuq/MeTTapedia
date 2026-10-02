import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCanonicalSubstitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedOccurrenceRHS
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationRuntime

/-!
# Canonical runtime entry for the actual generated whole activation

The input is the existing decoded authored source. Its canonical component
configuration has a genuine whole CostStep, and the existing runtime
completeness theorem supplies an occurrence candidate and a nonempty CostPath.
The full cost structural observation relates that successor to the actual
parsed authored RHS. Literal raw endpoint equality is kept separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

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

theorem stableKeySort_pair_orders {Alpha : Type} (key : Alpha → String) (left right : Alpha) :
    stableKeySort key [left, right] = [left, right] ∨
      stableKeySort key [left, right] = [right, left] := by
  simp only [stableKeySort, stableSortBy, List.foldl_cons, List.foldl_nil, stableInsertBy]
  split <;> simp

def wholeEntryTerm (body payload : RawCostTerm) (authority : String) (tail : RawCostStack) :
    RawCostTerm := RawCostTerm.fromComponents (wholeOccurrenceConfig body payload authority tail)

theorem wholeEntry_authored_readout (body payload : CostTerm LiteralAuthority)
    {signatureSource : Pattern} (signature : TypedSignature signatureSource)
    (tail : CostStack LiteralAuthority) :
    wholeEntryTerm (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey signatureSource) (literalEncodeStack tail) =
      literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail) := by
  unfold wholeEntryTerm wholeOccurrenceConfig
  change RawCostTerm.par _ _ = _
  unfold literalEncodeTerm decodedReceiverSource locatedContact
  simp only [CostTerm.relabel, CostProc.relabel, CostStack.relabel,
    encodeCostTerm, encodeCostProc, encodeCostStack]
  rw [signature.property.1, literalEncodeSig_singleton]
  rfl

theorem wholeEntry_wellFormed {body payload : RawCostTerm} {authority : String} {tail : RawCostStack}
    (bodyValid : body.wellFormed = true) (payloadValid : payload.wellFormed = true)
    (tailValid : tail.all RawCostSig.valid = true) :
    (wholeEntryTerm body payload authority tail).wellFormed = true := by
  simp [wholeEntryTerm, wholeOccurrenceConfig, RawCostTerm.fromComponents,
    RawCostTerm.wellFormed, RawCostProc.wellFormed, occurrenceNilLocation,
    RawCostName.wellFormed, RawCostSig.valid, bodyValid, payloadValid, tailValid]

theorem wholeEntry_runtimeScope {body payload : RawCostTerm} {authority : String} {tail : RawCostStack}
    (bodySafe : body.runtimeBinderSafeAt 1 = true)
    (payloadSafe : payload.runtimeBinderSafeAt 0 = true) :
    (wholeEntryTerm body payload authority tail).runtimeBinderSafe = true := by
  simp [wholeEntryTerm, wholeOccurrenceConfig, RawCostTerm.fromComponents,
    RawCostTerm.runtimeBinderSafe, RawCostTerm.runtimeBinderSafeAt,
    RawCostProc.runtimeBinderSafeAt, occurrenceNilLocation,
    RawCostName.runtimeBinderSafeAt, bodySafe, payloadSafe]

def canonicalWholeTarget (body payload : RawCostTerm) (tail : RawCostStack) : CostConfig String :=
  decodeRawConfig ((body.normalize.commSubst payload.normalize).components ++
    [RawCostTerm.purse occurrenceNilLocation (tail.map RawCostSig.normalize)])

theorem canonicalWholeTarget_readout (body payload : RawCostTerm) (tail : RawCostStack) :
    rawConfigStructuralDenote (encodeCostConfig (canonicalWholeTarget body payload tail)) =
      RawTermStructuralDenotation.combine
        (body.normalize.commSubst payload.normalize).structuralDenote
        (RawCostTerm.purse occurrenceNilLocation tail).structuralDenote := by
  unfold canonicalWholeTarget
  rw [rawConfigStructuralDenote_encode_decode]
  rw [← Multiset.coe_add, rawConfigStructuralDenote_add,
    rawConfigStructuralDenote_components]
  rw [Multiset.coe_singleton, rawConfigStructuralDenote_singleton]
  simp only [RawCostTerm.structuralDenote, RawCostStack.structuralFrames_map_normalize]

theorem wholeEntry_normalized_pair (body payload : RawCostTerm) :
    (RawCostProc.par (.recv occurrenceNilLocation body) (.send occurrenceNilLocation payload)).normalize =
      .par (.recv occurrenceNilLocation body.normalize) (.send occurrenceNilLocation payload.normalize) ∨
    (RawCostProc.par (.recv occurrenceNilLocation body) (.send occurrenceNilLocation payload)).normalize =
      .par (.send occurrenceNilLocation payload.normalize) (.recv occurrenceNilLocation body.normalize) := by
  have orders := stableKeySort_pair_orders RawCostProc.key
    (.recv occurrenceNilLocation body.normalize) (.send occurrenceNilLocation payload.normalize)
  simp only [RawCostProc.normalize, RawCostProc.components, occurrenceNilLocation,
    RawCostName.normalize, RawCostTerm.normalize] at orders ⊢
  rcases orders with first | second
  · exact Or.inl (congrArg RawCostProc.fromComponents first)
  · exact Or.inr (congrArg RawCostProc.fromComponents second)

theorem wholeEntry_canonical_declarative (body payload : RawCostTerm) (authority : String)
    (tail : RawCostStack) :
    CostStep (decodeRawConfig (wholeEntryTerm body payload authority tail).normalizeConfig)
      (.quote .nil) {authority} (canonicalWholeTarget body payload tail) := by
  change CostStep (decodeRawConfig (RawCostTerm.par
    (.signed (.par (.recv occurrenceNilLocation body) (.send occurrenceNilLocation payload)) [authority])
    (.purse occurrenceNilLocation ([authority] :: tail))).normalizeConfig) _ _ _
  rw [raw_normalConfig_par, raw_normalConfig_components, raw_normalConfig_components]
  have positive : ({authority} : CostSig String).RuntimeValid := by simp [CostSig.RuntimeValid]
  unfold canonicalWholeTarget
  rw [decodeRawConfig_append, decodeRawConfig_components, decodeCostTerm_commSubst]
  have cover := LocatedTokenCover.singleHead (CostName.quote CostTerm.nil) {authority} positive
    (decodeCostStack (tail.map RawCostSig.normalize))
  rcases wholeEntry_normalized_pair body payload with first | second
  · simp only [RawCostTerm.normalize, first]
    simpa [decodeCostTerm, decodeCostProc, decodeCostName, decodeCostSig,
      RawCostSig.normalize, stableSortBy, stableInsertBy, occurrenceNilLocation,
      RawCostName.normalize, RawCostTerm.normalize, decodeCostStack, CostTerm.components,
      LocatedPurse.configComponents, LocatedPurse.toTerm, decodeRawConfig] using
      CostStep.wholeRecvSend (context := 0) (body := decodeCostTerm body.normalize)
        (payload := decodeCostTerm payload.normalize) positive cover
  · simp only [RawCostTerm.normalize, second]
    simpa [decodeCostTerm, decodeCostProc, decodeCostName, decodeCostSig,
      RawCostSig.normalize, stableSortBy, stableInsertBy, occurrenceNilLocation,
      RawCostName.normalize, RawCostTerm.normalize, decodeCostStack, CostTerm.components,
      LocatedPurse.configComponents, LocatedPurse.toTerm, decodeRawConfig] using
      CostStep.wholeSendRecv (context := 0) (body := decodeCostTerm body.normalize)
        (payload := decodeCostTerm payload.normalize) positive cover

theorem wholeEntry_canonical_runtime {body payload : RawCostTerm} {authority : String} {tail : RawCostStack}
    (bodyValid : body.wellFormed = true) (payloadValid : payload.wellFormed = true)
    (tailValid : tail.all RawCostSig.valid = true) :
    RuntimeCostStepComplete (wholeEntryTerm body payload authority tail).normalizeConfig
      (.quote .nil) {authority} (canonicalWholeTarget body payload tail) :=
  runtimeCostCandidates_complete_up_to_struct (wholeEntry_wellFormed bodyValid payloadValid tailValid)
    (wholeEntry_canonical_declarative body payload authority tail)

theorem CodeImage.canonical_entry_supported {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) {signatureSource : Pattern}
    (signature : TypedSignature signatureSource) :
    (literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail)).supported = true := by
  rw [← wholeEntry_authored_readout]
  rw [RawCostTerm.supported, Bool.and_eq_true]
  exact ⟨wholeEntry_wellFormed bodyImage.literal_wellFormed payloadImage.literal_wellFormed
      tailImage.literal_wellFormed,
    wholeEntry_runtimeScope bodyImage.literal_runtimeBinderSafeAt payloadImage.literal_runtimeBinderSafeAt⟩

theorem CodeImage.canonical_entry_runtime {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) {signatureSource : Pattern}
    (signature : TypedSignature signatureSource) :
    RuntimeCostStepComplete
      (literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail)).normalizeConfig
      (.quote .nil) {literalAuthorityKey signatureSource}
      (canonicalWholeTarget (literalEncodeTerm body) (literalEncodeTerm payload) (literalEncodeStack tail)) := by
  rw [← wholeEntry_authored_readout]
  exact wholeEntry_canonical_runtime bodyImage.literal_wellFormed payloadImage.literal_wellFormed
    tailImage.literal_wellFormed

theorem CodeImage.canonical_entry_target_observation {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) :
    ∃ target fuel,
      (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported fuel
        (receiverContractum bodySource payloadSource tailSource)).map Subtype.val = some target ∧
      rawConfigStructuralDenote (encodeCostConfig
        (canonicalWholeTarget (literalEncodeTerm body) (literalEncodeTerm payload) (literalEncodeStack tail))) =
          rawConfigStructuralDenote (literalEncodeTerm target).normalizeConfig := by
  obtain ⟨result, resultImage, same⟩ := bodyImage.substitute_raw_readout payloadImage
  let target := locatedContact nilChannelLocation (.par result .nil) tail
  have targetImage : ConfigImage nilChannelLocation
      (receiverContractum bodySource payloadSource tailSource) target :=
    .contact (.collection (.cons (resultImage.toConfigImage nilChannelLocation) .nil)) tailImage
  obtain ⟨fuel, readback⟩ := targetImage.parser_eventually nilChannelLocation_free nilChannelLocation_supported
  refine ⟨target, fuel, readback fuel (le_refl fuel), ?_⟩
  rw [canonicalWholeTarget_readout, rawConfigStructuralDenote_normalizeConfig]
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
  rw [commObservation]
  change _ = (RawCostTerm.par (RawCostTerm.par (literalEncodeTerm result) .nil)
    (.purse occurrenceNilLocation (literalEncodeStack tail))).structuralDenote
  apply RawTermStructuralDenotation.ext <;>
    simp [RawCostTerm.structuralDenote, RawTermStructuralDenotation.combine,
      RawTermStructuralDenotation.empty]

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

theorem CodeImage.canonical_entry_path_rhs {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) {signatureSource : Pattern}
    (signature : TypedSignature signatureSource) (accepted : signature? signatureSource = some signature) :
    ∃ sourceFuel step target fuel,
      (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported sourceFuel
        (receiverSource nilChannelSource bodySource payloadSource signatureSource tailSource)).map Subtype.val =
          some (decodedReceiverSource nilChannelLocation body payload signature.val tail) ∧
      runtimeCostCandidates (literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail)) =
        some (runtimeCostCandidatesFromConfig
          (literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail)).normalizeConfig) ∧
      (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported fuel
        (receiverContractum bodySource payloadSource tailSource)).map Subtype.val = some target ∧
      step ∈ runtimeCostCandidatesFromConfig
        (literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail)).normalizeConfig ∧
      decodeCostName step.location = .quote .nil ∧
      decodeCostSig step.spend = {literalAuthorityKey signatureSource} ∧
      step.FrameExactFor
        (literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail)).normalizeConfig ∧
      (∃ path : CostPath 0
          (initialTraceComponents (literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail)))
          1 (applyTracedStep
            (initialTraceComponents (literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail))) step 0),
        path.depth = 1) ∧
      rawConfigStructuralDenote ((applyTracedStep
        (initialTraceComponents (literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail))) step 0).map
          RawTraceComponent.term) = rawConfigStructuralDenote (literalEncodeTerm target).normalizeConfig := by
  obtain ⟨sourceFuel, sourceReadback⟩ :=
    (receiver_config_structural_image bodyImage payloadImage signature accepted tailImage).parser_eventually
      nilChannelLocation_free nilChannelLocation_supported
  obtain ⟨target, fuel, parsed, targetObservation⟩ :=
    bodyImage.canonical_entry_target_observation payloadImage tailImage
  let source := literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail)
  have sourceSupported : source.supported = true :=
    bodyImage.canonical_entry_supported payloadImage tailImage signature
  have publicCandidates : runtimeCostCandidates source =
      some (runtimeCostCandidatesFromConfig source.normalizeConfig) := by
    rw [runtimeCostCandidates, sourceSupported]
    rfl
  have sourceValid : source.wellFormed = true :=
    ((RawCostTerm.supported_iff source).mp sourceSupported).1
  obtain ⟨step, enabled, location, spend, frame, path, observed⟩ :=
    canonical_runtime_complete_path sourceValid
      (bodyImage.canonical_entry_runtime payloadImage tailImage signature)
  exact ⟨sourceFuel, step, target, fuel, sourceReadback sourceFuel (le_refl sourceFuel),
    publicCandidates, parsed, enabled, location, spend, frame, path, observed.trans targetObservation⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
