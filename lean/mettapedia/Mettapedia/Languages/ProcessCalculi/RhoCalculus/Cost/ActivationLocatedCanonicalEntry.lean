import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedCanonicalEntry

/-!
# Actual canonical entry at admitted closed locations

The generated name parser determines both communication and funding location.
Canonical runtime entry normalizes that same location in both occurrences.
The exact signature remains one literal authority atom, and the successor is
compared with the parsed authored RHS through the full cost structural observer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem NameImage.purseInventory_zero {depth : Nat} {source : Pattern}
    {name : CostName LiteralAuthority} (image : NameImage depth source name) :
    name.purseInventory = 0 := by
  obtain ⟨fuel, readback⟩ := image.parser_eventually
  obtain ⟨decoded, _, same⟩ := Option.map_eq_some_iff.mp (readback fuel (le_refl fuel))
  exact same ▸ decoded.property.1

theorem NameImage.runtimeSupported {depth : Nat} {source : Pattern}
    {name : CostName LiteralAuthority} (image : NameImage depth source name) :
    name.RuntimeSupported := by
  obtain ⟨fuel, readback⟩ := image.parser_eventually
  obtain ⟨decoded, _, same⟩ := Option.map_eq_some_iff.mp (readback fuel (le_refl fuel))
  exact same ▸ decoded.property.2.2.1

theorem located_receiver_config_image
    {channelSource bodySource payloadSource signatureSource tailSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    {tail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (signature : TypedSignature signatureSource) (accepted : signature? signatureSource = some signature)
    (tailImage : StackImage tailSource tail) :
    ConfigImage location (receiverSource channelSource bodySource payloadSource signatureSource tailSource)
      (decodedReceiverSource location body payload signature.val tail) :=
  .contact (.signed signature accepted
    (.pair (.recv channelImage bodyImage) (.send channelImage payloadImage)))
    (.cons signature accepted tailImage)

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

theorem NameImage.located_canonical_entry_supported
    {channelSource bodySource payloadSource tailSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    {tail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) {signatureSource : Pattern}
    (signature : TypedSignature signatureSource) :
    (literalEncodeTerm (decodedReceiverSource location body payload signature.val tail)).supported = true := by
  rw [← locatedWholeEntry_authored_readout]
  rw [RawCostTerm.supported, Bool.and_eq_true]
  exact ⟨locatedWholeEntry_wellFormed channelImage.literal_wellFormed bodyImage.literal_wellFormed
      payloadImage.literal_wellFormed tailImage.literal_wellFormed,
    locatedWholeEntry_runtimeScope channelImage.literal_runtimeBinderSafeAt
      bodyImage.literal_runtimeBinderSafeAt payloadImage.literal_runtimeBinderSafeAt⟩

theorem NameImage.located_canonical_entry_runtime
    {channelSource bodySource payloadSource tailSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    {tail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) {signatureSource : Pattern}
    (signature : TypedSignature signatureSource) :
    RuntimeCostStepComplete
      (literalEncodeTerm (decodedReceiverSource location body payload signature.val tail)).normalizeConfig
      (decodeCostName (literalEncodeName location).normalize) {literalAuthorityKey signatureSource}
      (locatedCanonicalWholeTarget (literalEncodeName location) (literalEncodeTerm body)
        (literalEncodeTerm payload) (literalEncodeStack tail)) := by
  rw [← locatedWholeEntry_authored_readout]
  exact locatedWholeEntry_canonical_runtime channelImage.literal_wellFormed bodyImage.literal_wellFormed
    payloadImage.literal_wellFormed tailImage.literal_wellFormed

theorem NameImage.located_canonical_target_observation
    {channelSource bodySource payloadSource tailSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    {tail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) :
    ∃ target fuel,
      (config? location channelImage.purseInventory_zero channelImage.runtimeSupported fuel
        (receiverContractum bodySource payloadSource tailSource)).map Subtype.val = some target ∧
      rawConfigStructuralDenote (encodeCostConfig
        (locatedCanonicalWholeTarget (literalEncodeName location) (literalEncodeTerm body)
          (literalEncodeTerm payload) (literalEncodeStack tail))) =
        rawConfigStructuralDenote (literalEncodeTerm target).normalizeConfig := by
  obtain ⟨result, resultImage, same⟩ := bodyImage.substitute_raw_readout payloadImage
  let target := locatedContact location (.par result .nil) tail
  have targetImage : ConfigImage location
      (receiverContractum bodySource payloadSource tailSource) target :=
    .contact (.collection (.cons (resultImage.toConfigImage location) .nil)) tailImage
  obtain ⟨fuel, readback⟩ := targetImage.parser_eventually
    channelImage.purseInventory_zero channelImage.runtimeSupported
  refine ⟨target, fuel, readback fuel (le_refl fuel), ?_⟩
  rw [locatedCanonicalWholeTarget_readout, rawConfigStructuralDenote_normalizeConfig]
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
    (.purse (literalEncodeName location) (literalEncodeStack tail))).structuralDenote
  apply RawTermStructuralDenotation.ext <;>
    simp [RawCostTerm.structuralDenote, RawTermStructuralDenotation.combine,
      RawTermStructuralDenotation.empty]

/-- Actual parser readbacks, canonical public catalogue, occurrence path and full RHS observation. -/
theorem NameImage.located_canonical_entry_path_rhs
    {channelSource bodySource payloadSource signatureSource tailSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    {tail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (signature : TypedSignature signatureSource) (accepted : signature? signatureSource = some signature)
    (tailImage : StackImage tailSource tail) :
    ∃ sourceFuel step target fuel,
      (config? location channelImage.purseInventory_zero channelImage.runtimeSupported sourceFuel
        (receiverSource channelSource bodySource payloadSource signatureSource tailSource)).map Subtype.val =
          some (decodedReceiverSource location body payload signature.val tail) ∧
      runtimeCostCandidates (literalEncodeTerm (decodedReceiverSource location body payload signature.val tail)) =
        some (runtimeCostCandidatesFromConfig
          (literalEncodeTerm (decodedReceiverSource location body payload signature.val tail)).normalizeConfig) ∧
      (config? location channelImage.purseInventory_zero channelImage.runtimeSupported fuel
        (receiverContractum bodySource payloadSource tailSource)).map Subtype.val = some target ∧
      step ∈ runtimeCostCandidatesFromConfig
        (literalEncodeTerm (decodedReceiverSource location body payload signature.val tail)).normalizeConfig ∧
      decodeCostName step.location = decodeCostName (literalEncodeName location).normalize ∧
      decodeCostSig step.spend = {literalAuthorityKey signatureSource} ∧
      step.FrameExactFor
        (literalEncodeTerm (decodedReceiverSource location body payload signature.val tail)).normalizeConfig ∧
      (∃ path : CostPath 0
          (initialTraceComponents (literalEncodeTerm (decodedReceiverSource location body payload signature.val tail)))
          1 (applyTracedStep
            (initialTraceComponents (literalEncodeTerm (decodedReceiverSource location body payload signature.val tail))) step 0),
        path.depth = 1) ∧
      rawConfigStructuralDenote ((applyTracedStep
        (initialTraceComponents (literalEncodeTerm (decodedReceiverSource location body payload signature.val tail))) step 0).map
          RawTraceComponent.term) = rawConfigStructuralDenote (literalEncodeTerm target).normalizeConfig := by
  obtain ⟨sourceFuel, sourceReadback⟩ :=
    (located_receiver_config_image channelImage bodyImage payloadImage signature accepted tailImage).parser_eventually
      channelImage.purseInventory_zero channelImage.runtimeSupported
  obtain ⟨target, fuel, parsed, targetObservation⟩ :=
    channelImage.located_canonical_target_observation bodyImage payloadImage tailImage
  let source := literalEncodeTerm (decodedReceiverSource location body payload signature.val tail)
  have sourceSupported : source.supported = true :=
    channelImage.located_canonical_entry_supported bodyImage payloadImage tailImage signature
  have publicCandidates : runtimeCostCandidates source =
      some (runtimeCostCandidatesFromConfig source.normalizeConfig) := by
    rw [runtimeCostCandidates, sourceSupported]
    rfl
  have sourceValid : source.wellFormed = true :=
    ((RawCostTerm.supported_iff source).mp sourceSupported).1
  obtain ⟨step, enabled, located, spent, frame, path, observed⟩ :=
    canonical_runtime_complete_path sourceValid
      (channelImage.located_canonical_entry_runtime bodyImage payloadImage tailImage signature)
  exact ⟨sourceFuel, step, target, fuel, sourceReadback sourceFuel (le_refl sourceFuel),
    publicCandidates, parsed, enabled, located, spent, frame, path, observed.trans targetObservation⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
