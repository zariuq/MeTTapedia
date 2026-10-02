import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationLocatedCanonicalEntry

/-!
# Canonical runtime entry in arbitrary admitted parallel frames

The frame is read by the existing generated configuration parser. Its complete
code, signing seals and located purses remain in the source and RHS observers.
The theorem preserves one selected funded firing; other candidates, including
same-location ambient borrowing, remain available to the original runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem encodeCostConfig_add (left right : CostConfig String) :
    encodeCostConfig (left + right) = encodeCostConfig left + encodeCostConfig right := by
  simp [encodeCostConfig]

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

theorem ConfigImage.literal_supported {channelSource source : Pattern}
    {location : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term) :
    (literalEncodeTerm term).supported = true := by
  rw [RawCostTerm.supported, Bool.and_eq_true]
  exact ⟨image.literal_wellFormed channelImage.literal_wellFormed,
    image.literal_runtimeBinderSafeAt channelImage.literal_runtimeBinderSafeAt⟩

theorem locatedWholeEntry_canonical_frame_runtime
    {location : RawCostName} {body payload ambient : RawCostTerm} {authority : String} {tail : RawCostStack}
    (locationValid : location.wellFormed = true)
    (bodyValid : body.wellFormed = true) (payloadValid : payload.wellFormed = true)
    (tailValid : tail.all RawCostSig.valid = true) (ambientValid : ambient.wellFormed = true) :
    RuntimeCostStepComplete
      (RawCostTerm.par (locatedWholeEntryTerm location body payload authority tail) ambient).normalizeConfig
      (decodeCostName location.normalize) {authority}
      (decodeRawConfig ambient.normalizeConfig + locatedCanonicalWholeTarget location body payload tail) := by
  have sourceValid :
      (RawCostTerm.par (locatedWholeEntryTerm location body payload authority tail) ambient).wellFormed = true := by
    change ((locatedWholeEntryTerm location body payload authority tail).wellFormed && ambient.wellFormed) = true
    rw [locatedWholeEntry_wellFormed locationValid bodyValid payloadValid tailValid, ambientValid]
    rfl
  apply runtimeCostCandidates_complete_up_to_struct sourceValid
  rw [raw_normalConfig_par, add_comm]
  exact (locatedWholeEntry_canonical_declarative location body payload authority tail).add_frame
    (decodeRawConfig ambient.normalizeConfig)

def ambientReceiverSource (channel body payload signature tail ambient : Pattern) : Pattern :=
  .collection .hashBag [receiverSource channel body payload signature tail, ambient] none

def ambientReceiverContractum (body payload tail ambient : Pattern) : Pattern :=
  .collection .hashBag [receiverContractum body payload tail, ambient] none

def decodedAmbientReceiver (location : CostName LiteralAuthority)
    (body payload : CostTerm LiteralAuthority) (signature : CostSig LiteralAuthority)
    (tail : CostStack LiteralAuthority) (ambient : CostTerm LiteralAuthority) : CostTerm LiteralAuthority :=
  .par (decodedReceiverSource location body payload signature tail) (.par ambient .nil)

theorem ambient_receiver_config_image
    {channelSource bodySource payloadSource signatureSource tailSource ambientSource : Pattern}
    {location : CostName LiteralAuthority} {body payload ambient : CostTerm LiteralAuthority}
    {tail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (signature : TypedSignature signatureSource) (accepted : signature? signatureSource = some signature)
    (tailImage : StackImage tailSource tail) (ambientImage : ConfigImage location ambientSource ambient) :
    ConfigImage location
      (ambientReceiverSource channelSource bodySource payloadSource signatureSource tailSource ambientSource)
      (decodedAmbientReceiver location body payload signature.val tail ambient) :=
  .collection (.cons (located_receiver_config_image channelImage bodyImage payloadImage signature accepted tailImage)
    (.cons ambientImage .nil))

theorem NameImage.ambient_canonical_target_observation
    {channelSource bodySource payloadSource tailSource ambientSource : Pattern}
    {location : CostName LiteralAuthority} {body payload ambient : CostTerm LiteralAuthority}
    {tail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) (ambientImage : ConfigImage location ambientSource ambient) :
    ∃ target fuel,
      (config? location channelImage.purseInventory_zero channelImage.runtimeSupported fuel
        (ambientReceiverContractum bodySource payloadSource tailSource ambientSource)).map Subtype.val = some target ∧
      rawConfigStructuralDenote (encodeCostConfig
        (decodeRawConfig (literalEncodeTerm (.par ambient .nil)).normalizeConfig +
          locatedCanonicalWholeTarget (literalEncodeName location) (literalEncodeTerm body)
            (literalEncodeTerm payload) (literalEncodeStack tail))) =
        rawConfigStructuralDenote (literalEncodeTerm target).normalizeConfig := by
  obtain ⟨core, coreFuel, coreParsed, coreObserved⟩ :=
    channelImage.located_canonical_target_observation bodyImage payloadImage tailImage
  have coreImage := config_parser_image coreParsed
  have targetImage : ConfigImage location
      (ambientReceiverContractum bodySource payloadSource tailSource ambientSource)
      (.par core (.par ambient .nil)) := .collection (.cons coreImage (.cons ambientImage .nil))
  obtain ⟨fuel, readback⟩ := targetImage.parser_eventually
    channelImage.purseInventory_zero channelImage.runtimeSupported
  refine ⟨.par core (.par ambient .nil), fuel, readback fuel (le_refl fuel), ?_⟩
  rw [encodeCostConfig_add, rawConfigStructuralDenote_add, rawConfigStructuralDenote_encode_decode,
    coreObserved]
  simp only [rawConfigStructuralDenote_normalizeConfig]
  change RawTermStructuralDenotation.combine
    (RawCostTerm.par (literalEncodeTerm ambient) .nil).structuralDenote
    (literalEncodeTerm core).structuralDenote =
    (RawCostTerm.par (literalEncodeTerm core)
      (RawCostTerm.par (literalEncodeTerm ambient) .nil)).structuralDenote
  apply RawTermStructuralDenotation.ext <;>
    simp [RawCostTerm.structuralDenote, RawTermStructuralDenotation.combine, add_comm]

/-- Every admitted ambient frame retains a selected actual canonical firing and its full RHS observation. -/
theorem NameImage.ambient_canonical_entry_path_rhs
    {channelSource bodySource payloadSource signatureSource tailSource ambientSource : Pattern}
    {location : CostName LiteralAuthority} {body payload ambient : CostTerm LiteralAuthority}
    {tail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (signature : TypedSignature signatureSource) (accepted : signature? signatureSource = some signature)
    (tailImage : StackImage tailSource tail) (ambientImage : ConfigImage location ambientSource ambient) :
    ∃ sourceFuel step target fuel,
      (config? location channelImage.purseInventory_zero channelImage.runtimeSupported sourceFuel
        (ambientReceiverSource channelSource bodySource payloadSource signatureSource tailSource ambientSource)).map
          Subtype.val = some (decodedAmbientReceiver location body payload signature.val tail ambient) ∧
      runtimeCostCandidates (literalEncodeTerm (decodedAmbientReceiver location body payload signature.val tail ambient)) =
        some (runtimeCostCandidatesFromConfig
          (literalEncodeTerm (decodedAmbientReceiver location body payload signature.val tail ambient)).normalizeConfig) ∧
      (config? location channelImage.purseInventory_zero channelImage.runtimeSupported fuel
        (ambientReceiverContractum bodySource payloadSource tailSource ambientSource)).map Subtype.val = some target ∧
      step ∈ runtimeCostCandidatesFromConfig
        (literalEncodeTerm (decodedAmbientReceiver location body payload signature.val tail ambient)).normalizeConfig ∧
      decodeCostName step.location = decodeCostName (literalEncodeName location).normalize ∧
      decodeCostSig step.spend = {literalAuthorityKey signatureSource} ∧
      step.FrameExactFor
        (literalEncodeTerm (decodedAmbientReceiver location body payload signature.val tail ambient)).normalizeConfig ∧
      (∃ path : CostPath 0
          (initialTraceComponents (literalEncodeTerm (decodedAmbientReceiver location body payload signature.val tail ambient)))
          1 (applyTracedStep
            (initialTraceComponents (literalEncodeTerm (decodedAmbientReceiver location body payload signature.val tail ambient))) step 0),
        path.depth = 1) ∧
      rawConfigStructuralDenote ((applyTracedStep
        (initialTraceComponents (literalEncodeTerm (decodedAmbientReceiver location body payload signature.val tail ambient))) step 0).map
          RawTraceComponent.term) = rawConfigStructuralDenote (literalEncodeTerm target).normalizeConfig := by
  have sourceImage := ambient_receiver_config_image channelImage bodyImage payloadImage signature accepted tailImage ambientImage
  obtain ⟨sourceFuel, sourceReadback⟩ := sourceImage.parser_eventually
    channelImage.purseInventory_zero channelImage.runtimeSupported
  obtain ⟨target, fuel, parsed, targetObservation⟩ :=
    channelImage.ambient_canonical_target_observation bodyImage payloadImage tailImage ambientImage
  let source := literalEncodeTerm (decodedAmbientReceiver location body payload signature.val tail ambient)
  have sourceSupported : source.supported = true := sourceImage.literal_supported channelImage
  have publicCandidates : runtimeCostCandidates source =
      some (runtimeCostCandidatesFromConfig source.normalizeConfig) := by
    rw [runtimeCostCandidates, sourceSupported]
    rfl
  have sourceValid : source.wellFormed = true :=
    ((RawCostTerm.supported_iff source).mp sourceSupported).1
  have ambientValid : (literalEncodeTerm (.par ambient .nil)).wellFormed = true := by
    change ((literalEncodeTerm ambient).wellFormed && true) = true
    rw [ambientImage.literal_wellFormed channelImage.literal_wellFormed]
    rfl
  have runtime := locatedWholeEntry_canonical_frame_runtime (authority := literalAuthorityKey signatureSource)
    channelImage.literal_wellFormed
    bodyImage.literal_wellFormed payloadImage.literal_wellFormed tailImage.literal_wellFormed ambientValid
  rw [locatedWholeEntry_authored_readout location body payload signature tail] at runtime
  change RuntimeCostStepComplete source.normalizeConfig _ _ _ at runtime
  obtain ⟨step, enabled, located, spent, frame, path, observed⟩ :=
    canonical_runtime_complete_path sourceValid runtime
  exact ⟨sourceFuel, step, target, fuel, sourceReadback sourceFuel (le_refl sourceFuel),
    publicCandidates, parsed, enabled, located, spent, frame, path, observed.trans targetObservation⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
