import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationLocatedCanonicalEntry

/-!
# Canonical runtime entry in arbitrary admitted parallel frames

A whole-funded contact beside any admitted configuration. The frame keeps its code, seals and
located purses in the source and in the successor. The firing
(`NameImage.ambient_canonical_entry_path_rhs`) is `ConfigImage.funded_redex_fires_readback` with
whole funding and the frame's bag; other candidates, including borrowing from a purse of the
frame at the same location, remain available to the runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

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

/-- Beside any admitted frame, the contact fires, and the successor is observed as the image of
the generated right side beside the frame. -/
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
          RawTraceComponent.term) = rawConfigStructuralDenote (literalEncodeTerm target).normalizeConfig :=
  (ambient_receiver_config_image channelImage bodyImage payloadImage signature accepted tailImage
    ambientImage).funded_redex_fires_readback channelImage bodyImage payloadImage (.whole signature tail)
    ambient.components (by simp [decodedAmbientReceiver, CostTerm.components, Funding.redex])
    (fun result => .par (locatedContact location (.par result .nil) tail) (.par ambient .nil))
    (fun resultImage => .collection (.cons (receiver_contractum_image resultImage tailImage)
      (.cons ambientImage .nil)))
    (fun result => by
      simp [CostTerm.components, receiver_contractum_components, Funding.residue])

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
