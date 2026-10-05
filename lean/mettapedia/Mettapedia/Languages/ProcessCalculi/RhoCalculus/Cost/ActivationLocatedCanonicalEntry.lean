import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedCanonicalEntry

/-!
# Canonical entry at admitted closed locations

The generated name readout determines both the communication and the funding location. The
firing of the isolated whole-funded contact at the image of a closed channel
(`NameImage.located_canonical_entry_path_rhs`) is `ConfigImage.funded_redex_fires_readback` with
whole funding and an empty frame; the raw lemmas it used are in `ActivationFundedRedex`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

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
  obtain ⟨fuel, readback⟩ := (receiver_contractum_image (location := location) resultImage
    tailImage).parser_eventually channelImage.purseInventory_zero channelImage.runtimeSupported
  refine ⟨_, fuel, readback fuel le_rfl, ?_⟩
  rw [rawConfigStructuralDenote_normalizeConfig, structuralDenote_literal, receiver_contractum_components]
  exact locatedCanonicalWholeTarget_observation bodyImage payloadImage same location tail

/-- Readouts of source and target, the public candidate list, a path of one step, and the
observation of the successor. -/
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
          RawTraceComponent.term) = rawConfigStructuralDenote (literalEncodeTerm target).normalizeConfig :=
  (located_receiver_config_image channelImage bodyImage payloadImage signature accepted tailImage).funded_redex_fires_readback
    channelImage bodyImage payloadImage (.whole signature tail) 0 (add_zero _).symm
    (fun result => locatedContact location (.par result .nil) tail)
    (fun resultImage => receiver_contractum_image resultImage tailImage)
    (fun result => (receiver_contractum_components location result tail).trans (add_zero _).symm)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
