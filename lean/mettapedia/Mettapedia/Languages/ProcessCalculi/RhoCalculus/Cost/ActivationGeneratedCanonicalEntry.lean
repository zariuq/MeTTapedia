import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationFundedRedex

/-!
# Canonical runtime entry for the generated whole activation at the nil channel

The isolated whole-funded contact at the nil channel. Its raw lemmas are those of a located
contact at the nil channel, and its firing (`CodeImage.canonical_entry_path_rhs`) is
`ConfigImage.funded_redex_fires_readback` with whole funding and an empty frame. Literal raw
endpoint equality is kept separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

def wholeEntryTerm (body payload : RawCostTerm) (authority : String) (tail : RawCostStack) :
    RawCostTerm := RawCostTerm.fromComponents (wholeOccurrenceConfig body payload authority tail)

theorem wholeEntry_authored_readout (body payload : CostTerm LiteralAuthority)
    {signatureSource : Pattern} (signature : TypedSignature signatureSource)
    (tail : CostStack LiteralAuthority) :
    wholeEntryTerm (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey signatureSource) (literalEncodeStack tail) =
      literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail) :=
  locatedWholeEntry_authored_readout nilChannelLocation body payload signature tail

theorem wholeEntry_wellFormed {body payload : RawCostTerm} {authority : String} {tail : RawCostStack}
    (bodyValid : body.wellFormed = true) (payloadValid : payload.wellFormed = true)
    (tailValid : tail.all RawCostSig.valid = true) :
    (wholeEntryTerm body payload authority tail).wellFormed = true :=
  locatedWholeEntry_wellFormed rfl bodyValid payloadValid tailValid

theorem wholeEntry_runtimeScope {body payload : RawCostTerm} {authority : String} {tail : RawCostStack}
    (bodySafe : body.runtimeBinderSafeAt 1 = true)
    (payloadSafe : payload.runtimeBinderSafeAt 0 = true) :
    (wholeEntryTerm body payload authority tail).runtimeBinderSafe = true :=
  locatedWholeEntry_runtimeScope rfl bodySafe payloadSafe

def canonicalWholeTarget (body payload : RawCostTerm) (tail : RawCostStack) : CostConfig String :=
  decodeRawConfig ((body.normalize.commSubst payload.normalize).components ++
    [RawCostTerm.purse occurrenceNilLocation (tail.map RawCostSig.normalize)])

theorem canonicalWholeTarget_readout (body payload : RawCostTerm) (tail : RawCostStack) :
    rawConfigStructuralDenote (encodeCostConfig (canonicalWholeTarget body payload tail)) =
      RawTermStructuralDenotation.combine
        (body.normalize.commSubst payload.normalize).structuralDenote
        (RawCostTerm.purse occurrenceNilLocation tail).structuralDenote :=
  locatedCanonicalWholeTarget_readout occurrenceNilLocation body payload tail

theorem wholeEntry_normalized_pair (body payload : RawCostTerm) :
    (RawCostProc.par (.recv occurrenceNilLocation body) (.send occurrenceNilLocation payload)).normalize =
      .par (.recv occurrenceNilLocation body.normalize) (.send occurrenceNilLocation payload.normalize) ∨
    (RawCostProc.par (.recv occurrenceNilLocation body) (.send occurrenceNilLocation payload)).normalize =
      .par (.send occurrenceNilLocation payload.normalize) (.recv occurrenceNilLocation body.normalize) :=
  locatedWholeEntry_normalized_pair occurrenceNilLocation body payload

theorem wholeEntry_canonical_declarative (body payload : RawCostTerm) (authority : String)
    (tail : RawCostStack) :
    CostStep (decodeRawConfig (wholeEntryTerm body payload authority tail).normalizeConfig)
      (.quote .nil) {authority} (canonicalWholeTarget body payload tail) :=
  locatedWholeEntry_canonical_declarative occurrenceNilLocation body payload authority tail

theorem wholeEntry_canonical_runtime {body payload : RawCostTerm} {authority : String} {tail : RawCostStack}
    (bodyValid : body.wellFormed = true) (payloadValid : payload.wellFormed = true)
    (tailValid : tail.all RawCostSig.valid = true) :
    RuntimeCostStepComplete (wholeEntryTerm body payload authority tail).normalizeConfig
      (.quote .nil) {authority} (canonicalWholeTarget body payload tail) :=
  locatedWholeEntry_canonical_runtime rfl bodyValid payloadValid tailValid

theorem CodeImage.canonical_entry_supported {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) {signatureSource : Pattern}
    (signature : TypedSignature signatureSource) :
    (literalEncodeTerm (decodedReceiverSource nilChannelLocation body payload signature.val tail)).supported = true := by
  rw [← wholeEntry_authored_readout, RawCostTerm.supported, Bool.and_eq_true]
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
  obtain ⟨fuel, readback⟩ := (receiver_contractum_image (location := nilChannelLocation) resultImage
    tailImage).parser_eventually nilChannelLocation_free nilChannelLocation_supported
  refine ⟨_, fuel, readback fuel le_rfl, ?_⟩
  rw [rawConfigStructuralDenote_normalizeConfig, structuralDenote_literal, receiver_contractum_components]
  exact locatedCanonicalWholeTarget_observation bodyImage payloadImage same nilChannelLocation tail

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
          RawTraceComponent.term) = rawConfigStructuralDenote (literalEncodeTerm target).normalizeConfig :=
  (receiver_config_structural_image bodyImage payloadImage signature accepted tailImage).funded_redex_fires_readback
    .baseZeroQuote bodyImage payloadImage (.whole signature tail) 0 (add_zero _).symm
    (fun result => locatedContact nilChannelLocation (.par result .nil) tail)
    (fun resultImage => receiver_contractum_image resultImage tailImage)
    (fun result => (receiver_contractum_components nilChannelLocation result tail).trans (add_zero _).symm)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
