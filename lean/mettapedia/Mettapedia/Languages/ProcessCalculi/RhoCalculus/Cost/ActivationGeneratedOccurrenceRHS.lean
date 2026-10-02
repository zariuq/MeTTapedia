import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedOccurrenceInventory

/-!
# Full authored RHS comparison for actual occurrence successors

The existing target parser returns the actual authored contact and funding
tail. Its explicitly normalized configuration readout equals the actual
traced successor, retaining multiplicities, exact keys and located purses.
The occurrence path starts from literal encoded components; canonical entry
requires a separate normalization versus communication compatibility law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem raw_normalConfig_par (left right : RawCostTerm) :
    decodeRawConfig (RawCostTerm.par left right).normalizeConfig =
      decodeRawConfig left.normalizeConfig + decodeRawConfig right.normalizeConfig := by
  unfold RawCostTerm.normalizeConfig
  rw [decodeRawConfig_stableKeySort, decodeRawConfig_stableKeySort, decodeRawConfig_stableKeySort]
  simp only [RawCostTerm.normalize]
  have components :
      (stableKeySort RawCostTerm.key (left.normalize.components ++ right.normalize.components)).Forall
        RawCostTerm.IsComponent :=
    stableKeySort_forall RawCostTerm.key
      (List.forall_append.mpr ⟨RawCostTerm.components_forall_isComponent _,
        RawCostTerm.components_forall_isComponent _⟩)
  rw [RawCostTerm.components_fromComponents _ components, decodeRawConfig_stableKeySort,
    decodeRawConfig_append]

theorem raw_normalConfig_nil : decodeRawConfig RawCostTerm.nil.normalizeConfig = 0 := rfl

theorem raw_normalConfig_components (term : RawCostTerm) :
    decodeRawConfig term.normalizeConfig = (decodeCostTerm term.normalize).components := by
  unfold RawCostTerm.normalizeConfig
  rw [decodeRawConfig_stableKeySort, decodeRawConfig_components]

theorem StackImage.literal_normalize_identity {source : Pattern} {stack : CostStack LiteralAuthority}
    (image : StackImage source stack) :
    (literalEncodeStack stack).map RawCostSig.normalize = literalEncodeStack stack := by
  induction image with
  | empty => rfl
  | cons signature accepted rest ih =>
    change (encodeCostSig (signature.val.map literalAuthorityKey)).normalize ::
      (literalEncodeStack _).map RawCostSig.normalize =
      encodeCostSig (signature.val.map literalAuthorityKey) :: literalEncodeStack _
    rw [signature.property.1, literalEncodeSig_singleton, ih]
    rfl

theorem StackImage.literal_purse_normalConfig {source : Pattern} {stack : CostStack LiteralAuthority}
    (image : StackImage source stack) :
    decodeRawConfig (RawCostTerm.purse occurrenceNilLocation (literalEncodeStack stack)).normalizeConfig =
      {CostTerm.purse (.quote .nil) (stack.relabel literalAuthorityKey)} := by
  rw [raw_normalConfig_components]
  change (decodeCostTerm (.purse occurrenceNilLocation
    ((literalEncodeStack stack).map RawCostSig.normalize))).components = _
  rw [image.literal_normalize_identity]
  change {CostTerm.purse (.quote .nil) (decodeCostStack (literalEncodeStack stack))} = _
  rw [literalEncodeStack, decodeCostStack_encodeCostStack]

theorem CodeImage.wholeOccurrence_successor_rhs {bodySource payloadSource tailSource : Pattern}
    {body payload : CostTerm LiteralAuthority} {tail : CostStack LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) (authority : Pattern) :
    ∃ target fuel,
      (config? nilChannelLocation nilChannelLocation_free nilChannelLocation_supported fuel
        (receiverContractum bodySource payloadSource tailSource)).map Subtype.val = some target ∧
      decodeRawConfig ((applyTracedStep
        (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey authority) (literalEncodeStack tail))
        (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey authority) (literalEncodeStack tail)) 0).map RawTraceComponent.term) =
        decodeRawConfig (literalEncodeTerm target).normalizeConfig := by
  obtain ⟨result, resultImage, same⟩ := bodyImage.substitute_raw_readout payloadImage
  let target := locatedContact nilChannelLocation (.par result .nil) tail
  have targetImage : ConfigImage nilChannelLocation
      (receiverContractum bodySource payloadSource tailSource) target :=
    .contact (.collection (.cons (resultImage.toConfigImage nilChannelLocation) .nil)) tailImage
  obtain ⟨fuel, readback⟩ := targetImage.parser_eventually nilChannelLocation_free nilChannelLocation_supported
  refine ⟨target, fuel, readback fuel (le_refl fuel), ?_⟩
  rw [wholeOccurrenceSuccessor_components]
  have contractum : (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey authority) (literalEncodeStack tail)).contractum =
        (literalEncodeTerm result).normalize := by
    change ((literalEncodeTerm body).commSubst (literalEncodeTerm payload)).normalize = _
    rw [← literalEncodeTerm_commSubst]
    exact same
  rw [contractum, RawCostTerm.normalize_idempotent]
  change _ = decodeRawConfig
    (RawCostTerm.par (RawCostTerm.par (literalEncodeTerm result) .nil)
      (.purse occurrenceNilLocation (literalEncodeStack tail))).normalizeConfig
  rw [raw_normalConfig_par, raw_normalConfig_par, raw_normalConfig_nil, add_zero,
    raw_normalConfig_components, tailImage.literal_purse_normalConfig,
    literalEncodeStack, decodeCostStack_encodeCostStack]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
