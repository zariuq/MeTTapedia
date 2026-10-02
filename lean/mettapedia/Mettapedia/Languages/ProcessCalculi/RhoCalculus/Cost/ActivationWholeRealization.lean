import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationWholeRepresentative

/-!
# Whole-rule representatives for exact funded occurrences

The actual selected contact and the untouched occurrence frame are reified by
the existing parser. Their full normalized raw component multiset is exactly
the original configuration. The contact fires the authored R1 rule; the
collection containing that contact is only a configuration representative,
since the one-rule authored language has no parallel congruence declaration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open ActivationGenerated ActivationGenerated.SerializationAdmission
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Parallel normal readout retains the complete raw component multiset. -/
theorem raw_normalConfig_par_toMultiset (left right : RawCostTerm) :
    ((RawCostTerm.par left right).normalizeConfig : Multiset RawCostTerm) =
      (left.normalizeConfig : Multiset RawCostTerm) + (right.normalizeConfig : Multiset RawCostTerm) := by
  unfold RawCostTerm.normalizeConfig
  rw [stableKeySort_toMultiset, stableKeySort_toMultiset, stableKeySort_toMultiset]
  change ((RawCostTerm.fromComponents (stableKeySort RawCostTerm.key
    (left.normalize.components ++ right.normalize.components))).components : Multiset RawCostTerm) = _
  rw [RawCostTerm.components_fromComponents]
  · rw [stableKeySort_toMultiset]
    rfl
  · apply stableKeySort_forall
    exact List.forall_append.mpr ⟨RawCostTerm.components_forall_isComponent _,
      RawCostTerm.components_forall_isComponent _⟩

theorem raw_normalConfig_component_toMultiset {term : RawCostTerm}
    (component : term.IsComponent) (normalized : term.normalize = term) :
    (term.normalizeConfig : Multiset RawCostTerm) = {term} := by
  unfold RawCostTerm.normalizeConfig
  rw [stableKeySort_toMultiset, normalized,
    RawCostTerm.components_eq_singleton_of_isComponent component]
  rfl

theorem RawWholeOccurrenceCover.admitted_location {channelSource : Pattern}
    {location : CostName LiteralAuthority} {config : RawCostConfig}
    (_channelImage : NameImage 0 channelSource location) (cover : RawWholeOccurrenceCover config)
    (images : config.Forall (ConfigAdmitted (literalEncodeName location).normalize)) :
    (literalEncodeName location).normalize = cover.redex.location := by
  obtain ⟨purse, selected, purseLocation, _head, _tail⟩ := cover.admitted_selected_singleton images
  have located := cover.located purse (by rw [selected]; simp)
  rw [purseLocation, RawCostName.normalize_idempotent,
    wholeAt?_location_normalized cover.found] at located
  exact located

/-- Reify the selected whole contact and the exact unconsumed occurrence
frame. The representative's normal source bag agrees literally, retaining
all seals, locations, purse occurrences and ordered stack tails. -/
theorem RawWholeOccurrenceCover.authored_representative
    {channelSource : Pattern} {location : CostName LiteralAuthority} {config : RawCostConfig}
    (channelImage : NameImage 0 channelSource location) (cover : RawWholeOccurrenceCover config)
    (images : config.Forall (ConfigAdmitted (literalEncodeName location).normalize))
    (components : config.Forall RawCostTerm.IsComponent)
    (normalized : config.Forall (fun term => term.normalize = term)) :
    ∃ reversed bodySource payloadSource signatureSource tailSource frameSource,
      ∃ (signature : TypedSignature signatureSource), ∃ body payload tail frame,
        CodeImage 1 bodySource body ∧ CodeImage 0 payloadSource payload ∧
        signature? signatureSource = some signature ∧ StackImage tailSource tail ∧
        ConfigImage location frameSource frame ∧
        ConfigImage location
          (orderedReceiverSource reversed channelSource bodySource payloadSource signatureSource tailSource)
          (locatedContact location (orderedReceiverCode reversed location body payload signature.val)
            (.cons signature.val tail)) ∧
        ((literalEncodeTerm (.par
          (locatedContact location (orderedReceiverCode reversed location body payload signature.val)
            (.cons signature.val tail)) (.par frame .nil))).normalizeConfig : Multiset RawCostTerm) =
          (config : Multiset RawCostTerm) ∧
        receiverBindings channelSource bodySource payloadSource signatureSource tailSource ∈
          matchPatternForRuleUsing rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeRedexRewrite
            (orderedReceiverSource reversed channelSource bodySource payloadSource signatureSource tailSource) ∧
        Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
          (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
          rhoCIGSLT.costWholeLanguage
          (orderedReceiverSource reversed channelSource bodySource payloadSource signatureSource tailSource)
          (receiverContractum bodySource payloadSource tailSource) := by
  obtain ⟨bodySource, payloadSource, signatureSource, signature, body, payload,
    bodyImage, payloadImage, checked, authority, bodySame, payloadSame⟩ := cover.admitted_fields images
  obtain ⟨purse, selected, purseLocation, head, tailAdmitted⟩ := cover.admitted_selected_singleton images
  obtain ⟨tailSource, tail, tailImage, tailSame⟩ := tailAdmitted.readback
  have locationSame := cover.admitted_location channelImage images
  obtain ⟨reversed, sourceSame⟩ := whole_source_normalized_readout cover.found
    location body payload signature locationSame authority bodySame payloadSame
  let retained := eraseIndices config ([cover.redex.index] ++ cover.selected.map RawIndexedPurse.index)
  obtain ⟨frameSource, frame, frameFuel, parsed, frameSame⟩ := configuration_parser_readback channelImage
    (RawCostName.normalize_idempotent _) retained (eraseIndices_forall images _)
    (eraseIndices_forall components _) (eraseIndices_forall normalized _)
  have frameImage := config_parser_image parsed
  have sourceNormalized := List.forall_iff_forall_mem.mp normalized cover.source
    (List.fst_mem_of_mem_zipIdx cover.occurrence)
  have sourceComponent := List.forall_iff_forall_mem.mp components cover.source
    (List.fst_mem_of_mem_zipIdx cover.occurrence)
  have codeBag : ((literalEncodeTerm
      (orderedReceiverCode reversed location body payload signature.val)).normalizeConfig : Multiset RawCostTerm) =
      {cover.source} := by
    unfold RawCostTerm.normalizeConfig
    rw [stableKeySort_toMultiset, ← sourceSame, sourceNormalized,
      RawCostTerm.components_eq_singleton_of_isComponent sourceComponent]
    rfl
  have encoded : encodeCostSig (signature.val.map literalAuthorityKey) = [literalAuthorityKey signatureSource] := by
    rw [signature.property.1, literalEncodeSig_singleton]
  have purseSame : (literalEncodeTerm (CostTerm.purse location (.cons signature.val tail))).normalize = purse.toTerm := by
    change RawCostTerm.purse (literalEncodeName location).normalize
      ((encodeCostSig (signature.val.map literalAuthorityKey)).normalize ::
        (literalEncodeStack tail).map RawCostSig.normalize) =
        RawCostTerm.purse purse.location (purse.head :: purse.tail)
    have headEncoded : (encodeCostSig (signature.val.map literalAuthorityKey)).normalize = purse.head := by
      rw [encoded, head, authority]
      rfl
    rw [headEncoded, tailImage.literal_normalize_identity, tailSame, purseLocation]
  have purseBag : ((literalEncodeTerm (CostTerm.purse location (.cons signature.val tail))).normalizeConfig :
      Multiset RawCostTerm) = {purse.toTerm} := by
    unfold RawCostTerm.normalizeConfig
    rw [stableKeySort_toMultiset, purseSame]
    rfl
  refine ⟨reversed, bodySource, payloadSource, signatureSource, tailSource, frameSource,
    signature, body, payload, tail, frame, bodyImage, payloadImage, checked, tailImage,
    frameImage, ordered_receiver_image reversed channelImage bodyImage payloadImage signature checked tailImage,
    ?_, ordered_receiver_match reversed _ _ _ _ _, ordered_receiver_step reversed _ _ _ _ _⟩
  change ((RawCostTerm.par
    (RawCostTerm.par (literalEncodeTerm (orderedReceiverCode reversed location body payload signature.val))
      (literalEncodeTerm (CostTerm.purse location (.cons signature.val tail))))
    (RawCostTerm.par (literalEncodeTerm frame) .nil)).normalizeConfig : Multiset RawCostTerm) = _
  rw [raw_normalConfig_par_toMultiset, raw_normalConfig_par_toMultiset,
    raw_normalConfig_par_toMultiset, codeBag, purseBag, frameSame]
  have partition := whole_source_partition cover.occurrence cover.found cover.sourceOrdered
  change (retained : Multiset RawCostTerm) + {cover.source} +
    (cover.selected.map RawIndexedPurse.toTerm : Multiset RawCostTerm) = (config : Multiset RawCostTerm) at partition
  rw [selected] at partition
  change {cover.source} + {purse.toTerm} + ((retained : Multiset RawCostTerm) + 0) = _
  calc
    _ = (retained : Multiset RawCostTerm) + {cover.source} + {purse.toTerm} := by ac_rfl
    _ = _ := by simpa only [List.map_cons, List.map_nil, Multiset.coe_singleton] using partition

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
