import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationWholeRealization

/-!
# Full RHS comparison of reified whole occurrences

A retained whole occurrence determines a real authored R1 contact and its
untouched source frame. Both grouped endpoints are actual old-parser images.
The complete normalized source bag agrees literally with the runtime source;
the successor comparison uses the full cost structural observer. The grouped
source is not asserted to step in the one-rule authored language.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open ActivationGenerated ActivationGenerated.SerializationAdmission
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

theorem raw_admitted_comm_readout {body payload : RawCostTerm}
    {bodySource payloadSource : Pattern} {receiver message : CostTerm LiteralAuthority}
    (bodyAdmitted : CodeAdmitted 1 body) (payloadAdmitted : CodeAdmitted 0 payload)
    (bodyImage : CodeImage 1 bodySource receiver) (payloadImage : CodeImage 0 payloadSource message)
    (bodySame : body.normalize = (literalEncodeTerm receiver).normalize)
    (payloadSame : payload.normalize = (literalEncodeTerm message).normalize) :
    ∃ result, CodeImage 0
      (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.substituteReflective wrappedRhoDeclaration 0
        (generatedReplacement payloadSource) bodySource) result ∧
      (body.commSubst payload).structuralDenote = (literalEncodeTerm result).structuralDenote := by
  obtain ⟨result, image, same⟩ := bodyImage.substitute_raw_readout payloadImage
  refine ⟨result, image, ?_⟩
  have rawComparison := RawCostTerm.commSubst_normalize_structural 1
    bodyAdmitted.runtimeBinderSafeAt payloadAdmitted.runtimeBinderSafeAt
  have encodedComparison := RawCostTerm.commSubst_normalize_structural 1
    bodyImage.literal_runtimeBinderSafeAt payloadImage.literal_runtimeBinderSafeAt
  have normalizedSame :
      ((literalEncodeTerm receiver).commSubst (literalEncodeTerm message)).normalize =
        (literalEncodeTerm result).normalize := by
    rw [← literalEncodeTerm_commSubst]
    exact same
  unfold RawCostTerm.StructurallyEquivalent at rawComparison encodedComparison
  rw [RawCostTerm.structuralDenote_normalize, RawCostTerm.structuralDenote_normalize] at rawComparison encodedComparison
  calc
    _ = (body.normalize.commSubst payload.normalize).structuralDenote := rawComparison.symm
    _ = ((literalEncodeTerm receiver).normalize.commSubst
      (literalEncodeTerm message).normalize).structuralDenote := by rw [bodySame, payloadSame]
    _ = ((literalEncodeTerm receiver).commSubst (literalEncodeTerm message)).structuralDenote := encodedComparison
    _ = _ := by
      have observed := congrArg RawCostTerm.structuralDenote normalizedSame
      simpa only [RawCostTerm.structuralDenote_normalize] using observed

theorem residualFor_full_structural_readout (config : RawCostConfig) (participants : List Nat)
    (selected : List RawSelectedPurse) (contractum : RawCostTerm) :
    (residualFor config participants selected contractum).structuralDenote =
      RawTermStructuralDenotation.combine
        (rawConfigStructuralDenote (eraseIndices config (participants ++ selected.map RawIndexedPurse.index)))
        (RawTermStructuralDenotation.combine contractum.structuralDenote
          (rawConfigStructuralDenote (selected.map RawIndexedPurse.toTailTerm))) := by
  unfold residualFor
  rw [RawCostTerm.structuralDenote_normalize, RawCostTerm.structuralDenote_fromComponents]
  apply RawTermStructuralDenotation.ext <;>
    simp [rawConfigStructuralDenote, RawTermStructuralDenotation.combine,
      RawCostTerm.structuralAtoms_components, RawCostTerm.structuralDrops_components,
      RawCostTerm.structuralDenote_normalize, RawIndexedPurse.toTailTerm, Function.comp_def]

theorem literal_contractum_frame_structural_readout (location : CostName LiteralAuthority)
    (result frame : CostTerm LiteralAuthority) (tail : CostStack LiteralAuthority) :
    (literalEncodeTerm (.par (locatedContact location (.par result .nil) tail)
      (.par frame .nil))).structuralDenote =
      RawTermStructuralDenotation.combine (literalEncodeTerm frame).structuralDenote
        (RawTermStructuralDenotation.combine (literalEncodeTerm result).structuralDenote
          (literalEncodeTerm (CostTerm.purse location tail)).structuralDenote) := by
  change (RawCostTerm.par (RawCostTerm.par (RawCostTerm.par (literalEncodeTerm result) .nil)
    (literalEncodeTerm (CostTerm.purse location tail)))
    (RawCostTerm.par (literalEncodeTerm frame) .nil)).structuralDenote = _
  apply RawTermStructuralDenotation.ext <;>
    simp [RawCostTerm.structuralDenote, RawTermStructuralDenotation.combine,
      RawTermStructuralDenotation.empty, add_comm, add_left_comm]

/-- The selected cell and its ordered tail use the same checked whole
signature as the runtime firing. Normalization fixes the location once. -/
theorem RawWholeOccurrenceCover.admitted_funding_coordinates
    {channelSource : Pattern} {location : CostName LiteralAuthority} {config : RawCostConfig}
    (channelImage : NameImage 0 channelSource location) (cover : RawWholeOccurrenceCover config)
    (images : config.Forall (ConfigAdmitted (literalEncodeName location).normalize)) :
    ∃ signatureSource, ∃ signature : TypedSignature signatureSource,
      ∃ purse tailSource tail,
        signature? signatureSource = some signature ∧
        cover.runtimeStep.spend = [literalAuthorityKey signatureSource] ∧
        cover.runtimeStep.location = (literalEncodeName location).normalize ∧
        cover.runtimeStep.participantIndices = [cover.redex.index] ∧
        cover.runtimeStep.selectedPurses = [purse] ∧
        purse.location = (literalEncodeName location).normalize ∧
        purse.head = [literalAuthorityKey signatureSource] ∧
        StackImage tailSource tail ∧ purse.tail = literalEncodeStack tail := by
  obtain ⟨bodySource, payloadSource, signatureSource, signature, body, payload,
    _bodyImage, _payloadImage, checked, authority, _bodySame, _payloadSame⟩ := cover.admitted_fields images
  obtain ⟨purse, selected, purseLocation, head, tailAdmitted⟩ := cover.admitted_selected_singleton images
  obtain ⟨tailSource, tail, tailImage, tailSame⟩ := tailAdmitted.readback
  refine ⟨signatureSource, signature, purse, tailSource, tail, checked, authority,
    ?_, rfl, selected, purseLocation, head.trans authority, tailImage, tailSame.symm⟩
  exact (cover.admitted_location channelImage images).symm

/-- The existing source occurrence partition transports literal component
readouts without replacing the selected physical purse. -/
theorem RawWholeOccurrenceCover.source_partition_normal_readout
    {config : RawCostConfig} (cover : RawWholeOccurrenceCover config)
    (code funding frame : CostTerm LiteralAuthority) (purse : RawSelectedPurse)
    (selected : cover.selected = [purse])
    (sourceSame : cover.source.normalize = (literalEncodeTerm code).normalize)
    (purseSame : (literalEncodeTerm funding).normalize = purse.toTerm)
    (frameSame : ((literalEncodeTerm frame).normalizeConfig : Multiset RawCostTerm) =
      (eraseIndices config ([cover.redex.index] ++ cover.selected.map RawIndexedPurse.index) : Multiset RawCostTerm))
    (components : config.Forall RawCostTerm.IsComponent)
    (normalized : config.Forall (fun term => term.normalize = term)) :
    ((literalEncodeTerm (.par (.par code funding) (.par frame .nil))).normalizeConfig : Multiset RawCostTerm) =
      (config : Multiset RawCostTerm) := by
  have sourceNormalized := List.forall_iff_forall_mem.mp normalized cover.source
    (List.fst_mem_of_mem_zipIdx cover.occurrence)
  have sourceComponent := List.forall_iff_forall_mem.mp components cover.source
    (List.fst_mem_of_mem_zipIdx cover.occurrence)
  have codeBag : ((literalEncodeTerm code).normalizeConfig : Multiset RawCostTerm) = {cover.source} := by
    unfold RawCostTerm.normalizeConfig
    rw [stableKeySort_toMultiset, ← sourceSame, sourceNormalized,
      RawCostTerm.components_eq_singleton_of_isComponent sourceComponent]
    rfl
  have purseBag : ((literalEncodeTerm funding).normalizeConfig : Multiset RawCostTerm) = {purse.toTerm} := by
    unfold RawCostTerm.normalizeConfig
    rw [stableKeySort_toMultiset, purseSame]
    rfl
  change ((RawCostTerm.par (RawCostTerm.par (literalEncodeTerm code) (literalEncodeTerm funding))
    (RawCostTerm.par (literalEncodeTerm frame) .nil)).normalizeConfig : Multiset RawCostTerm) = _
  rw [raw_normalConfig_par_toMultiset, raw_normalConfig_par_toMultiset,
    raw_normalConfig_par_toMultiset, codeBag, purseBag, frameSame]
  have partition := whole_source_partition cover.occurrence cover.found cover.sourceOrdered
  rw [selected] at partition
  change {cover.source} + {purse.toTerm} +
    ((eraseIndices config ([cover.redex.index] ++ cover.selected.map RawIndexedPurse.index) : Multiset RawCostTerm) + 0) = _
  calc
    _ = (eraseIndices config ([cover.redex.index] ++ cover.selected.map RawIndexedPurse.index) : Multiset RawCostTerm) +
      {cover.source} + {purse.toTerm} := by ac_rfl
    _ = _ := by
      simpa only [selected, List.map_cons, List.map_nil, Multiset.coe_singleton] using partition

/-- Exact source-index removal and ordered selected tails give the whole
successor's full cost observation. No grouped authored step is required. -/
theorem RawWholeOccurrenceCover.residual_full_structural_comparison
    {config : RawCostConfig} (cover : RawWholeOccurrenceCover config)
    (location : CostName LiteralAuthority) (result frame : CostTerm LiteralAuthority)
    (tail : CostStack LiteralAuthority) (purse : RawSelectedPurse)
    (selected : cover.selected = [purse])
    (purseLocation : purse.location = (literalEncodeName location).normalize)
    (tailSame : literalEncodeStack tail = purse.tail)
    (resultObserved : (cover.redex.body.commSubst cover.redex.payload).structuralDenote =
      (literalEncodeTerm result).structuralDenote)
    (frameSame : ((literalEncodeTerm frame).normalizeConfig : Multiset RawCostTerm) =
      (eraseIndices config ([cover.redex.index] ++ cover.selected.map RawIndexedPurse.index) : Multiset RawCostTerm)) :
    rawConfigStructuralDenote cover.runtimeStep.residual.normalizeConfig =
      rawConfigStructuralDenote (literalEncodeTerm (.par
        (locatedContact location (.par result .nil) tail) (.par frame .nil))).normalizeConfig := by
  have frameObserved := congrArg rawConfigStructuralDenote frameSame
  rw [rawConfigStructuralDenote_normalizeConfig] at frameObserved
  have tailObserved : rawConfigStructuralDenote (cover.selected.map RawIndexedPurse.toTailTerm) =
      (literalEncodeTerm (CostTerm.purse location tail)).structuralDenote := by
    rw [selected]
    simp only [List.map_cons, List.map_nil, Multiset.coe_singleton, rawConfigStructuralDenote_singleton]
    change (RawCostTerm.purse purse.location purse.tail).structuralDenote =
      (RawCostTerm.purse (literalEncodeName location) (literalEncodeStack tail)).structuralDenote
    rw [purseLocation, ← tailSame]
    simp only [RawCostTerm.structuralDenote, RawCostName.structuralDenote_normalize]
  rw [rawConfigStructuralDenote_normalizeConfig, rawConfigStructuralDenote_normalizeConfig]
  change (residualFor config [cover.redex.index] cover.selected
    (cover.redex.body.commSubst cover.redex.payload).normalize).structuralDenote = _
  rw [residualFor_full_structural_readout, RawCostTerm.structuralDenote_normalize,
    resultObserved, tailObserved, ← frameObserved]
  exact (literal_contractum_frame_structural_readout location result frame tail).symm

/-- The contact and its same retained frame are presented through actual
parser images on both sides of the selected actual authored R1 firing. -/
theorem RawWholeOccurrenceCover.authored_full_rhs
    {channelSource : Pattern} {location : CostName LiteralAuthority} {config : RawCostConfig}
    (channelImage : NameImage 0 channelSource location) (cover : RawWholeOccurrenceCover config)
    (images : config.Forall (ConfigAdmitted (literalEncodeName location).normalize))
    (components : config.Forall RawCostTerm.IsComponent)
    (normalized : config.Forall (fun term => term.normalize = term)) :
    ∃ contactSource contactTarget frameSource sourceTerm targetTerm,
      Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
        rhoCIGSLT.costWholeLanguage contactSource contactTarget ∧
      ConfigImage location (.collection .hashBag [contactSource, frameSource] none) sourceTerm ∧
      ConfigImage location (.collection .hashBag [contactTarget, frameSource] none) targetTerm ∧
      ((literalEncodeTerm sourceTerm).normalizeConfig : Multiset RawCostTerm) = (config : Multiset RawCostTerm) ∧
      rawConfigStructuralDenote cover.runtimeStep.residual.normalizeConfig =
        rawConfigStructuralDenote (literalEncodeTerm targetTerm).normalizeConfig := by
  obtain ⟨bodySource, payloadSource, signatureSource, signature, receiver, message,
    bodyImage, payloadImage, checked, authority, bodySame, payloadSame⟩ := cover.admitted_fields images
  obtain ⟨purse, selected, purseLocation, head, tailAdmitted⟩ := cover.admitted_selected_singleton images
  obtain ⟨tailSource, tail, tailImage, tailSame⟩ := tailAdmitted.readback
  have sourceImage := List.forall_iff_forall_mem.mp images cover.source
    (List.fst_mem_of_mem_zipIdx cover.occurrence)
  obtain ⟨bodyAdmitted, payloadAdmitted⟩ := sourceImage.whole_code cover.found
  obtain ⟨result, resultImage, resultObserved⟩ := raw_admitted_comm_readout bodyAdmitted payloadAdmitted
    bodyImage payloadImage bodySame payloadSame
  obtain ⟨reversed, sourceSame⟩ := whole_source_normalized_readout cover.found location receiver message signature
    (cover.admitted_location channelImage images) authority bodySame payloadSame
  let retained := eraseIndices config ([cover.redex.index] ++ cover.selected.map RawIndexedPurse.index)
  obtain ⟨frameSource, frame, frameFuel, frameParsed, frameSame⟩ := configuration_parser_readback channelImage
    (RawCostName.normalize_idempotent _) retained (eraseIndices_forall images _)
    (eraseIndices_forall components _) (eraseIndices_forall normalized _)
  have frameImage := config_parser_image frameParsed
  let contactSource := orderedReceiverSource reversed channelSource bodySource payloadSource signatureSource tailSource
  let contactTarget := receiverContractum bodySource payloadSource tailSource
  let sourceTerm : CostTerm LiteralAuthority := .par (locatedContact location (orderedReceiverCode reversed location receiver message signature.val)
    (.cons signature.val tail)) (.par frame .nil)
  let targetTerm : CostTerm LiteralAuthority := .par (locatedContact location (.par result .nil) tail) (.par frame .nil)
  have contactSourceImage := ordered_receiver_image reversed channelImage bodyImage payloadImage signature checked tailImage
  have contactTargetImage : ConfigImage location contactTarget (locatedContact location (.par result .nil) tail) :=
    .contact (.collection (.cons (resultImage.toConfigImage location) .nil)) tailImage
  refine ⟨contactSource, contactTarget, frameSource, sourceTerm, targetTerm,
    ordered_receiver_step reversed _ _ _ _ _, .collection (.cons contactSourceImage (.cons frameImage .nil)),
    .collection (.cons contactTargetImage (.cons frameImage .nil)), ?_, ?_⟩
  · have purseSame : (literalEncodeTerm (CostTerm.purse location (.cons signature.val tail))).normalize = purse.toTerm := by
      change RawCostTerm.purse (literalEncodeName location).normalize
        ((encodeCostSig (signature.val.map literalAuthorityKey)).normalize ::
          (literalEncodeStack tail).map RawCostSig.normalize) =
            RawCostTerm.purse purse.location (purse.head :: purse.tail)
      have headEncoded : (encodeCostSig (signature.val.map literalAuthorityKey)).normalize = purse.head := by
        rw [signature.property.1, literalEncodeSig_singleton, head, authority]
        rfl
      rw [headEncoded, tailImage.literal_normalize_identity, tailSame, purseLocation]
    exact cover.source_partition_normal_readout _ _ _ purse selected sourceSame purseSame frameSame components normalized
  · exact cover.residual_full_structural_comparison location result frame tail purse
      selected purseLocation tailSame resultObserved frameSame

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
