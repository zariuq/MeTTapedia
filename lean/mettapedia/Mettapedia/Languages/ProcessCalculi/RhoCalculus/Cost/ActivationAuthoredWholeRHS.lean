import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAuthoredWholeOccurrence

/-!
# Full authored RHS readout with the same physical tail and frame

The backwards comparison derives collector success from parsed code and
keeps the selected purse's entire ordered tail. Both grouped endpoint images
use the original parser; only their source bag is a literal equality, while
the runtime successor uses the established full cost structural observer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open SerializationAdmission

theorem AuthoredWholeParserFields.enabled_full_rhs
    {locationSource : Pattern} {location : CostName LiteralAuthority}
    {source : Pattern} {decoded : CostTerm LiteralAuthority} {bindings : Bindings}
    (locationImage : NameImage 0 locationSource location)
    (fields : AuthoredWholeParserFields location source decoded bindings)
    {config : RawCostConfig} (wellFormed : config.Forall (fun term => term.wellFormed = true))
    (images : config.Forall (ConfigAdmitted (literalEncodeName location).normalize))
    (components : config.Forall RawCostTerm.IsComponent)
    (normalized : config.Forall (fun term => term.normalize = term))
    (inputLocated : (literalEncodeName fields.inputChannel).normalize = (literalEncodeName location).normalize)
    (outputLocated : (literalEncodeName fields.outputChannel).normalize = (literalEncodeName location).normalize)
    (index : Nat)
    (occurrence : ((literalEncodeTerm (twoChannelReceiverCode fields.reversed fields.inputChannel
      fields.outputChannel fields.body fields.payload fields.signature.val)).normalize, index) ∈ config.zipIdx)
    (purse : RawSelectedPurse) (purseMember : purse ∈ config.purses)
    (purseLocated : purse.location = (literalEncodeName location).normalize)
    (purseHead : purse.head = [literalAuthorityKey fields.signatureSource])
    (purseTail : purse.tail = literalEncodeStack fields.tail) :
    ∃ cover : RawWholeOccurrenceCover config, ∃ result frameSource frame,
      cover.redex.index = index ∧ cover.selected = [purse] ∧
      cover.runtimeStep ∈ runtimeCostCandidatesFromConfig config ∧
      ConfigImage location (receiverContractum fields.bodySource fields.payloadSource fields.tailSource)
        (locatedContact location (.par result .nil) fields.tail) ∧
      ConfigImage location frameSource frame ∧
      ((literalEncodeTerm (.par decoded (.par frame .nil))).normalizeConfig : Multiset RawCostTerm) =
        (config : Multiset RawCostTerm) ∧
      rawConfigStructuralDenote cover.runtimeStep.residual.normalizeConfig =
        rawConfigStructuralDenote (literalEncodeTerm (.par
          (locatedContact location (.par result .nil) fields.tail) (.par frame .nil))).normalizeConfig := by
  obtain ⟨cover, indexSame, _locationSame, bodySame, payloadSame, _sigSame, sourceEq, selected, enabled⟩ :=
    fields.exact_occurrence_cover wellFormed inputLocated outputLocated index occurrence
      purse purseMember purseLocated purseHead
  have receiverAdmitted : CodeAdmitted 1 cover.redex.body := by
    rw [bodySame]
    exact fields.bodyImage.serialized.normalize
  have payloadAdmitted : CodeAdmitted 0 cover.redex.payload := by
    rw [payloadSame]
    exact fields.payloadImage.serialized.normalize
  have receiverReadout : cover.redex.body.normalize = (literalEncodeTerm fields.body).normalize := by
    rw [bodySame, RawCostTerm.normalize_idempotent]
  have payloadReadout : cover.redex.payload.normalize = (literalEncodeTerm fields.payload).normalize := by
    rw [payloadSame, RawCostTerm.normalize_idempotent]
  obtain ⟨result, resultImage, resultObserved⟩ := raw_admitted_comm_readout
    receiverAdmitted payloadAdmitted fields.bodyImage fields.payloadImage receiverReadout payloadReadout
  let retained := eraseIndices config ([cover.redex.index] ++ cover.selected.map RawIndexedPurse.index)
  obtain ⟨frameSource, frame, frameFuel, frameParsed, frameSame⟩ := configuration_parser_readback
    locationImage (RawCostName.normalize_idempotent _) retained
    (eraseIndices_forall images _) (eraseIndices_forall components _) (eraseIndices_forall normalized _)
  have frameImage := config_parser_image frameParsed
  have targetImage : ConfigImage location
      (receiverContractum fields.bodySource fields.payloadSource fields.tailSource)
      (locatedContact location (.par result .nil) fields.tail) :=
    .contact (.collection (.cons (resultImage.toConfigImage location) .nil)) fields.tailImage
  have sourceSame : cover.source.normalize =
      (literalEncodeTerm (twoChannelReceiverCode fields.reversed fields.inputChannel fields.outputChannel
        fields.body fields.payload fields.signature.val)).normalize := by
    rw [sourceEq, RawCostTerm.normalize_idempotent]
  have encodedFunding : encodeCostSig (fields.fundingSignature.val.map literalAuthorityKey) =
      [literalAuthorityKey fields.signatureSource] := by
    rw [← fields.signature_value_eq, fields.signature.property.1, literalEncodeSig_singleton]
  have purseSame : (literalEncodeTerm (CostTerm.purse location
      (.cons fields.fundingSignature.val fields.tail))).normalize = purse.toTerm := by
    change RawCostTerm.purse (literalEncodeName location).normalize
      ((encodeCostSig (fields.fundingSignature.val.map literalAuthorityKey)).normalize ::
        (literalEncodeStack fields.tail).map RawCostSig.normalize) =
      .purse purse.location (purse.head :: purse.tail)
    rw [encodedFunding, fields.tailImage.serialized.normalize_identity, ← purseLocated, ← purseTail, purseHead]
    rfl
  have sourceBag := cover.source_partition_normal_readout
    (twoChannelReceiverCode fields.reversed fields.inputChannel fields.outputChannel
      fields.body fields.payload fields.signature.val)
    (.purse location (.cons fields.fundingSignature.val fields.tail)) frame purse
    selected sourceSame purseSame frameSame components normalized
  refine ⟨cover, result, frameSource, frame, indexSame, selected, enabled, targetImage, frameImage,
    ?_, cover.residual_full_structural_comparison location result frame fields.tail purse
      selected purseLocated purseTail.symm resultObserved frameSame⟩
  rw [fields.decoded_eq]
  exact sourceBag

/-- Concrete occurrence admission keeps the indexed code and selected
physical purse as input data. It contains no collector, enabledness or
successor-comparison premise. -/
structure AuthoredWholeOccurrenceAdmission {location : CostName LiteralAuthority}
    {source : Pattern} {decoded : CostTerm LiteralAuthority} {bindings : Bindings}
    (fields : AuthoredWholeParserFields location source decoded bindings) (config : RawCostConfig) where
  inputLocated : (literalEncodeName fields.inputChannel).normalize = (literalEncodeName location).normalize
  outputLocated : (literalEncodeName fields.outputChannel).normalize = (literalEncodeName location).normalize
  index : Nat
  occurrence : ((literalEncodeTerm (twoChannelReceiverCode fields.reversed fields.inputChannel
    fields.outputChannel fields.body fields.payload fields.signature.val)).normalize, index) ∈ config.zipIdx
  purse : RawSelectedPurse
  purseMember : purse ∈ config.purses
  purseLocated : purse.location = (literalEncodeName location).normalize
  purseHead : purse.head = [literalAuthorityKey fields.signatureSource]
  purseTail : purse.tail = literalEncodeStack fields.tail

/-- Every actual admitted R1 firing supplies its independent concrete
occurrence admission problem. Any such same-purse witness lifts to the
existing catalogue and full RHS observer with an unchanged retained frame.
The grouped endpoint images do not assert a grouped authored step. -/
theorem actual_whole_step_physical_lifting
    {base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator}
    {locationSource : Pattern} {location : CostName LiteralAuthority}
    {source target : Pattern} {decoded : CostTerm LiteralAuthority}
    (step : Step (.reflection rhoCIGSLT.costWholeReflectionProfile) base
      rhoCIGSLT.costWholeLanguage source target)
    (image : ConfigImage location source decoded)
    (locationImage : NameImage 0 locationSource location)
    (config : RawCostConfig) (wellFormed : config.Forall (fun term => term.wellFormed = true))
    (images : config.Forall (ConfigAdmitted (literalEncodeName location).normalize))
    (components : config.Forall RawCostTerm.IsComponent)
    (normalized : config.Forall (fun term => term.normalize = term)) :
    ∃ bindings, ∃ fields : AuthoredWholeParserFields location source decoded bindings,
      target = receiverContractum fields.bodySource fields.payloadSource fields.tailSource ∧
      ∀ admission : AuthoredWholeOccurrenceAdmission fields config,
        ∃ cover : RawWholeOccurrenceCover config, ∃ frameSource sourceTerm targetTerm,
          cover.redex.index = admission.index ∧ cover.selected = [admission.purse] ∧
          cover.runtimeStep ∈ runtimeCostCandidatesFromConfig config ∧
          ConfigImage location (.collection .hashBag [source, frameSource] none) sourceTerm ∧
          ConfigImage location (.collection .hashBag [target, frameSource] none) targetTerm ∧
          ((literalEncodeTerm sourceTerm).normalizeConfig : Multiset RawCostTerm) =
            (config : Multiset RawCostTerm) ∧
          rawConfigStructuralDenote cover.runtimeStep.residual.normalizeConfig =
            rawConfigStructuralDenote (literalEncodeTerm targetTerm).normalizeConfig := by
  obtain ⟨bindings, fields, targetEq⟩ := actual_whole_step_parser_fields step image
  refine ⟨bindings, fields, targetEq, ?_⟩
  intro admission
  obtain ⟨cover, result, frameSource, frame, indexSame, selected, enabled, targetImage,
    frameImage, sourceBag, targetObserved⟩ := fields.enabled_full_rhs locationImage wellFormed images
      components normalized admission.inputLocated admission.outputLocated admission.index
      admission.occurrence admission.purse admission.purseMember admission.purseLocated
      admission.purseHead admission.purseTail
  refine ⟨cover, frameSource, .par decoded (.par frame .nil),
    .par (locatedContact location (.par result .nil) fields.tail) (.par frame .nil),
    indexSame, selected, enabled, .collection (.cons image (.cons frameImage .nil)), ?_,
    sourceBag, targetObserved⟩
  rw [targetEq]
  exact .collection (.cons targetImage (.cons frameImage .nil))

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
