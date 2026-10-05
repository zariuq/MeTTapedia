import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSplitCanonicalSource
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAtomicPurseImage

/-!
# Readouts for the canonical split firing

The configuration readout reads separately signed endpoints and their two purses. The firing
(`NameImage.split_canonical_entry_path_rhs`) is `ConfigImage.funded_redex_fires_readback` with
split funding and an empty frame: one step spends both keys, and the successor, with both tails
kept, is observed as a readout of generated syntax. No generated rewrite is asserted for split
funding.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

def splitFundingTailSource (tail : Pattern) : Pattern :=
  .apply "$cost:apparatus-constructor:contact"
    [.apply "$cost:wrapped-constructor:PZero" [],
     .apply "$cost:apparatus-constructor:funding" [tail]]

def splitReceiverSuccessorSource (body payload recvTail sendTail : Pattern) : Pattern :=
  ambientReceiverContractum body payload recvTail (splitFundingTailSource sendTail)

theorem NameImage.split_canonical_target_observation
    {channelSource bodySource payloadSource recvTailSource sendTailSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    {recvTail sendTail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (recvTailImage : StackImage recvTailSource recvTail) (sendTailImage : StackImage sendTailSource sendTail) :
    ∃ target fuel,
      (config? location channelImage.purseInventory_zero channelImage.runtimeSupported fuel
        (splitReceiverSuccessorSource bodySource payloadSource recvTailSource sendTailSource)).map
          Subtype.val = some target ∧
      rawConfigStructuralDenote (encodeCostConfig
        (locatedSplitCanonicalTarget (literalEncodeName location) (literalEncodeTerm body)
          (literalEncodeTerm payload) (literalEncodeStack recvTail) (literalEncodeStack sendTail))) =
        rawConfigStructuralDenote (literalEncodeTerm target).normalizeConfig := by
  have ambientImage : ConfigImage location (splitFundingTailSource sendTailSource)
      (locatedContact location .nil sendTail) := .contact .zero sendTailImage
  obtain ⟨target, fuel, parsed, observed⟩ :=
    channelImage.ambient_canonical_target_observation bodyImage payloadImage recvTailImage ambientImage
  have tailReadout : literalEncodeTerm (.par (locatedContact location .nil sendTail) .nil) =
      RawCostTerm.par (.par .nil (.purse (literalEncodeName location) (literalEncodeStack sendTail))) .nil := rfl
  rw [tailReadout] at observed
  exact ⟨target, fuel, parsed, observed⟩

/-- Readouts of source and successor, a candidate spending both keys, and a path of one step. -/
theorem NameImage.split_canonical_entry_path_rhs
    {channelSource bodySource payloadSource recvSignatureSource sendSignatureSource recvTailSource sendTailSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    {recvTail sendTail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (recvSignature : TypedSignature recvSignatureSource)
    (recvAccepted : signature? recvSignatureSource = some recvSignature)
    (sendSignature : TypedSignature sendSignatureSource)
    (sendAccepted : signature? sendSignatureSource = some sendSignature)
    (recvTailImage : StackImage recvTailSource recvTail) (sendTailImage : StackImage sendTailSource sendTail) :
    let source := literalEncodeTerm
      (decodedSplitReceiver location body payload recvSignature.val sendSignature.val recvTail sendTail)
    ∃ sourceFuel step target fuel,
      (config? location channelImage.purseInventory_zero channelImage.runtimeSupported sourceFuel
        (splitReceiverSource channelSource bodySource payloadSource recvSignatureSource sendSignatureSource
          recvTailSource sendTailSource)).map Subtype.val =
        some (decodedSplitReceiver location body payload recvSignature.val sendSignature.val recvTail sendTail) ∧
      runtimeCostCandidates source = some (runtimeCostCandidatesFromConfig source.normalizeConfig) ∧
      (config? location channelImage.purseInventory_zero channelImage.runtimeSupported fuel
        (splitReceiverSuccessorSource bodySource payloadSource recvTailSource sendTailSource)).map Subtype.val = some target ∧
      step ∈ runtimeCostCandidatesFromConfig source.normalizeConfig ∧
      decodeCostName step.location = decodeCostName (literalEncodeName location).normalize ∧
      decodeCostSig step.spend = {literalAuthorityKey recvSignatureSource} + {literalAuthorityKey sendSignatureSource} ∧
      step.FrameExactFor source.normalizeConfig ∧
      (∃ path : CostPath 0 (initialTraceComponents source) 1
          (applyTracedStep (initialTraceComponents source) step 0), path.depth = 1) ∧
      rawConfigStructuralDenote ((applyTracedStep (initialTraceComponents source) step 0).map
        RawTraceComponent.term) = rawConfigStructuralDenote (literalEncodeTerm target).normalizeConfig :=
  (split_receiver_config_image channelImage bodyImage payloadImage recvSignature recvAccepted sendSignature
    sendAccepted recvTailImage sendTailImage).funded_redex_fires_readback channelImage bodyImage payloadImage
    (.split recvSignature sendSignature recvTail sendTail) 0 (add_zero _).symm
    (fun result => .par (locatedContact location (.par result .nil) recvTail)
      (.par (locatedContact location .nil sendTail) .nil))
    (fun resultImage => .collection (.cons (receiver_contractum_image resultImage recvTailImage)
      (.cons (.contact .zero sendTailImage) .nil)))
    (fun result => by
      simp [CostTerm.components, locatedContact, Funding.residue])

/-- The two admitted funding occurrences consume two cells in one actual firing, with exact two-atom debit. -/
theorem NameImage.split_canonical_entry_resource_balance
    {channelSource bodySource payloadSource recvSignatureSource sendSignatureSource recvTailSource sendTailSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    {recvTail sendTail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (recvSignature : TypedSignature recvSignatureSource)
    (recvAccepted : signature? recvSignatureSource = some recvSignature)
    (sendSignature : TypedSignature sendSignatureSource)
    (sendAccepted : signature? sendSignatureSource = some sendSignature)
    (recvTailImage : StackImage recvTailSource recvTail) (sendTailImage : StackImage sendTailSource sendTail) :
    let source := literalEncodeTerm
      (decodedSplitReceiver location body payload recvSignature.val sendSignature.val recvTail sendTail)
    ∃ step,
      step ∈ runtimeCostCandidatesFromConfig source.normalizeConfig ∧
      decodeCostSig step.spend = {literalAuthorityKey recvSignatureSource} + {literalAuthorityKey sendSignatureSource} ∧
      step.selectedPurses.length = 2 ∧
      (∃ path : CostPath 0 (initialTraceComponents source) 1
          (applyTracedStep (initialTraceComponents source) step 0), path.depth = 1) ∧
      (decodeRawConfig ((applyTracedStep (initialTraceComponents source) step 0).map
        RawTraceComponent.term)).ResourceSeparated ∧
      (decodeRawConfig source.normalizeConfig).physicalPurseCells =
        (decodeRawConfig ((applyTracedStep (initialTraceComponents source) step 0).map
          RawTraceComponent.term)).physicalPurseCells + 2 ∧
      (decodeRawConfig source.normalizeConfig).storedSignatures =
        (decodeRawConfig ((applyTracedStep (initialTraceComponents source) step 0).map
          RawTraceComponent.term)).storedSignatures +
          ({literalAuthorityKey recvSignatureSource} + {literalAuthorityKey sendSignatureSource}) ∧
      (decodeRawConfig source.normalizeConfig).physicalPurseOccurrences =
        (decodeRawConfig ((applyTracedStep (initialTraceComponents source) step 0).map
          RawTraceComponent.term)).physicalPurseOccurrences := by
  obtain ⟨_, step, _, _, _, _, _, enabled, _, spent, _, path, _⟩ :=
    channelImage.split_canonical_entry_path_rhs bodyImage payloadImage recvSignature recvAccepted
      sendSignature sendAccepted recvTailImage sendTailImage
  have image := split_receiver_config_image channelImage bodyImage payloadImage
    recvSignature recvAccepted sendSignature sendAccepted recvTailImage sendTailImage
  have count := image.canonical_candidate_cells_eq_atoms channelImage enabled
  rw [spent, Multiset.card_add, Multiset.card_singleton, Multiset.card_singleton] at count
  obtain ⟨separated, cells, atoms, occurrences⟩ := image.canonical_candidate_inventory channelImage enabled
  exact ⟨step, enabled, spent, count, path, separated,
    by simpa only [count] using cells, by simpa only [spent] using atoms, occurrences⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
