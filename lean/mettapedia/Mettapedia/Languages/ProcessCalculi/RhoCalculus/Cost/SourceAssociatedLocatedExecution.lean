import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.PreSigningProcessReadout
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAmbientInventory

/-!
# Source-associated commitments at closed locations and in parallel frames

The exact signing key is computed from the complete original receiver and
sender before outer signing. The genuine process parser and intrinsic readout
associate it with an admitted source class. Canonical runtime entry then
constructs one selected firing, preserving its full RHS observation and
physical resource balance in the admitted ambient frame.

The channel is any closed name in the existing parser image. Funding uses the
configuration parser's explicit location index. The source key describes the
selected original pair; ambient code is retained separately. A signature
continues to be one opaque literal authority atom.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedLocatedExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated

def originalPair (channel body payload : Pattern) : Pattern :=
  .collection .hashBag
    [.apply (costBaseConstructorName "PInput") [channel, .lambda none body],
     .apply (costBaseConstructorName "POutput") [channel, payload]] none

def signature (channel body payload : Pattern) : Pattern :=
  AtomicSignatureInterpretation.commitLiteral
    (canonicalize (eraseGenerated (originalPair channel body payload)))

def authority (channel body payload : Pattern) : CostSig LiteralAuthority :=
  {signature channel body payload}

theorem signature_ne_unit (channel body payload : Pattern) :
    signature channel body payload ≠ .apply costSignatureUnitConstructorName [] := by
  simp [signature, AtomicSignatureInterpretation.commitLiteral,
    costSignatureCommitConstructorName, costSignatureUnitConstructorName]

theorem originalPair_image {channelSource bodySource payloadSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload) :
    ProcImage 0 (originalPair channelSource bodySource payloadSource)
      (.par (.recv location body) (.send location payload)) :=
  .pair (.recv channelImage bodyImage) (.send channelImage payloadImage)

/-- Both actual reader functions construct the original class associated with
the key. No separately supplied signature participates in this readout. -/
theorem admitted_origin {channelSource bodySource payloadSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload) :
    ∃ original : ClosedOriginAccountInterpretation.Origin,
      AtomicSignatureInterpretation.canonical rhoCIGSLT
        (ClosedOriginAccountInterpretation.admitted original) =
          signature channelSource bodySource payloadSource := by
  have pairImage := originalPair_image channelImage bodyImage payloadImage
  obtain ⟨fuel, result, found, exactRuntime⟩ := PreSigningProcessReadout.readout_of_image pairImage
  have readoutImage : ProcImage 0 (originalPair channelSource bodySource payloadSource)
      result.runtime.val := by
    rw [exactRuntime]
    exact pairImage
  exact ⟨PreSigningProcessReadout.origin readoutImage found,
    PreSigningProcessReadout.origin_signature readoutImage found⟩

theorem signature_decodes {channelSource bodySource payloadSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload) :
    ∃ decoded : TypedSignature (signature channelSource bodySource payloadSource),
      signature? (signature channelSource bodySource payloadSource) = some decoded ∧
        decoded.val = authority channelSource bodySource payloadSource := by
  obtain ⟨original, associated⟩ := admitted_origin channelImage bodyImage payloadImage
  unfold authority
  rw [← associated]
  exact ⟨Commitments.authority _, Commitments.canonical_decoded _, rfl⟩

/-- A computed source authority enables a real catalogue occurrence at the
closed channel. Parser readbacks, the path and balance refer to that same
occurrence, including the full retained ambient frame. -/
theorem canonical_entry_path_rhs_balance
    {channelSource bodySource payloadSource tailSource ambientSource : Pattern}
    {location : CostName LiteralAuthority} {body payload ambient : CostTerm LiteralAuthority}
    {tail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (tailImage : StackImage tailSource tail) (ambientImage : ConfigImage location ambientSource ambient) :
    let key := signature channelSource bodySource payloadSource
    let source := literalEncodeTerm
      (decodedAmbientReceiver location body payload {key} tail ambient)
    ∃ original : ClosedOriginAccountInterpretation.Origin,
      AtomicSignatureInterpretation.canonical rhoCIGSLT
        (ClosedOriginAccountInterpretation.admitted original) = key ∧
      ∃ sourceFuel step target fuel,
        (config? location channelImage.purseInventory_zero channelImage.runtimeSupported sourceFuel
          (ambientReceiverSource channelSource bodySource payloadSource key tailSource ambientSource)).map
            Subtype.val = some (decodedAmbientReceiver location body payload {key} tail ambient) ∧
        runtimeCostCandidates source = some (runtimeCostCandidatesFromConfig source.normalizeConfig) ∧
        (config? location channelImage.purseInventory_zero channelImage.runtimeSupported fuel
          (ambientReceiverContractum bodySource payloadSource tailSource ambientSource)).map Subtype.val =
            some target ∧
        step ∈ runtimeCostCandidatesFromConfig source.normalizeConfig ∧
        decodeCostName step.location = decodeCostName (literalEncodeName location).normalize ∧
        decodeCostSig step.spend = {literalAuthorityKey key} ∧
        step.FrameExactFor source.normalizeConfig ∧
        (∃ path : CostPath 0 (initialTraceComponents source) 1
            (applyTracedStep (initialTraceComponents source) step 0), path.depth = 1) ∧
        rawConfigStructuralDenote ((applyTracedStep (initialTraceComponents source) step 0).map
          RawTraceComponent.term) = rawConfigStructuralDenote (literalEncodeTerm target).normalizeConfig ∧
        (decodeRawConfig ((applyTracedStep (initialTraceComponents source) step 0).map
          RawTraceComponent.term)).ResourceSeparated ∧
        (decodeRawConfig source.normalizeConfig).physicalPurseCells =
          (decodeRawConfig ((applyTracedStep (initialTraceComponents source) step 0).map
            RawTraceComponent.term)).physicalPurseCells + 1 ∧
        (decodeRawConfig source.normalizeConfig).storedSignatures =
          (decodeRawConfig ((applyTracedStep (initialTraceComponents source) step 0).map
            RawTraceComponent.term)).storedSignatures + {literalAuthorityKey key} ∧
        (decodeRawConfig source.normalizeConfig).physicalPurseOccurrences =
          (decodeRawConfig ((applyTracedStep (initialTraceComponents source) step 0).map
            RawTraceComponent.term)).physicalPurseOccurrences := by
  obtain ⟨original, associated⟩ := admitted_origin channelImage bodyImage payloadImage
  obtain ⟨decoded, accepted, value⟩ := signature_decodes channelImage bodyImage payloadImage
  have executed := channelImage.ambient_canonical_entry_path_rhs
    bodyImage payloadImage decoded accepted tailImage ambientImage
  have sourceImage := ambient_receiver_config_image
    channelImage bodyImage payloadImage decoded accepted tailImage ambientImage
  change decoded.val = {signature channelSource bodySource payloadSource} at value
  rw [value] at executed sourceImage
  obtain ⟨sourceFuel, step, target, fuel, parsedSource, publicCatalogue, parsedTarget,
    enabled, located, spent, frame, path, observed⟩ := executed
  obtain ⟨separated, _, _, occurrences⟩ :=
    sourceImage.canonical_candidate_inventory channelImage enabled
  obtain ⟨_, cells, atoms⟩ := sourceImage.canonical_singleton_inventory channelImage enabled spent
  exact ⟨original, associated, sourceFuel, step, target, fuel, parsedSource, publicCatalogue,
    parsedTarget, enabled, located, spent, frame, path, observed, separated, cells, atoms, occurrences⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedLocatedExecution
