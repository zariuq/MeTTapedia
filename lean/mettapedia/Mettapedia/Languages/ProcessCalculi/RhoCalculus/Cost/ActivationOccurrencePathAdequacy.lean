import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrencePathReadout
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrencePathScope
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationWholeOccurrenceRHS
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSplitOccurrenceReadout

/-!
# Occurrencewise adequacy throughout admitted cost execution

Each actual firing retains its source trace, candidate and exact physical
cover. Whole firings have a selected authored R1 representative with the same
ambient frame; split firings use the existing concrete rho rule. The complete
source bag is literal, while the whole authored RHS comparison uses the full
cost structural observer. No path of grouped authored steps is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open ActivationGenerated ActivationGenerated.SerializationAdmission
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Proof-bearing readout of one existing firing occurrence. This predicate
retains the actual old relations, parser images and physical-cover identity;
it supplies no new operational authority. -/
def GeneratedOccurrenceEvidence (location : CostName LiteralAuthority)
    (entry : Nat × List RawTraceComponent × RawRuntimeStep) : Prop :=
  TraceComponentsCanonical entry.2.1 ∧
  (entry.2.1.map RawTraceComponent.term).Forall (ConfigAdmitted (literalEncodeName location).normalize) ∧
  entry.2.2 ∈ runtimeCostCandidatesFromConfig (entry.2.1.map RawTraceComponent.term) ∧
  RuntimeCostStepSound (entry.2.1.map RawTraceComponent.term) entry.2.2 ∧
  ((∃ cover : RawWholeOccurrenceCover (entry.2.1.map RawTraceComponent.term),
    cover.runtimeStep = entry.2.2 ∧
    (∃ signatureSource, ∃ signature : TypedSignature signatureSource,
      ∃ purse tailSource tail,
        signature? signatureSource = some signature ∧
        cover.runtimeStep.spend = [literalAuthorityKey signatureSource] ∧
        cover.runtimeStep.location = (literalEncodeName location).normalize ∧
        cover.runtimeStep.participantIndices = [cover.redex.index] ∧
        cover.runtimeStep.selectedPurses = [purse] ∧
        purse.location = (literalEncodeName location).normalize ∧
        purse.head = [literalAuthorityKey signatureSource] ∧
        StackImage tailSource tail ∧ purse.tail = literalEncodeStack tail) ∧
    (∃ contactSource contactTarget frameSource sourceTerm targetTerm,
      Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
          Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
        rhoCIGSLT.costWholeLanguage contactSource contactTarget ∧
      ConfigImage location (.collection .hashBag [contactSource, frameSource] none) sourceTerm ∧
      ConfigImage location (.collection .hashBag [contactTarget, frameSource] none) targetTerm ∧
      ((literalEncodeTerm sourceTerm).normalizeConfig : Multiset RawCostTerm) =
        (entry.2.1.map RawTraceComponent.term : Multiset RawCostTerm) ∧
      rawConfigStructuralDenote ((applyTracedStep entry.2.1 entry.2.2 entry.1).map RawTraceComponent.term) =
        rawConfigStructuralDenote (literalEncodeTerm targetTerm).normalizeConfig)) ∨
   (∃ cover : RawSplitOccurrenceCover (entry.2.1.map RawTraceComponent.term),
    cover.runtimeStep = entry.2.2 ∧ cover.selected.length = 2 ∧
    ∃ bodySource payloadSource recvSignatureSource sendSignatureSource,
      ∃ (recvSignature : TypedSignature recvSignatureSource) (sendSignature : TypedSignature sendSignatureSource),
        ∃ body payload,
          CodeImage 1 bodySource body ∧ CodeImage 0 payloadSource payload ∧
          signature? recvSignatureSource = some recvSignature ∧
          signature? sendSignatureSource = some sendSignature ∧
          cover.receiver.sig = [literalAuthorityKey recvSignatureSource] ∧
          cover.sender.sig = [literalAuthorityKey sendSignatureSource] ∧
          cover.receiver.body.normalize = (literalEncodeTerm body).normalize ∧
          cover.sender.payload.normalize = (literalEncodeTerm payload).normalize))

theorem CostPath.occurrencewise_generated_adequacy
    {channelSource : Pattern} {location : CostName LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    (canonical : TraceComponentsCanonical components)
    (initialImages : (components.map RawTraceComponent.term).Forall
      (ConfigAdmitted (literalEncodeName location).normalize)) :
    ∀ entry ∈ path.firingEntries, GeneratedOccurrenceEvidence location entry := by
  intro entry member
  obtain ⟨supported, _bounded, enabled⟩ := path.firingEntries_enabled entry member
  obtain ⟨sourceCanonical, images⟩ := path.firingEntries_canonical_admitted canonical initialImages entry member
  refine ⟨sourceCanonical, images, enabled,
    costStep_sound_runtime sourceCanonical.rawConfig supported.toConfig enabled, ?_⟩
  rcases runtime_candidate_exact_occurrence_cover enabled with ⟨cover, same⟩ | ⟨cover, same⟩
  · left
    refine ⟨cover, same, cover.admitted_funding_coordinates channelImage images, ?_⟩
    obtain ⟨contactSource, contactTarget, frameSource, sourceTerm, targetTerm,
      firing, sourceImage, targetImage, sourceBag, targetObserved⟩ :=
      cover.authored_full_rhs channelImage images sourceCanonical.terms sourceCanonical.normalized
    refine ⟨contactSource, contactTarget, frameSource, sourceTerm, targetTerm,
      firing, sourceImage, targetImage, sourceBag, ?_⟩
    rw [applyTracedStep_toMultiset sourceCanonical enabled entry.1, ← same]
    exact targetObserved
  · right
    exact ⟨cover, same, cover.admitted_selected_length_two images, cover.admitted_fields images⟩

namespace ActivationGenerated

/-- A complete actual finite parser-domain execution has every retained
occurrence comparison, an exact endpoint parser readback, and a same-length
pure-base path under the independently licensed erasure encoding. -/
theorem ConfigImage.finite_path_operational_adequacy
    {channelSource source : Pattern} {location : CostName LiteralAuthority}
    {term : CostTerm LiteralAuthority} (channelImage : NameImage 0 channelSource location)
    (image : ConfigImage location source term)
    {finalId : Nat} {finalComponents : List RawTraceComponent}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm term)) finalId finalComponents)
    {signatureName : SignatureNameEncoding String}
    (signatureClosed : signatureName.MapsToClosedRhoNames) :
    ∃ finalSource decoded fuel,
      ∃ finalSafe : (decodeRawConfig (finalComponents.map RawTraceComponent.term)).BinderSafe,
      ∃ purePath : Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT.rhoLanguageDefGSLT.RewritePath
        ((decodeRawConfig ((initialTraceComponents (literalEncodeTerm term)).map RawTraceComponent.term))
          |>.eraseCanonicalProcess signatureClosed image.initial_decoded_binderSafe)
        ((decodeRawConfig (finalComponents.map RawTraceComponent.term))
          |>.eraseCanonicalProcess signatureClosed finalSafe),
        (config? location channelImage.purseInventory_zero channelImage.runtimeSupported fuel finalSource).map
          Subtype.val = some decoded ∧
        ((literalEncodeTerm decoded).normalizeConfig : Multiset RawCostTerm) =
          (finalComponents.map RawTraceComponent.term : Multiset RawCostTerm) ∧
        purePath.length = path.depth ∧
        (∀ entry ∈ path.firingEntries, GeneratedOccurrenceEvidence location entry) := by
  obtain ⟨finalSource, decoded, fuel, parsed, exactReadback⟩ := image.finite_path_parser_readback channelImage path
  obtain ⟨finalSafe, purePath, length⟩ := image.finite_path_base_erasure path signatureClosed
  exact ⟨finalSource, decoded, fuel, finalSafe, purePath, parsed, exactReadback, length,
    path.occurrencewise_generated_adequacy channelImage (initialTraceComponents_canonical _)
      image.initial_serialized_admission⟩

end ActivationGenerated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
