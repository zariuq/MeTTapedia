import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAmbientCanonicalEntry

/-!
# Location and exact-authority controls for canonical generated entry

A nonempty signed process is quoted as a closed channel. Its actual generated
parser image enables a real canonical runtime path. Different canonical
locations and different literal signature atoms block the existing catalogue.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

theorem locatedWhole_wrong_location_blocked (body payload : RawCostTerm)
    {channel purseLocation : RawCostName}
    (different : purseLocation.normalize ≠ channel.normalize)
    (authority : String) (tail : RawCostStack) :
    runtimeCostCandidatesFromConfig
      [.signed (.par (.recv channel body) (.send channel payload)) [authority],
       .purse purseLocation ([authority] :: tail)] = [] := by
  simp [runtimeCostCandidatesFromConfig, RawCostConfig.purses, collectPursesAux,
    RawCostConfig.wholeRedexes, collectWholesAux, wholeAt?, RawCostSig.normalize,
    stableSortBy, stableInsertBy, wholeCandidates, matchingPurses, RawCostName.normalize_idempotent,
    different, exactPurseCovers, exactPurseCoversAux,
    RawCostConfig.recvEndpoints, collectRecvsAux, RawCostConfig.sendEndpoints, collectSendsAux]

theorem locatedWhole_wrong_key_blocked (location : RawCostName) (body payload : RawCostTerm)
    {required available : String} (different : available ≠ required) (tail : RawCostStack) :
    runtimeCostCandidatesFromConfig
      [.signed (.par (.recv location body) (.send location payload)) [required],
       .purse location ([available] :: tail)] = [] := by
  simp [runtimeCostCandidatesFromConfig, RawCostConfig.purses, collectPursesAux,
    RawCostConfig.wholeRedexes, collectWholesAux, wholeAt?, RawCostSig.normalize,
    stableSortBy, stableInsertBy, wholeCandidates, matchingPurses, RawCostName.normalize_idempotent,
    exactPurseCovers, exactPurseCoversAux, RawCostSig.subtract, different,
    RawCostConfig.recvEndpoints, collectRecvsAux, RawCostConfig.sendEndpoints, collectSendsAux]

theorem locatedWhole_wrong_literal_key_blocked (location : RawCostName)
    (body payload : CostTerm LiteralAuthority) {required available : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (different : available ≠ required) (tail : CostStack LiteralAuthority) :
    runtimeCostCandidatesFromConfig
      [.signed (.par (.recv location (literalEncodeTerm body))
        (.send location (literalEncodeTerm payload))) [literalAuthorityKey required],
       .purse location ([literalAuthorityKey available] :: literalEncodeStack tail)] = [] := by
  exact locatedWhole_wrong_key_blocked location _ _
    (fun same => different (literalAuthorityKey_injective same)) _

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationLocatedControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated

def unitSource : Pattern := .apply costSignatureUnitConstructorName []
def emptySource : Pattern := .apply costTokenStackEmptyConstructorName []
def zeroSource : Pattern := .apply (costWrappedConstructorName "PZero") []
def boundBodySource : Pattern := .apply (costWrappedConstructorName "PDrop") [.bvar 0]

def unitTyped : TypedSignature unitSource :=
  ⟨{unitSource}, rfl, checkHasType_sound (by decide +kernel)⟩

theorem unit_accepted : signature? unitSource = some unitTyped := by
  have typed : checkHasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] unitSource
      (.base costSignatureSortName) = true := by decide +kernel
  unfold signature?
  rw [dif_pos typed]
  rfl

def payloadSource : Pattern := .apply costSignedConstructorName
  [.apply (costBaseConstructorName "POutput") [nilChannelSource, zeroSource], unitSource]

def payload : CostTerm LiteralAuthority := .signed (.send nilChannelLocation .nil) {unitSource}

theorem payload_image : CodeImage 0 payloadSource payload :=
  .signed unitTyped unit_accepted (.send .baseZeroQuote .zero)

def channelSource : Pattern := .apply (costWrappedConstructorName "NQuote") [payloadSource]
def channel : CostName LiteralAuthority := .quote payload

theorem channel_image : NameImage 0 channelSource channel := .quote payload_image

theorem closed_nonempty_channel : channel ≠ nilChannelLocation := by
  intro same
  cases same

theorem canonical_channel_distinct :
    (literalEncodeName channel).normalize ≠ occurrenceNilLocation.normalize := by
  have encoded : literalEncodeName channel = RawCostName.quote
      (.signed (.send occurrenceNilLocation .nil) [literalAuthorityKey unitSource]) := by
    change RawCostName.quote (.signed (.send occurrenceNilLocation .nil)
      (encodeCostSig (({unitSource} : CostSig LiteralAuthority).map literalAuthorityKey))) = _
    rw [literalEncodeSig_singleton]
  intro same
  rw [encoded] at same
  simp only [RawCostName.normalize, RawCostTerm.normalize, RawCostProc.normalize,
    RawCostSig.normalize, stableSortBy, occurrenceNilLocation] at same
  cases same

/-- A bound-name receiver transfers a nonempty signed payload at the quoted nonempty channel. -/
theorem actual_closed_location_entry :
    ∃ step,
      step ∈ runtimeCostCandidatesFromConfig
        (literalEncodeTerm (decodedReceiverSource channel (.drop (.bvar 0)) payload
          {unitSource} .empty)).normalizeConfig ∧
      decodeCostName step.location = decodeCostName (literalEncodeName channel).normalize ∧
      decodeCostSig step.spend = {literalAuthorityKey unitSource} ∧
      ∃ path : CostPath 0
          (initialTraceComponents (literalEncodeTerm
            (decodedReceiverSource channel (.drop (.bvar 0)) payload {unitSource} .empty)))
          1 (applyTracedStep (initialTraceComponents (literalEncodeTerm
            (decodedReceiverSource channel (.drop (.bvar 0)) payload {unitSource} .empty))) step 0),
        path.depth = 1 := by
  obtain ⟨_, step, _, _, _, _, _, enabled, located, spent, _, path, _⟩ :=
    channel_image.located_canonical_entry_path_rhs
      (CodeImage.drop (NameImage.bvar (index := 0) (by decide +kernel)))
      payload_image unitTyped unit_accepted StackImage.empty
  exact ⟨step, enabled, located, spent, path⟩

theorem actual_wrong_location_catalogue_empty :
    runtimeCostCandidatesFromConfig
      [.signed (.par (.recv (literalEncodeName channel) (.drop (.bvar 0)))
        (.send (literalEncodeName channel) (literalEncodeTerm payload))) [literalAuthorityKey unitSource],
       .purse occurrenceNilLocation [[literalAuthorityKey unitSource]]] = [] :=
  locatedWhole_wrong_location_blocked _ _ (Ne.symm canonical_channel_distinct) _ []

def productSource : Pattern := .apply costSignatureProductConstructorName [unitSource, unitSource]

theorem product_not_unit : productSource ≠ unitSource := by
  decide +kernel

theorem actual_wrong_key_catalogue_empty :
    runtimeCostCandidatesFromConfig
      [.signed (.par (.recv (literalEncodeName channel) (.drop (.bvar 0)))
        (.send (literalEncodeName channel) (literalEncodeTerm payload))) [literalAuthorityKey unitSource],
       .purse (literalEncodeName channel) [[literalAuthorityKey productSource]]] = [] :=
  locatedWhole_wrong_literal_key_blocked (literalEncodeName channel)
    (.drop (.bvar 0)) payload product_not_unit .empty

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationLocatedControls
