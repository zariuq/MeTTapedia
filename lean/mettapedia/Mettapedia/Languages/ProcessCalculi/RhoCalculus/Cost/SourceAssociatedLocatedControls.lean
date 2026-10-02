import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedLocatedExecution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationLocatedControls

/-!
# Computed source authority at a nonempty quoted channel

The receiver drops its bound name and receives signed payload code. A second
signed payload remains in the ambient frame. The outer authority is computed
from the genuine original pair, and an actual catalogue occurrence consumes
one physical funding cell. A unit-key purse and a purse at the nil channel
cannot authorize that isolated whole firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedLocatedControls

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open ActivationGenerated
open ActivationLocatedControls

def originalKey : Pattern := SourceAssociatedLocatedExecution.signature
  channelSource boundBodySource payloadSource

def framedSource : RawCostTerm := literalEncodeTerm
  (decodedAmbientReceiver channel (.drop (.bvar 0)) payload {originalKey} .empty payload)

theorem actual_nonempty_location_and_frame :
    ∃ step,
      step ∈ runtimeCostCandidatesFromConfig framedSource.normalizeConfig ∧
      decodeCostName step.location = decodeCostName (literalEncodeName channel).normalize ∧
      decodeCostSig step.spend = {literalAuthorityKey originalKey} ∧
      (∃ path : CostPath 0 (initialTraceComponents framedSource) 1
          (applyTracedStep (initialTraceComponents framedSource) step 0), path.depth = 1) ∧
      (decodeRawConfig framedSource.normalizeConfig).physicalPurseCells =
        (decodeRawConfig ((applyTracedStep (initialTraceComponents framedSource) step 0).map
          RawTraceComponent.term)).physicalPurseCells + 1 := by
  obtain ⟨_, _, _, step, _, _, _, _, _, enabled, located, spent, _, path, _, _, cells, _, _⟩ :=
    SourceAssociatedLocatedExecution.canonical_entry_path_rhs_balance channel_image
      (CodeImage.drop (NameImage.bvar (index := 0) (by decide +kernel)))
      payload_image StackImage.empty (payload_image.toConfigImage channel)
  exact ⟨step, enabled, located, spent, path, cells⟩

theorem unit_key_cannot_authorize_original :
    runtimeCostCandidatesFromConfig
      [.signed (.par (.recv (literalEncodeName channel) (.drop (.bvar 0)))
        (.send (literalEncodeName channel) (literalEncodeTerm payload))) [literalAuthorityKey originalKey],
       .purse (literalEncodeName channel) [[literalAuthorityKey unitSource]]] = [] := by
  exact locatedWhole_wrong_literal_key_blocked
    (literalEncodeName channel) (.drop (.bvar 0)) payload
    (required := originalKey) (available := unitSource)
    (SourceAssociatedLocatedExecution.signature_ne_unit
      channelSource boundBodySource payloadSource).symm
    .empty

theorem nil_purse_cannot_authorize_original :
    runtimeCostCandidatesFromConfig
      [.signed (.par (.recv (literalEncodeName channel) (.drop (.bvar 0)))
        (.send (literalEncodeName channel) (literalEncodeTerm payload))) [literalAuthorityKey originalKey],
       .purse occurrenceNilLocation [[literalAuthorityKey originalKey]]] = [] :=
  locatedWhole_wrong_location_blocked _ _ (Ne.symm canonical_channel_distinct) _ []

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedLocatedControls
