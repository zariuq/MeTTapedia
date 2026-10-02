import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedLocatedExecution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationExecutablePath

/-!
# One physical cell bounds all admitted code continuations

An isolated receiver/sender pair has a commitment computed from its original
source and exactly one physical purse cell. Every actual execution from that
configuration has at most one funded firing. Receiver substitution may copy
or discard signed code; it cannot create the authority for a second firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedSingleCell

open Mettapedia.OSLF.MeTTaIL.Syntax ActivationGenerated
open SourceAssociatedLocatedExecution

def isolated (location : CostName LiteralAuthority) (body payload : CostTerm LiteralAuthority)
    (authority : CostSig LiteralAuthority) : CostTerm LiteralAuthority :=
  decodedAmbientReceiver location body payload authority .empty .nil

theorem initial_cells_eq_one (location : CostName LiteralAuthority)
    (body payload : CostTerm LiteralAuthority) (authority : CostSig LiteralAuthority) :
    (decodeRawConfig ((initialTraceComponents (literalEncodeTerm
      (isolated location body payload authority))).map RawTraceComponent.term)).physicalPurseCells = 1 := by
  change CostConfig.physicalPurseMeasure CostStack.cellCount
    (decodeRawConfig ((initialTraceComponents (literalEncodeTerm
      (isolated location body payload authority))).map RawTraceComponent.term)) = 1
  rw [initialTraceComponents_physical_measure]
  simp [isolated, decodedAmbientReceiver, decodedReceiverSource,
    literalEncodeTerm, decodeCostTerm_encodeCostTerm, CostTerm.relabel,
    locatedContact, CostTerm.components, CostConfig.physicalPurseMeasure,
    CostTerm.physicalPurseMeasure, CostStack.relabel, CostStack.cellCount]

/-- Closed parser-admitted code alone supports no funded firing, even when
its syntax contains sealed communication redexes. -/
theorem unfunded_code_path_depth_eq_zero
    {source : Pattern} {term : CostTerm LiteralAuthority}
    (image : CodeImage 0 source term) {finalId finalComponents}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm term)) finalId finalComponents) :
    path.depth = 0 := by
  have free := image.literal_decoded_purseFree
  apply path.executable_depth_eq_zero_of_no_cells (initialTraceComponents_canonical _)
    (initialTraceComponents_resourceSeparated _ free.components_resourceSeparated)
  change CostConfig.physicalPurseMeasure CostStack.cellCount _ = 0
  rw [initialTraceComponents_physical_measure]
  exact free.components_physicalPurseMeasure_zero CostStack.cellCount

/-- The single-cell bound is inhabited by an actual computed-source firing. -/
theorem exists_one_firing
    {channelSource bodySource payloadSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload) :
    ∃ step,
      step ∈ runtimeCostCandidatesFromConfig (literalEncodeTerm
        (isolated location body payload (authority channelSource bodySource payloadSource))).normalizeConfig ∧
      ∃ path : CostPath 0 (initialTraceComponents (literalEncodeTerm
        (isolated location body payload (authority channelSource bodySource payloadSource)))) 1
        (applyTracedStep (initialTraceComponents (literalEncodeTerm
          (isolated location body payload (authority channelSource bodySource payloadSource)))) step 0),
        path.depth = 1 := by
  obtain ⟨_, _, _, step, _, _, _, _, _, enabled, _, _, _, path, _⟩ :=
    canonical_entry_path_rhs_balance channelImage bodyImage payloadImage StackImage.empty
      (ConfigImage.zero (location := location))
  exact ⟨step, enabled, path⟩

/-- The bound applies to every actual path and every admitted receiver body,
including bodies that duplicate or discard their code argument. -/
theorem every_path_depth_le_one
    {channelSource bodySource payloadSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    {finalId finalComponents}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm
      (isolated location body payload (authority channelSource bodySource payloadSource))))
      finalId finalComponents) : path.depth ≤ 1 := by
  obtain ⟨decoded, accepted, value⟩ := signature_decodes channelImage bodyImage payloadImage
  have sourceImage := ambient_receiver_config_image channelImage bodyImage payloadImage
    decoded accepted StackImage.empty (ConfigImage.zero (location := location))
  rw [value] at sourceImage
  have separated := initialTraceComponents_resourceSeparated _
    (sourceImage.literal_components_resourceSeparated channelImage)
  have bound := path.executable_depth_add_remaining_cells_le
    (initialTraceComponents_canonical _) separated
  rw [initial_cells_eq_one] at bound
  omega

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedSingleCell
