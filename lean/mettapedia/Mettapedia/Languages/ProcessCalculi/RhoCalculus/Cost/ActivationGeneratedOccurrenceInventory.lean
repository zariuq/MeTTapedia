import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedOccurrencePath
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationLiteralInventory
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimePathRefinement

/-!
# Physical inventory of actual generated occurrence firings

Every participant and selected purse occurrence is accounted for directly.
The emitted code is purse-free and the original ordered tail remains one
located purse. These statements do not require canonical source syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem wholeOccurrenceSuccessor_components (body payload : RawCostTerm) (authority : String)
    (tail : RawCostStack) :
    decodeRawConfig ((applyTracedStep (wholeOccurrenceComponents body payload authority tail)
      (wholeOccurrenceStep body payload authority tail) 0).map RawTraceComponent.term) =
      (decodeCostTerm (wholeOccurrenceStep body payload authority tail).contractum.normalize).components +
        {CostTerm.purse (.quote .nil) (decodeCostStack tail)} := by
  rw [applyTracedStep_terms, wholeOccurrenceComponents_terms, decodeRawConfig_stableKeySort]
  change decodeRawConfig
    (eraseIndices (wholeOccurrenceConfig body payload authority tail) [0, 1] ++
      (wholeOccurrenceStep body payload authority tail).contractum.normalize.components ++
      [RawCostTerm.purse occurrenceNilLocation tail]) = _
  have consumed : eraseIndices (wholeOccurrenceConfig body payload authority tail) [0, 1] = [] := by
    simp [eraseIndices, wholeOccurrenceConfig]
  rw [consumed, List.nil_append, decodeRawConfig_append, decodeRawConfig_components]
  rfl

theorem CodeImage.wholeOccurrenceStep_purseFree {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority} (bodyImage : CodeImage 1 bodySource body)
    (payloadImage : CodeImage 0 payloadSource payload) (authority : Pattern) (tail : CostStack LiteralAuthority) :
    (decodeCostTerm (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey authority) (literalEncodeStack tail)).contractum).PurseFree := by
  obtain ⟨result, fuel, parsed, same⟩ := bodyImage.wholeOccurrenceStep_contractum payloadImage authority tail
  rw [same]
  exact (code_parser_image parsed).literal_normal_decoded_purseFree

theorem wholeOccurrence_initial_measure {Measure : Type*} [AddCommMonoid Measure]
    (weight : CostStack String → Measure) (body payload : RawCostTerm) (authority : String)
    (tail : RawCostStack) :
    (decodeRawConfig (wholeOccurrenceConfig body payload authority tail)).physicalPurseMeasure weight =
      weight (.cons {authority} (decodeCostStack tail)) := by
  simp [wholeOccurrenceConfig, decodeRawConfig, decodeCostTerm, decodeCostStack,
    decodeCostSig, CostConfig.physicalPurseMeasure, CostTerm.physicalPurseMeasure]

theorem CodeImage.wholeOccurrence_final_measure {Measure : Type*} [AddCommMonoid Measure]
    (weight : CostStack String → Measure) {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority} (bodyImage : CodeImage 1 bodySource body)
    (payloadImage : CodeImage 0 payloadSource payload) (authority : Pattern) (tail : CostStack LiteralAuthority) :
    (decodeRawConfig ((applyTracedStep
      (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
        (literalAuthorityKey authority) (literalEncodeStack tail))
      (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
        (literalAuthorityKey authority) (literalEncodeStack tail)) 0).map RawTraceComponent.term)).physicalPurseMeasure weight =
      weight (tail.relabel literalAuthorityKey) := by
  rw [wholeOccurrenceSuccessor_components, CostConfig.physicalPurseMeasure_add]
  have free := bodyImage.wholeOccurrenceStep_purseFree payloadImage authority tail
  have normalizedFree := (RawCostTerm.purseFree_normalize_iff _).mpr free
  rw [normalizedFree.components_physicalPurseMeasure_zero]
  simp [CostConfig.physicalPurseMeasure, CostTerm.physicalPurseMeasure,
    literalEncodeStack, decodeCostStack_encodeCostStack]

theorem CodeImage.wholeOccurrence_cells_balance {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority} (bodyImage : CodeImage 1 bodySource body)
    (payloadImage : CodeImage 0 payloadSource payload) (authority : Pattern) (tail : CostStack LiteralAuthority) :
    (decodeRawConfig (wholeOccurrenceConfig (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey authority) (literalEncodeStack tail))).physicalPurseCells =
      (decodeRawConfig ((applyTracedStep
        (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey authority) (literalEncodeStack tail))
        (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey authority) (literalEncodeStack tail)) 0).map RawTraceComponent.term)).physicalPurseCells + 1 := by
  unfold CostConfig.physicalPurseCells
  rw [wholeOccurrence_initial_measure CostStack.cellCount,
    bodyImage.wholeOccurrence_final_measure CostStack.cellCount payloadImage authority tail]
  simp only [literalEncodeStack, decodeCostStack_encodeCostStack, CostStack.cellCount]

theorem CodeImage.wholeOccurrence_stored_signatures_balance {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority} (bodyImage : CodeImage 1 bodySource body)
    (payloadImage : CodeImage 0 payloadSource payload) (authority : Pattern) (tail : CostStack LiteralAuthority) :
    (decodeRawConfig (wholeOccurrenceConfig (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey authority) (literalEncodeStack tail))).storedSignatures =
      (decodeRawConfig ((applyTracedStep
        (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey authority) (literalEncodeStack tail))
        (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey authority) (literalEncodeStack tail)) 0).map RawTraceComponent.term)).storedSignatures +
        {literalAuthorityKey authority} := by
  unfold CostConfig.storedSignatures
  rw [wholeOccurrence_initial_measure CostStack.storedSignatures,
    bodyImage.wholeOccurrence_final_measure CostStack.storedSignatures payloadImage authority tail]
  simp only [literalEncodeStack, decodeCostStack_encodeCostStack, CostStack.storedSignatures]
  exact add_comm _ _

theorem CodeImage.wholeOccurrence_purse_occurrences {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority} (bodyImage : CodeImage 1 bodySource body)
    (payloadImage : CodeImage 0 payloadSource payload) (authority : Pattern) (tail : CostStack LiteralAuthority) :
    (decodeRawConfig (wholeOccurrenceConfig (literalEncodeTerm body) (literalEncodeTerm payload)
      (literalAuthorityKey authority) (literalEncodeStack tail))).physicalPurseOccurrences =
      (decodeRawConfig ((applyTracedStep
        (wholeOccurrenceComponents (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey authority) (literalEncodeStack tail))
        (wholeOccurrenceStep (literalEncodeTerm body) (literalEncodeTerm payload)
          (literalAuthorityKey authority) (literalEncodeStack tail)) 0).map RawTraceComponent.term)).physicalPurseOccurrences := by
  unfold CostConfig.physicalPurseOccurrences
  rw [wholeOccurrence_initial_measure (fun _ => 1),
    bodyImage.wholeOccurrence_final_measure (fun _ => 1) payloadImage authority tail]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
