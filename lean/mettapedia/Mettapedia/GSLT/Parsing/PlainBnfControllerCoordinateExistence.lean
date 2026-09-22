import Mettapedia.GSLT.Parsing.PlainBnfControllerPayloadProvenance
import Mathlib.Logic.Function.Basic

/-!
# Existence of the controller's auxiliary coordinate observation

The existing source enumeration embeds each definition position as its full
ranked payload. Injectivity permits a proof-only total extension of the inverse
on that finite image. Admission supplies nonemptiness; the extension is hidden
existentially and is not a runtime decoder for malformed ranks or payloads.

No condition is imposed on the extension outside the actual candidate image.
The existing full-payload provenance theorem makes that behavior unreachable:
any two eligible extensions agree on every live heap occurrence. This module
concerns an auxiliary mathematical observation, not generated or native code.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerCoordinateExistence

open PlainBnfStructuredDiscoveryGraph (Definitions definitionsFromDocument)
open PlainBnfStructuredEnumeration (candidates)
open PlainBnfSourceRank (Rank value successor)
open PlainBnfReverseIndexSourceExecution (Item)
open PlainBnfWakeSourceExecution (HeapItem heapItem Queues contents)

/-- Observation of an existing source-enumeration position, including its
entire name, body, and span. It is not another enumeration implementation. -/
def positionItem (definitions : Definitions) (position : Fin definitions.length) : Item :=
  ((successor^[position.val]) Rank.zero, definitions.get position)

theorem positionItem_rank (definitions : Definitions) (position : Fin definitions.length) :
    value (positionItem definitions position).1 = position.val := by
  simp [positionItem, PlainBnfEnumerationSourceExecution.value_iterate, value]

theorem positionItem_mem (definitions : Definitions) (position : Fin definitions.length) :
    positionItem definitions position ∈ candidates definitions := by
  apply List.mem_map.mpr
  refine ⟨(definitions.get position, position.val), ?_, rfl⟩
  exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simp)

theorem candidate_is_positionItem (definitions : Definitions) (item : Item)
    (member : item ∈ candidates definitions) :
    ∃ position : Fin definitions.length, item = positionItem definitions position := by
  obtain ⟨⟨definition, index⟩, inside, same⟩ := List.mem_map.mp member
  obtain ⟨bound, selected⟩ := List.mem_zipIdx' inside
  subst item
  refine ⟨⟨index, bound⟩, ?_⟩
  exact congrArg (fun body => ((successor^[index]) Rank.zero, body)) selected

theorem position_payload_injective (definitions : Definitions) :
    Function.Injective (fun position => heapItem (positionItem definitions position)) := by
  intro left right same
  have ranks := congrArg (fun payload : HeapItem => value payload.1) same
  apply Fin.ext
  simpa only [heapItem, PlainBnfScheduleSourceExecution.node, positionItem,
    PlainBnfEnumerationSourceExecution.value_iterate, value, Nat.zero_add] using ranks

/-- The finite-image inverse exists for every nonempty definition list.
The arbitrary extension outside that image is local to this proof. -/
theorem coordinate_exists (definitions : Definitions) (nonempty : definitions ≠ []) :
    ∃ coordinate : HeapItem → Fin definitions.length,
      ∀ item ∈ candidates definitions, (coordinate (heapItem item)).val = value item.1 := by
  classical
  have positive : 0 < definitions.length := List.length_pos_iff.mpr nonempty
  let inhabitant : Fin definitions.length := ⟨0, positive⟩
  let embedding := fun position => heapItem (positionItem definitions position)
  have injective : Function.Injective embedding := position_payload_injective definitions
  refine ⟨Function.extend embedding id (fun _ => inhabitant), ?_⟩
  intro item member
  obtain ⟨position, rfl⟩ := candidate_is_positionItem definitions item member
  have exactPosition := injective.extend_apply id (fun _ => inhabitant) position
  change (Function.extend embedding id (fun _ => inhabitant) (embedding position)).val = _
  rw [exactPosition]
  exact (positionItem_rank definitions position).symm

/-- Admission's actual nonempty rule-occurrence condition discharges the
only nonemptiness premise; no additional caller-supplied coordinate is needed. -/
theorem admitted_coordinate_exists (admitted : PlainBnfSemanticAdmission.AdmittedInput) :
    ∃ coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length,
      ∀ item ∈ candidates (definitionsFromDocument admitted.document),
        (coordinate (heapItem item)).val = value item.1 := by
  apply coordinate_exists
  intro empty
  exact admitted.wellFormed.1 (List.map_eq_nil_iff.mp empty)

/-- Any eligible choices agree on every live payload occurrence. In
particular, no off-image extension choice can alter a live coordinate. -/
theorem coordinates_agree_on_live (definitions : Definitions) (queues : Queues)
    (provenance : PlainBnfControllerPayloadProvenance.FromCandidates (candidates definitions) queues)
    (first second : HeapItem → Fin definitions.length)
    (firstRanks : ∀ item ∈ candidates definitions, (first (heapItem item)).val = value item.1)
    (secondRanks : ∀ item ∈ candidates definitions, (second (heapItem item)).val = value item.1) :
    ∀ payload ∈ contents queues, first payload = second payload := by
  intro payload member
  obtain ⟨item, present, rfl⟩ := provenance payload member
  exact Fin.ext ((firstRanks item present).trans (secondRanks item present).symm)

/-- The nonempty hypothesis cannot simply be dropped from a total-extension
statement: the codomain has no position for an empty definition list. -/
theorem empty_definitions_have_no_coordinate (payload : HeapItem) :
    ¬ Nonempty (HeapItem → Fin ([] : Definitions).length) := by
  rintro ⟨coordinate⟩
  exact Fin.elim0 (coordinate payload)

#print axioms position_payload_injective
#print axioms admitted_coordinate_exists
#print axioms coordinates_agree_on_live
#print axioms empty_definitions_have_no_coordinate

end Mettapedia.GSLT.Parsing.PlainBnfControllerCoordinateExistence
