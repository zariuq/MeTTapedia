import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationNormalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimePathRefinement

/-!
# Physical resource balance for actual executable firings

The executable source partition retains exact occurrences. Resource separation
excludes purse-bearing communicated code; consequently the contractum introduces
no authority, and the successor replaces only selected purse heads by their tails.
Cell depletion and signing-atom depletion are distinct observations of this same
operation. These results use the existing runtime candidates and paths.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

private theorem decoded_member_separated {config : RawCostConfig}
    (separated : (decodeRawConfig config).ResourceSeparated)
    {term : RawCostTerm} (member : term ∈ config) :
    (decodeCostTerm term).ResourceSeparated := by
  exact List.forall_iff_forall_mem.mp
    ((decodeRawConfig_resourceSeparated_iff config).mp separated) term member

theorem RawIndexedPurse.selected_location_purseFree
    {config : RawCostConfig} {selected : List RawSelectedPurse}
    (separated : (decodeRawConfig config).ResourceSeparated)
    (fromSource : selected.Sublist config.purses)
    {purse : RawSelectedPurse} (member : purse ∈ selected) :
    (decodeCostName purse.location).purseInventory = 0 := by
  have inPurses := fromSource.subset member
  have mapped : purse.toTerm ∈ config.filter RawCostTerm.isActivePurse := by
    rw [← RawCostConfig.purses_map_toTerm config]
    exact List.mem_map.mpr ⟨purse, inPurses, rfl⟩
  have sourceTerm : purse.toTerm ∈ config := (List.mem_filter.mp mapped).1
  exact decoded_member_separated separated sourceTerm

private theorem measure_singleton
    {Measure : Type u} [AddCommMonoid Measure] (weight : CostStack String → Measure)
    (term : CostTerm String) :
    CostConfig.physicalPurseMeasure weight {term} = term.physicalPurseMeasure weight := by
  simp [CostConfig.physicalPurseMeasure]

private theorem measure_decode_coe
    {Measure : Type u} [AddCommMonoid Measure] (weight : CostStack String → Measure)
    (items : List RawCostTerm) :
    CostConfig.physicalPurseMeasure weight ((items : Multiset RawCostTerm).map decodeCostTerm) =
      (decodeRawConfig items).physicalPurseMeasure weight := rfl

private theorem decoded_selected_measure
    {Measure : Type u} [AddCommMonoid Measure] (weight : CostStack String → Measure)
    (selected : List RawSelectedPurse) :
    (decodeRawConfig (selected.map RawIndexedPurse.toTerm)).physicalPurseMeasure weight =
      (selected.map fun purse => weight (.cons (decodeCostSig purse.head)
        (decodeCostStack purse.tail))).sum := by
  simp [decodeRawConfig, CostConfig.physicalPurseMeasure, List.map_map,
    RawIndexedPurse.toTerm, decodeCostTerm, decodeCostStack,
    CostTerm.physicalPurseMeasure, Function.comp_def]

private theorem decoded_tail_measure
    {Measure : Type u} [AddCommMonoid Measure] (weight : CostStack String → Measure)
    (selected : List RawSelectedPurse) :
    (decodeRawConfig (selected.map RawIndexedPurse.toTailTerm)).physicalPurseMeasure weight =
      (selected.map fun purse => weight (decodeCostStack purse.tail)).sum := by
  simp [decodeRawConfig, CostConfig.physicalPurseMeasure, List.map_map,
    RawIndexedPurse.toTailTerm, decodeCostTerm,
    CostTerm.physicalPurseMeasure, Function.comp_def]

/-- An actual enabled candidate has a purse-free contractum and removes exactly
its participant and selected-purse occurrences from the source inventory. -/
theorem runtime_candidate_code_and_source_measure
    {Measure : Type u} [AddCommMonoid Measure] (weight : CostStack String → Measure)
    {config : RawCostConfig} {step : RawRuntimeStep}
    (canonical : config.Canonical)
    (separated : (decodeRawConfig config).ResourceSeparated)
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    (decodeCostTerm step.contractum).PurseFree ∧
      (decodeRawConfig config).physicalPurseMeasure weight =
        (decodeRawConfig (eraseIndices config (step.participantIndices ++
          step.selectedPurses.map RawIndexedPurse.index))).physicalPurseMeasure weight +
        (step.selectedPurses.map fun purse => weight
          (.cons (decodeCostSig purse.head) (decodeCostStack purse.tail))).sum := by
  have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
  rcases runtimeCostCandidatesFromConfig_origin enabled with
    ⟨redex, source, _redexMember, sourceMember, found, candidate⟩ |
      ⟨recv, send, recvSource, sendSource, _recvMember, _sendMember,
        recvMember, sendMember, recvFound, sendFound, candidate⟩
  · simp only [wholeCandidates] at candidate
    obtain ⟨selected, _selectedMember, rfl⟩ := List.mem_map.mp candidate
    have sourceSeparated := decoded_member_separated separated
      (List.fst_mem_of_mem_zipIdx sourceMember)
    have decoded := wholeAt?_decode_source_of_normalized
      (RawCostConfig.normalized_of_mem_zipIdx canonical sourceMember) found
    have sourceZero : (decodeCostTerm source).physicalPurseMeasure weight = 0 := by
      rcases decoded with decoded | decoded <;>
        simp only [decoded, CostTerm.physicalPurseMeasure]
    have free : (decodeCostTerm redex.body).PurseFree ∧
        (decodeCostTerm redex.payload).PurseFree := by
      rcases decoded with decoded | decoded
      · rw [decoded] at sourceSeparated
        exact sourceSeparated.wholeRecvSend_payloads
      · rw [decoded] at sourceSeparated
        exact sourceSeparated.wholeSendRecv_payloads
    constructor
    · apply (RawCostTerm.purseFree_normalize_iff _).mpr
      rw [decodeCostTerm_commSubst]
      exact free.1.substitute free.2 0
    · have partition := whole_source_partition sourceMember found funding.selected_from_config
      have measure := congrArg (fun raw : Multiset RawCostTerm =>
        CostConfig.physicalPurseMeasure weight (raw.map decodeCostTerm)) partition
      simpa only [Multiset.map_add, Multiset.map_singleton,
        CostConfig.physicalPurseMeasure_add, measure_singleton, measure_decode_coe,
        sourceZero, add_zero, decoded_selected_measure] using measure.symm
  · unfold splitCandidates at candidate
    split at candidate
    · obtain ⟨selected, _selectedMember, rfl⟩ := List.mem_map.mp candidate
      have recvSeparated := decoded_member_separated separated
        (List.fst_mem_of_mem_zipIdx recvMember)
      have sendSeparated := decoded_member_separated separated
        (List.fst_mem_of_mem_zipIdx sendMember)
      have decodedRecv := recvAt?_decode_source_of_normalized
        (RawCostConfig.normalized_of_mem_zipIdx canonical recvMember) recvFound
      have decodedSend := sendAt?_decode_source_of_normalized
        (RawCostConfig.normalized_of_mem_zipIdx canonical sendMember) sendFound
      rw [decodedRecv] at recvSeparated
      rw [decodedSend] at sendSeparated
      constructor
      · apply (RawCostTerm.purseFree_normalize_iff _).mpr
        rw [decodeCostTerm_commSubst]
        exact recvSeparated.recv_body.substitute sendSeparated.send_payload 0
      · have partition := split_source_partition recvMember sendMember recvFound sendFound
          funding.selected_from_config
        have measure := congrArg (fun raw : Multiset RawCostTerm =>
          CostConfig.physicalPurseMeasure weight (raw.map decodeCostTerm)) partition
        simpa only [Multiset.map_add, Multiset.map_singleton,
          CostConfig.physicalPurseMeasure_add, measure_singleton, measure_decode_coe,
          decodedRecv, decodedSend, CostTerm.physicalPurseMeasure, add_zero,
          decoded_selected_measure] using measure.symm
    · contradiction

/-- The actual traced successor contains the retained frame, no purses from
the admitted contractum, and exactly the selected purse tails. -/
theorem applyTracedStep_physical_measure
    {Measure : Type u} [AddCommMonoid Measure] (weight : CostStack String → Measure)
    (components : List RawTraceComponent) (step : RawRuntimeStep) (eventId : Nat)
    (free : (decodeCostTerm step.contractum).PurseFree) :
    (decodeRawConfig ((applyTracedStep components step eventId).map RawTraceComponent.term)).physicalPurseMeasure weight =
      (decodeRawConfig (eraseIndices (components.map RawTraceComponent.term)
        (step.participantIndices ++ step.selectedPurses.map RawIndexedPurse.index))).physicalPurseMeasure weight +
      (step.selectedPurses.map fun purse => weight (decodeCostStack purse.tail)).sum := by
  rw [applyTracedStep_terms, decodeRawConfig_stableKeySort]
  have normalizedFree := (RawCostTerm.purseFree_normalize_iff step.contractum).mpr free
  have contractumZero := normalizedFree.components_physicalPurseMeasure_zero weight
  simp only [decodeRawConfig_append, CostConfig.physicalPurseMeasure_add,
    decodeRawConfig_components, contractumZero, add_zero]
  change _ + (decodeRawConfig (step.selectedPurses.map RawIndexedPurse.toTailTerm)).physicalPurseMeasure weight = _
  rw [decoded_tail_measure]

/-- Actual executable forcing preserves the code/resource boundary. -/
theorem applyTracedStep_resourceSeparated
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated)
    (enabled : step ∈ runtimeCostCandidatesFromConfig (components.map RawTraceComponent.term))
    (eventId : Nat) :
    (decodeRawConfig ((applyTracedStep components step eventId).map RawTraceComponent.term)).ResourceSeparated := by
  have free := (runtime_candidate_code_and_source_measure CostStack.cellCount
    canonical.rawConfig separated enabled).1
  have normalizedFree := (RawCostTerm.purseFree_normalize_iff step.contractum).mpr free
  have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
  have sourceSeparated := (decodeRawConfig_resourceSeparated_iff _).mp separated
  have retainedSeparated := eraseIndices_forall sourceSeparated
    (step.participantIndices ++ step.selectedPurses.map RawIndexedPurse.index)
  have contractumSeparated : step.contractum.normalize.components.Forall
      (fun raw => (decodeCostTerm raw).ResourceSeparated) := by
    apply (decodeRawConfig_resourceSeparated_iff _).mp
    rw [decodeRawConfig_components]
    exact normalizedFree.components_resourceSeparated
  have tailSeparated : (step.selectedPurses.map RawIndexedPurse.toTailTerm).Forall
      (fun raw => (decodeCostTerm raw).ResourceSeparated) := by
    rw [List.forall_iff_forall_mem]
    intro raw member
    obtain ⟨purse, purseMember, rfl⟩ := List.mem_map.mp member
    exact RawIndexedPurse.selected_location_purseFree separated
      funding.selected_from_config purseMember
  rw [applyTracedStep_terms, decodeRawConfig_resourceSeparated_iff]
  apply stableKeySort_forall
  simp only [List.forall_append]
  exact ⟨⟨retainedSeparated, contractumSeparated⟩, tailSeparated⟩

private theorem selected_cells_balance : ∀ selected : List RawSelectedPurse,
    (selected.map fun purse => (CostStack.cons (decodeCostSig purse.head)
      (decodeCostStack purse.tail)).cellCount).sum =
    (selected.map fun purse => (decodeCostStack purse.tail).cellCount).sum + selected.length
  | [] => by simp
  | purse :: rest => by
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [selected_cells_balance rest]
      simp only [CostStack.cellCount]
      omega

/-- Each actually selected purse occurrence contributes exactly one consumed
cell, even when its head contains several signature atoms. -/
theorem applyTracedStep_physical_cells_balance
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated)
    (enabled : step ∈ runtimeCostCandidatesFromConfig (components.map RawTraceComponent.term))
    (eventId : Nat) :
    (decodeRawConfig (components.map RawTraceComponent.term)).physicalPurseCells =
      (decodeRawConfig ((applyTracedStep components step eventId).map RawTraceComponent.term)).physicalPurseCells + step.selectedPurses.length := by
  obtain ⟨free, sourceMeasure⟩ := runtime_candidate_code_and_source_measure
    CostStack.cellCount canonical.rawConfig separated enabled
  have targetMeasure := applyTracedStep_physical_measure CostStack.cellCount
    components step eventId free
  unfold CostConfig.physicalPurseCells
  rw [sourceMeasure, targetMeasure, selected_cells_balance]
  omega

/-- Replacing selected heads by tails preserves purse occurrences, including
empty purses. This count is independent of signing-atom and cell depletion. -/
theorem applyTracedStep_physical_purse_occurrences
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated)
    (enabled : step ∈ runtimeCostCandidatesFromConfig (components.map RawTraceComponent.term))
    (eventId : Nat) :
    (decodeRawConfig (components.map RawTraceComponent.term)).physicalPurseOccurrences =
      (decodeRawConfig ((applyTracedStep components step eventId).map RawTraceComponent.term)).physicalPurseOccurrences := by
  obtain ⟨free, sourceMeasure⟩ := runtime_candidate_code_and_source_measure
    (fun _ => (1 : Nat)) canonical.rawConfig separated enabled
  have targetMeasure := applyTracedStep_physical_measure (fun _ => (1 : Nat))
    components step eventId free
  exact sourceMeasure.trans targetMeasure.symm

private theorem selected_stored_balance (selected : List RawSelectedPurse) :
    (selected.map fun purse => (CostStack.cons (decodeCostSig purse.head)
      (decodeCostStack purse.tail)).storedSignatures).sum =
    (selected.map fun purse => (decodeCostStack purse.tail).storedSignatures).sum +
      rawSelectedSpend selected := by
  simp only [CostStack.storedSignatures, List.sum_map_add, rawSelectedSpend,
    decodeCostSig]
  ac_rfl

/-- Exact stored signing atoms decrease by the actual candidate's exact spend;
no numerical price interpretation participates in authority matching. -/
theorem applyTracedStep_stored_signatures_balance
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated)
    (enabled : step ∈ runtimeCostCandidatesFromConfig (components.map RawTraceComponent.term))
    (eventId : Nat) :
    (decodeRawConfig (components.map RawTraceComponent.term)).storedSignatures =
      (decodeRawConfig ((applyTracedStep components step eventId).map RawTraceComponent.term)).storedSignatures + decodeCostSig step.spend := by
  obtain ⟨free, sourceMeasure⟩ := runtime_candidate_code_and_source_measure
    CostStack.storedSignatures canonical.rawConfig separated enabled
  have targetMeasure := applyTracedStep_physical_measure CostStack.storedSignatures
    components step eventId free
  have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
  unfold CostConfig.storedSignatures
  rw [sourceMeasure, targetMeasure, selected_stored_balance, funding.exact_spend]
  change _ + (_ + step.spend.toMultiset) = (_ + _) + step.spend.toMultiset
  ac_rfl

/-- The actual traced successor and the public residual decode to the same
occurrence multiset. The existing proof uses the candidate's exact frame. -/
theorem applyTracedStep_decode_normalizedResidual
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    (canonical : TraceComponentsCanonical components)
    (enabled : step ∈ runtimeCostCandidatesFromConfig (components.map RawTraceComponent.term))
    (eventId : Nat) :
    decodeRawConfig ((applyTracedStep components step eventId).map RawTraceComponent.term) =
      decodeRawConfig step.residual.normalizeConfig := by
  unfold decodeRawConfig
  exact congrArg (Multiset.map decodeCostTerm)
    (applyTracedStep_toMultiset canonical enabled eventId)

/-- Physical balance also holds for the actual runtime's public normalized
residual, without an implication from structural denotation to inventory. -/
theorem runtime_candidate_normalizedResidual_balance
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated)
    (enabled : step ∈ runtimeCostCandidatesFromConfig (components.map RawTraceComponent.term)) :
    (decodeRawConfig step.residual.normalizeConfig).ResourceSeparated ∧
    (decodeRawConfig (components.map RawTraceComponent.term)).physicalPurseCells =
      (decodeRawConfig step.residual.normalizeConfig).physicalPurseCells +
        step.selectedPurses.length ∧
    (decodeRawConfig (components.map RawTraceComponent.term)).storedSignatures =
      (decodeRawConfig step.residual.normalizeConfig).storedSignatures + decodeCostSig step.spend := by
  have decoded := applyTracedStep_decode_normalizedResidual canonical enabled 0
  rw [← decoded]
  exact ⟨applyTracedStep_resourceSeparated canonical separated enabled 0,
    applyTracedStep_physical_cells_balance canonical separated enabled 0,
    applyTracedStep_stored_signatures_balance canonical separated enabled 0⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
