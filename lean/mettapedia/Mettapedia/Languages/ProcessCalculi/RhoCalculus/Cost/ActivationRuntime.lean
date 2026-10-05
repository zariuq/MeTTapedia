import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationNormalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimePathRefinement
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeWave

/-!
# Physical resource balance for actual executable firings

The executable source partition retains exact occurrences. Resource separation
excludes purse-bearing communicated code; consequently the contractum introduces
no authority, and the successor replaces only selected purse heads by their tails.

On the purses this is a firing of the purse system: at the location of the step,
the purses it selects are among the purses of the decoded source, and the purses
of the decoded successor are those the firing leaves. Cells, purse occurrences
and stored signing atoms are readouts of the bag of purses, so the balance of
each is the law of the purse system read on it.

The event of an enabled step, which exists when every component is well formed,
is a funded event: it is enabled in the decoded configuration, the purses after
its funded firing are the purses of the decoded successor, and it spends what
the step spends and selects as many purses. The decoded configurations
themselves can differ, since the step adds its contractum normalized and the
event its contractum as substituted. Without well-formedness a step can fire
with no purse, which no funded event does; the balances above hold for such
steps too.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.GSLT.Causality.ResourceInteraction

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

/-- The purses an executable step selects, decoded: each as its top cell and
the cells under it. -/
def RawRuntimeStep.chosenPurses (step : RawRuntimeStep) :
    Multiset (CostSig String × List (CostSig String)) :=
  (step.selectedPurses.map fun purse =>
    (decodeCostSig purse.head, (decodeCostStack purse.tail).toList) : List _)

private theorem decode_coe (items : List RawCostTerm) :
    (items : Multiset RawCostTerm).map decodeCostTerm = decodeRawConfig items := rfl

/-- The decoded selected purses, all at the location of the step, are what the
purse system takes there. -/
private theorem decoded_selected_purses {step : RawRuntimeStep}
    (located : ∀ purse ∈ step.selectedPurses, purse.location = step.location) :
    (decodeRawConfig (step.selectedPurses.map RawIndexedPurse.toTerm)).purses =
      step.chosenPurses.map fun purse => (decodeCostName step.location, purse.1 :: purse.2) := by
  unfold RawRuntimeStep.chosenPurses decodeRawConfig CostConfig.purses
  rw [Multiset.map_coe, Multiset.filterMap_coe, List.map_map, List.map_map, List.filterMap_map]
  refine congrArg _ (List.filterMap_eq_map_iff_forall_eq_some.mpr fun purse member => ?_)
  rw [Function.comp_apply, Function.comp_apply, ← located purse member]
  simp [RawIndexedPurse.toTerm, decodeCostTerm, decodeCostStack, CostTerm.purse?, CostStack.toList]

/-- The decoded tails of the selected purses are what the purse system leaves
at the location of the step. -/
private theorem decoded_tail_purses {step : RawRuntimeStep}
    (located : ∀ purse ∈ step.selectedPurses, purse.location = step.location) :
    (decodeRawConfig (step.selectedPurses.map fun purse =>
        RawCostTerm.purse purse.location purse.tail)).purses =
      step.chosenPurses.map fun purse => (decodeCostName step.location, purse.2) := by
  unfold RawRuntimeStep.chosenPurses decodeRawConfig CostConfig.purses
  rw [Multiset.map_coe, Multiset.filterMap_coe, List.map_map, List.map_map, List.filterMap_map]
  refine congrArg _ (List.filterMap_eq_map_iff_forall_eq_some.mpr fun purse member => ?_)
  rw [Function.comp_apply, Function.comp_apply, ← located purse member]
  simp [decodeCostTerm, CostTerm.purse?]

/-- An enabled candidate has a purse-free contractum, and the purses of its
source are the purses of the occurrences it leaves with the purses it selects. -/
theorem runtime_candidate_code_and_source_purses
    {config : RawCostConfig} {step : RawRuntimeStep}
    (canonical : config.Canonical)
    (separated : (decodeRawConfig config).ResourceSeparated)
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    (decodeCostTerm step.contractum).PurseFree ∧
      (decodeRawConfig config).purses =
        (decodeRawConfig (eraseIndices config step.consumedIndices)).purses +
          (decodeRawConfig (step.selectedPurses.map RawIndexedPurse.toTerm)).purses := by
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
    have sourceNone : CostConfig.purses {decodeCostTerm source} = 0 := by
      rcases decoded with decoded | decoded <;> rw [decoded] <;> rfl
    have free : (decodeCostTerm redex.body).PurseFree ∧
        (decodeCostTerm redex.payload).PurseFree := by
      rcases decoded with decoded | decoded <;> rw [decoded] at sourceSeparated
      · exact sourceSeparated.wholeRecvSend_payloads
      · exact sourceSeparated.wholeSendRecv_payloads
    constructor
    · apply (RawCostTerm.purseFree_normalize_iff _).mpr
      rw [decodeCostTerm_commSubst]
      exact free.1.substitute free.2 0
    · have partition := congrArg (fun raw : Multiset RawCostTerm =>
        CostConfig.purses (raw.map decodeCostTerm))
        (whole_source_partition sourceMember found funding.selected_from_config)
      simpa only [Multiset.map_add, Multiset.map_singleton, CostConfig.purses_add,
        sourceNone, add_zero, decode_coe, RawRuntimeStep.consumedIndices] using partition.symm
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
      · have partition := congrArg (fun raw : Multiset RawCostTerm =>
          CostConfig.purses (raw.map decodeCostTerm))
          (split_source_partition recvMember sendMember recvFound sendFound
            funding.selected_from_config)
        have recvNone : CostConfig.purses {decodeCostTerm recvSource} = 0 := by
          rw [decodedRecv]
          rfl
        have sendNone : CostConfig.purses {decodeCostTerm sendSource} = 0 := by
          rw [decodedSend]
          rfl
        simpa only [Multiset.map_add, Multiset.map_singleton, CostConfig.purses_add,
          recvNone, sendNone, add_zero, decode_coe, RawRuntimeStep.consumedIndices]
          using partition.symm
    · contradiction

/-- **An executable step fires the purse system.** At the location of the step,
the purses it selects are among the purses of the decoded source, and the purses
of the decoded successor are those the firing leaves. -/
theorem applyTracedStep_purses_fire
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated)
    (enabled : step ∈ runtimeCostCandidatesFromConfig (components.map RawTraceComponent.term))
    (eventId : Nat) :
    (pursesMany (CostName String) (CostSig String)).Enables
        (decodeRawConfig (components.map RawTraceComponent.term)).purses
        (site := decodeCostName step.location) step.chosenPurses ∧
      CostConfig.purses (decodeRawConfig
          ((applyTracedStep components step eventId).map RawTraceComponent.term)) =
        (pursesMany (CostName String) (CostSig String)).fire
          (decodeRawConfig (components.map RawTraceComponent.term)).purses
          (site := decodeCostName step.location) step.chosenPurses := by
  obtain ⟨free, source⟩ :=
    runtime_candidate_code_and_source_purses canonical.rawConfig separated enabled
  have located := selectedPurses_location_eq canonical.rawConfig
    (runtimeCostCandidatesFromConfig_funding_valid enabled)
    (runtimeCostCandidatesFromConfig_location_normalized enabled)
  have contractum : (decodeRawConfig step.contractum.normalize.components).purses = 0 := by
    rw [decodeRawConfig_components]
    exact Multiset.card_eq_zero.mp ((CostConfig.physicalPurseOccurrences_eq _).symm.trans
      (((RawCostTerm.purseFree_normalize_iff _).mpr free).components_physicalPurseMeasure_zero _))
  refine ((pursesMany (CostName String) (CostSig String)).enables_fire_iff_frame _ _
    step.chosenPurses rfl).mpr ⟨_, source.trans (by rw [decoded_selected_purses located]; rfl), ?_⟩
  rw [applyTracedStep_terms, decodeRawConfig_stableKeySort, decodeRawConfig_append,
    decodeRawConfig_append, CostConfig.purses_add, CostConfig.purses_add, contractum, add_zero,
    decoded_tail_purses located]
  rfl

/-- Actual executable forcing preserves the code/resource boundary. -/
theorem applyTracedStep_resourceSeparated
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated)
    (enabled : step ∈ runtimeCostCandidatesFromConfig (components.map RawTraceComponent.term))
    (eventId : Nat) :
    (decodeRawConfig ((applyTracedStep components step eventId).map RawTraceComponent.term)).ResourceSeparated := by
  have free := (runtime_candidate_code_and_source_purses canonical.rawConfig separated enabled).1
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
  obtain ⟨present, fired⟩ := applyTracedStep_purses_fire canonical separated enabled eventId
  rw [CostConfig.physicalPurseCells_eq, CostConfig.physicalPurseCells_eq, fired,
    pursesMany_cells _ _ _ present, RawRuntimeStep.chosenPurses, Multiset.coe_card,
    List.length_map]

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
  obtain ⟨present, fired⟩ := applyTracedStep_purses_fire canonical separated enabled eventId
  rw [CostConfig.physicalPurseOccurrences_eq, CostConfig.physicalPurseOccurrences_eq, fired,
    pursesMany_card _ _ _ present]

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
  obtain ⟨present, fired⟩ := applyTracedStep_purses_fire canonical separated enabled eventId
  rw [CostConfig.storedSignatures_eq, CostConfig.storedSignatures_eq, fired,
    pursesMany_cells_taken _ _ _ present, Multiset.sum_add, RawRuntimeStep.chosenPurses,
    Multiset.map_coe, List.map_map, Multiset.sum_coe]
  change _ + rawSelectedSpend step.selectedPurses = _ + step.spend.toMultiset
  rw [(runtimeCostCandidatesFromConfig_funding_valid enabled).exact_spend]

/-- **An executable step is a funded firing, as the purses see it.** On a
canonical, separated configuration, the event of an embedding of an enabled
step is enabled in the decoded configuration; the purses after its funded firing
are the purses of the decoded successor; and it spends what the step spends and
selects as many purses. `RuntimeEventEmbedding.exists_of_enabled` gives such an
embedding for every enabled step when every component is well formed. The
decoded successor and the funded firing can differ in their code: the step adds
its contractum normalized, the event its contractum as substituted. -/
theorem RuntimeEventEmbedding.fire_purses {components : List RawTraceComponent}
    (embedding : RuntimeEventEmbedding (components.map RawTraceComponent.term))
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated)
    (eventId : Nat) :
    (costResourceSystem String).Enables (decodeRawConfig (components.map RawTraceComponent.term))
        (site := embedding.event.location) ⟨embedding.event, rfl⟩ ∧
      CostConfig.purses (decodeRawConfig
          ((applyTracedStep components embedding.step eventId).map RawTraceComponent.term)) =
        CostConfig.purses ((costResourceSystem String).fire
          (decodeRawConfig (components.map RawTraceComponent.term))
          (site := embedding.event.location) ⟨embedding.event, rfl⟩) ∧
      embedding.event.spend = decodeCostSig embedding.step.spend ∧
      embedding.event.funding.chosen.card = embedding.step.selectedPurses.length := by
  have nodup : (embedding.picked.map Prod.snd).Nodup := by
    rw [embedding.indices_eq]
    exact runtimeCostCandidate_consumedIndices_nodup embedding.enabled
  have frame : decodeRawConfig (components.map RawTraceComponent.term) =
      decodeRawConfig (eraseIndices (components.map RawTraceComponent.term)
        embedding.step.consumedIndices) +
        (costResourceSystem String).consume (site := embedding.event.location)
          ⟨embedding.event, rfl⟩ := by
    rw [← decodeRawConfig_erase_add_select (components.map RawTraceComponent.term)
      embedding.step.consumedIndices]
    exact congrArg (_ + ·) (((congrArg (Multiset.map decodeCostTerm)
      (selectIndices_eq_picked embedding.indices_eq.symm nodup embedding.picked_source)).trans
        embedding.consumed_eq).trans
      (costResourceSystem_consume (location := embedding.event.location) ⟨_, rfl⟩).symm)
  have enabled : (costResourceSystem String).Enables
      (decodeRawConfig (components.map RawTraceComponent.term))
      (site := embedding.event.location) ⟨embedding.event, rfl⟩ := by
    change _ + 0 ≤ _
    rw [add_zero, frame]
    exact Multiset.le_add_left _ _
  obtain ⟨present, fired⟩ :=
    applyTracedStep_purses_fire canonical separated embedding.enabled eventId
  have located := selectedPurses_location_eq canonical.rawConfig
    (runtimeCostCandidatesFromConfig_funding_valid embedding.enabled)
    (runtimeCostCandidatesFromConfig_location_normalized embedding.enabled)
  have consumed : (pursesMany (CostName String) (CostSig String)).consume
        (site := embedding.event.location) embedding.event.chosenPurses =
      (pursesMany (CostName String) (CostSig String)).consume
        (site := decodeCostName embedding.step.location) embedding.step.chosenPurses := by
    have both := (congrArg CostConfig.purses frame).symm.trans
      (runtime_candidate_code_and_source_purses canonical.rawConfig separated
        embedding.enabled).2
    rw [CostConfig.purses_add, costResource_consume_purses, decoded_selected_purses located] at both
    exact add_left_cancel both
  have released : embedding.event.contractum.purses = 0 :=
    embedding.event.contractum_purses_eq_zero separated
      (((costResource_enables_iff_le _ _).mp enabled).1.trans (Multiset.filter_le _ _))
  have samePurses : CostConfig.purses (decodeRawConfig
        ((applyTracedStep components embedding.step eventId).map RawTraceComponent.term)) =
      CostConfig.purses ((costResourceSystem String).fire
        (decodeRawConfig (components.map RawTraceComponent.term))
        (site := embedding.event.location) ⟨embedding.event, rfl⟩) := by
    rw [fired, costResource_fire_purses, released, add_zero]
    simp only [System.fire, pursesMany_produce_eq, consumed]
  refine ⟨enabled, samePurses, ?_, ?_⟩
  · have funded := costResource_storedSignatures _ _ enabled
    have none : embedding.event.contractum.storedSignatures = 0 :=
      contractum_physicalPurseMeasure_eq_zero _ separated _ enabled
    rw [none, add_zero, applyTracedStep_stored_signatures_balance canonical separated
      embedding.enabled eventId, CostConfig.storedSignatures_eq, CostConfig.storedSignatures_eq,
      samePurses] at funded
    exact (add_left_cancel funded).symm
  · have funded := costResource_physicalPurseCells _ _ enabled
    have none : embedding.event.contractum.physicalPurseCells = 0 :=
      contractum_physicalPurseMeasure_eq_zero _ separated _ enabled
    rw [none, add_zero, applyTracedStep_physical_cells_balance canonical separated
      embedding.enabled eventId, CostConfig.physicalPurseCells_eq, CostConfig.physicalPurseCells_eq,
      samePurses] at funded
    exact (Nat.add_left_cancel funded).symm

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
