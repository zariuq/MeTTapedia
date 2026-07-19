import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AtomicResourceTryClaim

/-!
# Selected runtime waves

The executable frontier names source occurrences by list index, whereas the
declarative parallel semantics names the corresponding consumed resources.
This module records the exact embedding of each enabled runtime candidate and
shows that a family with globally disjoint claimed indices determines one
`CostMatching`.  No equality of alternative matchings is asserted.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- One enabled runtime candidate together with the exact source occurrences
that decode to its declarative event resources. -/
structure RuntimeEventEmbedding (config : RawCostConfig) where
  step : RawRuntimeStep
  enabled : step ∈ runtimeCostCandidatesFromConfig config
  event : CostedEvent String
  picked : List (RawCostTerm × Nat)
  indices_eq : picked.map Prod.snd = step.consumedIndices
  picked_source : ∀ entry ∈ picked, entry ∈ config.zipIdx
  consumed_eq : decodeRawConfig (picked.map Prod.fst) = event.consumed

namespace RuntimeEventEmbedding

/-- Source indices consumed by the embedded event. -/
def indices {config : RawCostConfig}
    (embedding : RuntimeEventEmbedding config) : List Nat :=
  embedding.step.consumedIndices

/-- Every enabled candidate owns at least one endpoint occurrence. -/
theorem consumedIndices_ne_nil {config : RawCostConfig}
    {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    step.consumedIndices ≠ [] := by
  rcases runtimeCostCandidatesFromConfig_origin enabled with
    ⟨redex, source, _redex_member, _source_mem, _found, step_member⟩ |
      ⟨recv, send, recvSource, sendSource, _recv_member, _send_member,
        _recv_mem, _send_mem, _recv_found, _send_found, step_member⟩
  · simp only [wholeCandidates] at step_member
    obtain ⟨selected, _selected_member, rfl⟩ := List.mem_map.mp step_member
    simp [RawRuntimeStep.consumedIndices]
  · unfold splitCandidates at step_member
    split at step_member
    · obtain ⟨selected, _selected_member, rfl⟩ := List.mem_map.mp step_member
      simp [RawRuntimeStep.consumedIndices]
    · contradiction

/-- Every enabled candidate in a canonical supported configuration has an
exact occurrence embedding into one declarative event. -/
theorem exists_of_enabled {config : RawCostConfig}
    (canonical : config.Canonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    ∃ embedding : RuntimeEventEmbedding config, embedding.step = step := by
  rcases runtimeCostCandidatesFromConfig_origin enabled with
    ⟨redex, source, redex_member, source_mem, found, step_member⟩ |
      ⟨recv, send, recvSource, sendSource, recv_member, send_member,
        recv_mem, send_mem, recv_found, send_found, step_member⟩
  · simp only [wholeCandidates] at step_member
    obtain ⟨selected, _selected_member, step_eq⟩ :=
      List.mem_map.mp step_member
    subst step
    have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
    have surface_fixed := wholeAt?_surface_normalized found
    have located := selectedPurses_surface_eq canonical funding surface_fixed
    have selected_valid : selected.Forall RawIndexedPurse.WellFormed := by
      rw [List.forall_iff_forall_mem]
      intro purse purse_member
      exact RawRuntimeStep.selectedPurse_wellFormed config_ok enabled purse_member
    have redex_ok := List.forall_iff_forall_mem.mp
      (config.wholeRedexes_forall_wellFormed config_ok) redex redex_member
    let cover := decodedSelectedCover redex.surface redex.sig selected
      selected_valid funding.exact_spend
    let selection : FundingSelection String (decodeCostName redex.surface)
        (decodeCostSig redex.sig) :=
      ⟨decodeSelectedHeads selected selected_valid, by
        simpa [cover, decodedSelectedCover] using cover.demand_eq⟩
    let picked := (source, redex.index) :: selectedSourceEntries selected
    have picked_source : ∀ entry ∈ picked, entry ∈ config.zipIdx := by
      intro entry member
      rcases List.mem_cons.mp member with rfl | selected_member
      · exact source_mem
      · exact selectedSourceEntries_source funding.selected_from_config entry
          selected_member
    have selected_components :
        LocatedPurse.configComponents
            (decodedSelectedAvailable redex.surface selected selected_valid) =
          (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
            Multiset (CostTerm String)) :=
      decodedSelectedAvailable_components redex.surface selected selected_valid
        located
    have source_normalized :=
      RawCostConfig.normalized_of_mem_zipIdx canonical source_mem
    rcases wholeAt?_decode_source_of_normalized source_normalized found with
      source_recv_send | source_send_recv
    · let event := CostedEvent.wholeRecvSend
        (decodeCostName redex.surface) (decodeCostTerm redex.body)
        (decodeCostTerm redex.payload) (decodeCostSig redex.sig)
        (decodeCostSig_runtimeValid redex_ok.sig) selection
      refine ⟨{
        step := _
        enabled := enabled
        event := event
        picked := picked
        indices_eq := ?_
        picked_source := picked_source
        consumed_eq := ?_ }, rfl⟩
      · simp [picked, selectedSourceEntries, RawRuntimeStep.consumedIndices]
      · calc
          decodeRawConfig (picked.map Prod.fst) =
              {decodeCostTerm source} +
                (selected.map
                  (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
                    Multiset (CostTerm String)) := by
            simp [picked, selectedSourceEntries, decodeRawConfig,
              Function.comp_def]
          _ = {decodeCostTerm source} +
              LocatedPurse.configComponents
                (decodedSelectedAvailable redex.surface selected
                  selected_valid) := by
            rw [selected_components]
          _ = event.consumed := by
            simp [event, selection, source_recv_send,
              CostedEvent.consumed, CostedEvent.endpoints,
              CostedEvent.fundingBefore, FundingSelection.before,
              decodedSelectedAvailable]
    · let event := CostedEvent.wholeSendRecv
        (decodeCostName redex.surface) (decodeCostTerm redex.body)
        (decodeCostTerm redex.payload) (decodeCostSig redex.sig)
        (decodeCostSig_runtimeValid redex_ok.sig) selection
      refine ⟨{
        step := _
        enabled := enabled
        event := event
        picked := picked
        indices_eq := ?_
        picked_source := picked_source
        consumed_eq := ?_ }, rfl⟩
      · simp [picked, selectedSourceEntries, RawRuntimeStep.consumedIndices]
      · calc
          decodeRawConfig (picked.map Prod.fst) =
              {decodeCostTerm source} +
                (selected.map
                  (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
                    Multiset (CostTerm String)) := by
            simp [picked, selectedSourceEntries, decodeRawConfig,
              Function.comp_def]
          _ = {decodeCostTerm source} +
              LocatedPurse.configComponents
                (decodedSelectedAvailable redex.surface selected
                  selected_valid) := by
            rw [selected_components]
          _ = event.consumed := by
            simp [event, selection, source_send_recv,
              CostedEvent.consumed, CostedEvent.endpoints,
              CostedEvent.fundingBefore, FundingSelection.before,
              decodedSelectedAvailable]
  · unfold splitCandidates at step_member
    split at step_member
    next surfaces_match =>
      obtain ⟨selected, _selected_member, step_eq⟩ :=
        List.mem_map.mp step_member
      subst step
      have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
      have surface_fixed := recvAt?_surface_normalized recv_found
      have located := selectedPurses_surface_eq canonical funding surface_fixed
      have selected_valid : selected.Forall RawIndexedPurse.WellFormed := by
        rw [List.forall_iff_forall_mem]
        intro purse purse_member
        exact RawRuntimeStep.selectedPurse_wellFormed config_ok enabled
          purse_member
      have recv_ok := List.forall_iff_forall_mem.mp
        (config.recvEndpoints_forall_wellFormed config_ok) recv recv_member
      have send_ok := List.forall_iff_forall_mem.mp
        (config.sendEndpoints_forall_wellFormed config_ok) send send_member
      let spend := (recv.sig ++ send.sig).normalize
      have decoded_spend : decodeCostSig spend =
          decodeCostSig recv.sig + decodeCostSig send.sig := by
        change ((recv.sig ++ send.sig).normalize : Multiset String) =
          (recv.sig : Multiset String) + (send.sig : Multiset String)
        rw [RawCostSig.normalize_toMultiset]
        rfl
      let runtimeCover := decodedSelectedCover recv.surface spend selected
        selected_valid funding.exact_spend
      let selection : FundingSelection String (decodeCostName recv.surface)
          (decodeCostSig recv.sig + decodeCostSig send.sig) :=
        ⟨decodeSelectedHeads selected selected_valid, by
          rw [← decoded_spend]
          simpa [runtimeCover, decodedSelectedCover] using
            runtimeCover.demand_eq⟩
      let event := CostedEvent.split (decodeCostName recv.surface)
        (decodeCostTerm recv.body) (decodeCostTerm send.payload)
        (decodeCostSig recv.sig) (decodeCostSig send.sig)
        (decodeCostSig_runtimeValid recv_ok.sig)
        (decodeCostSig_runtimeValid send_ok.sig) selection
      let picked := (recvSource, recv.index) ::
        (sendSource, send.index) :: selectedSourceEntries selected
      have picked_source : ∀ entry ∈ picked, entry ∈ config.zipIdx := by
        intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact recv_mem
        · rcases List.mem_cons.mp member with rfl | selected_member
          · exact send_mem
          · exact selectedSourceEntries_source funding.selected_from_config
              entry selected_member
      have selected_components :
          LocatedPurse.configComponents
              (decodedSelectedAvailable recv.surface selected selected_valid) =
            (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
              Multiset (CostTerm String)) :=
        decodedSelectedAvailable_components recv.surface selected
          selected_valid located
      have recv_normalized :=
        RawCostConfig.normalized_of_mem_zipIdx canonical recv_mem
      have send_normalized :=
        RawCostConfig.normalized_of_mem_zipIdx canonical send_mem
      have recv_source :=
        recvAt?_decode_source_of_normalized recv_normalized recv_found
      have send_source :=
        sendAt?_decode_source_of_normalized send_normalized send_found
      have send_surface_fixed := sendAt?_surface_normalized send_found
      have surfaces_eq : send.surface = recv.surface := by
        calc
          send.surface = send.surface.normalize := send_surface_fixed.symm
          _ = recv.surface.normalize := surfaces_match.symm
          _ = recv.surface := surface_fixed
      refine ⟨{
        step := _
        enabled := enabled
        event := event
        picked := picked
        indices_eq := ?_
        picked_source := picked_source
        consumed_eq := ?_ }, rfl⟩
      · simp [picked, selectedSourceEntries, RawRuntimeStep.consumedIndices]
      · calc
          decodeRawConfig (picked.map Prod.fst) =
              {decodeCostTerm recvSource} + {decodeCostTerm sendSource} +
                (selected.map
                  (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
                    Multiset (CostTerm String)) := by
            simp [picked, selectedSourceEntries, decodeRawConfig,
              Function.comp_def]
          _ = {decodeCostTerm recvSource} + {decodeCostTerm sendSource} +
              LocatedPurse.configComponents
                (decodedSelectedAvailable recv.surface selected
                  selected_valid) := by
            rw [selected_components]
          _ = event.consumed := by
            simp [event, selection,
              recv_source, send_source, surfaces_eq,
              CostedEvent.consumed, CostedEvent.endpoints,
              CostedEvent.fundingBefore, FundingSelection.before,
              decodedSelectedAvailable]
    next => contradiction

end RuntimeEventEmbedding

/-- A runtime-selected wave is a family of enabled candidates whose complete
endpoint-and-funding claim family contains no repeated source occurrence. -/
structure SelectedRuntimeWave (config : RawCostConfig) where
  selected : List (RuntimeEventEmbedding config)
  indices_nodup :
    (selected.flatMap RuntimeEventEmbedding.indices).Nodup

namespace SelectedRuntimeWave

/-- All claimed source indices, in the selected event presentation order. -/
def indices {config : RawCostConfig} (wave : SelectedRuntimeWave config) :
    List Nat :=
  wave.selected.flatMap RuntimeEventEmbedding.indices

/-- All witnessed source entries, in the same event presentation order. -/
def picked {config : RawCostConfig} (wave : SelectedRuntimeWave config) :
    List (RawCostTerm × Nat) :=
  wave.selected.flatMap RuntimeEventEmbedding.picked

/-- Declarative events represented by the selected candidates. -/
def events {config : RawCostConfig} (wave : SelectedRuntimeWave config) :
    List (CostedEvent String) :=
  wave.selected.map RuntimeEventEmbedding.event

/-- One enabled candidate is always a valid selected wave. -/
def singleton {config : RawCostConfig}
    (embedding : RuntimeEventEmbedding config) : SelectedRuntimeWave config where
  selected := [embedding]
  indices_nodup := by
    simpa [RuntimeEventEmbedding.indices] using
      runtimeCostCandidate_consumedIndices_nodup embedding.enabled

/-- Selecting the same occurrence-bearing event twice cannot satisfy the
global claim invariant. -/
theorem duplicate_not_selected {config : RawCostConfig}
    (embedding : RuntimeEventEmbedding config) :
    ¬∃ wave : SelectedRuntimeWave config,
      wave.selected = [embedding, embedding] := by
  rintro ⟨wave, selected_eq⟩
  have indices_nonempty :=
    RuntimeEventEmbedding.consumedIndices_ne_nil embedding.enabled
  obtain ⟨head, tail, indices_eq⟩ := List.exists_cons_of_ne_nil indices_nonempty
  have claimed := wave.indices_nodup
  rw [selected_eq] at claimed
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    RuntimeEventEmbedding.indices] at claimed
  rw [indices_eq] at claimed
  have distinct := (List.nodup_append.mp claimed).2.2
    head (by simp) head (by simp)
  exact distinct rfl

private theorem embeddings_exist {config : RawCostConfig}
    (canonical : config.Canonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true)) :
    ∀ steps : List RawRuntimeStep,
      (∀ step ∈ steps, step ∈ runtimeCostCandidatesFromConfig config) →
      ∃ embeddings : List (RuntimeEventEmbedding config),
        embeddings.map RuntimeEventEmbedding.step = steps
  | [], _ => ⟨[], rfl⟩
  | step :: rest, enabled => by
      obtain ⟨head, head_eq⟩ := RuntimeEventEmbedding.exists_of_enabled
        canonical config_ok (enabled step (by simp))
      have rest_enabled :
          ∀ candidate ∈ rest,
            candidate ∈ runtimeCostCandidatesFromConfig config := by
        intro candidate member
        exact enabled candidate (by simp [member])
      obtain ⟨tail, tail_eq⟩ :=
        embeddings_exist canonical config_ok rest rest_enabled
      refine ⟨head :: tail, ?_⟩
      simp [head_eq, tail_eq]

private theorem embeddings_indices_eq {config : RawCostConfig}
    (embeddings : List (RuntimeEventEmbedding config)) :
    embeddings.flatMap RuntimeEventEmbedding.indices =
      (embeddings.map RuntimeEventEmbedding.step).flatMap
        RawRuntimeStep.consumedIndices := by
  induction embeddings with
  | nil => rfl
  | cons head tail induction =>
      simp [RuntimeEventEmbedding.indices, induction]

/-- Any selected list of enabled candidates whose claimed occurrence family
is globally duplicate-free can be lifted to a declarative selected wave. -/
theorem exists_of_selectedSteps {config : RawCostConfig}
    (canonical : config.Canonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    (steps : List RawRuntimeStep)
    (enabled : ∀ step ∈ steps,
      step ∈ runtimeCostCandidatesFromConfig config)
    (claims_nodup :
      (steps.flatMap RawRuntimeStep.consumedIndices).Nodup) :
    ∃ wave : SelectedRuntimeWave config,
      wave.selected.map RuntimeEventEmbedding.step = steps := by
  obtain ⟨embeddings, steps_eq⟩ :=
    embeddings_exist canonical config_ok steps enabled
  have indices_nodup :
      (embeddings.flatMap RuntimeEventEmbedding.indices).Nodup := by
    rw [embeddings_indices_eq, steps_eq]
    exact claims_nodup
  exact ⟨⟨embeddings, indices_nodup⟩, steps_eq⟩

private theorem picked_indices_aux {config : RawCostConfig} :
    ∀ embeddings : List (RuntimeEventEmbedding config),
      (embeddings.flatMap RuntimeEventEmbedding.picked).map Prod.snd =
        embeddings.flatMap RuntimeEventEmbedding.indices
  | [] => rfl
  | embedding :: rest => by
      simp only [List.flatMap_cons, List.map_append]
      rw [embedding.indices_eq, picked_indices_aux rest]
      rfl

/-- Flattening the per-event source witnesses recovers the claimed indices. -/
theorem picked_indices {config : RawCostConfig}
    (wave : SelectedRuntimeWave config) :
    wave.picked.map Prod.snd = wave.indices := by
  exact picked_indices_aux wave.selected

/-- Every flattened witness entry is an occurrence of the common source. -/
theorem picked_source {config : RawCostConfig}
    (wave : SelectedRuntimeWave config) :
    ∀ entry ∈ wave.picked, entry ∈ config.zipIdx := by
  intro entry member
  obtain ⟨embedding, embedding_member, entry_member⟩ :=
    List.mem_flatMap.mp member
  exact embedding.picked_source entry entry_member

private theorem decode_picked_aux {config : RawCostConfig} :
    ∀ embeddings : List (RuntimeEventEmbedding config),
      decodeRawConfig
          ((embeddings.flatMap RuntimeEventEmbedding.picked).map Prod.fst) =
        (embeddings.map fun embedding => embedding.event.consumed).sum
  | [] => by simp [decodeRawConfig]
  | embedding :: rest => by
      simp only [List.flatMap_cons, List.map_append, List.map_cons,
        List.sum_cons, decodeRawConfig_append]
      rw [embedding.consumed_eq, decode_picked_aux rest]

/-- The complete flattened source witness decodes to the sum of the selected
events' consumed resources. -/
theorem decode_picked {config : RawCostConfig}
    (wave : SelectedRuntimeWave config) :
    decodeRawConfig (wave.picked.map Prod.fst) =
      (wave.events.map CostedEvent.consumed).sum := by
  simpa [picked, events, Function.comp_def] using
    decode_picked_aux wave.selected

/-- Selecting the wave's globally disjoint occurrence indices recovers
exactly the sum of its declarative consumed resources. -/
theorem decode_selectIndices {config : RawCostConfig}
    (wave : SelectedRuntimeWave config) :
    decodeRawConfig (selectIndices config wave.indices) =
      (wave.events.map CostedEvent.consumed).sum := by
  have selected := selectIndices_eq_picked
    (config := config) (indices := wave.indices) (picked := wave.picked)
    wave.picked_indices.symm (by
      rw [wave.picked_indices]
      exact wave.indices_nodup)
    wave.picked_source
  have decoded :
      decodeRawConfig (selectIndices config wave.indices) =
        decodeRawConfig (wave.picked.map Prod.fst) := by
    unfold decodeRawConfig
    exact congrArg (Multiset.map decodeCostTerm) selected
  rw [decoded, wave.decode_picked]

/-- A selected occurrence-disjoint runtime wave determines one fixed
declarative matching in the decoded common source. -/
def toCostMatching {config : RawCostConfig}
    (wave : SelectedRuntimeWave config) : CostMatching String where
  source := decodeRawConfig config
  events := wave.events
  frame := decodeRawConfig (eraseIndices config wave.indices)
  source_eq := by
    have partition := decodeRawConfig_erase_add_select config wave.indices
    rw [wave.decode_selectIndices] at partition
    unfold costWaveSource
    rw [← partition]
    ac_rfl

/-- Every ordering of the selected runtime wave is therefore an ordinary
declarative cost trace with the matching's exact target. -/
theorem permutation_serializes {config : RawCostConfig}
    (wave : SelectedRuntimeWave config)
    {schedule : List (CostedEvent String)}
    (permutation : schedule.Perm wave.events) :
    CostTrace (decodeRawConfig config) (costWaveTrace schedule)
      wave.toCostMatching.target :=
  wave.toCostMatching.permutation_serializes permutation

end SelectedRuntimeWave

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
