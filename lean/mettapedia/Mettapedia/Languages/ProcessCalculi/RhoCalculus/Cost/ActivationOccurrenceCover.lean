import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Bridge

/-!
# Exact selected-cover catalogue correspondence

The occurrence certificates below retain the actual collector source indices
and the selected source-ordered purse occurrences. Their funding contract is
an exact located head sum, independently of candidate enumeration. The
existing cover search enumerates that same selection, and every actual runtime
candidate yields one of these certificates. No new reduction rule is added.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- Exact affordability retains the selected physical occurrences. -/
theorem exact_matching_cover_iff {config : RawCostConfig}
    (wellFormed : config.Forall (fun term => term.wellFormed = true))
    (location : RawCostName) (demand : RawCostSig) (selected : List RawSelectedPurse) :
    selected ∈ exactPurseCovers demand (matchingPurses location config.purses) ↔
      selected.Sublist config.purses ∧
        (∀ purse ∈ selected, purse.location.normalize = location.normalize) ∧
          rawSelectedSpend selected = demand.toMultiset := by
  constructor
  · intro member
    obtain ⟨spent, ordered, located⟩ := exact_matching_cover_sound member
    exact ⟨ordered, located, spent⟩
  · rintro ⟨ordered, located, spent⟩
    have valid : selected.Forall (fun purse => purse.head.valid = true) := by
      rw [List.forall_iff_forall_mem]
      intro purse member
      exact (List.forall_iff_forall_mem.mp
        (RawCostConfig.purses_forall_wellFormed wellFormed) purse (ordered.subset member)).head
    have retained : selected.filter (fun purse => decide
        (purse.location.normalize = location.normalize)) = selected := by
      apply List.filter_eq_self.mpr
      intro purse member
      exact of_decide_eq_true (by simpa using located purse member)
    have matching : selected.Sublist (matchingPurses location config.purses) := by
      unfold matchingPurses
      rw [← retained]
      exact ordered.filter _
    exact exactPurseCovers_complete matching valid spent

/-- A whole redex occurrence and one exact physical funding selection. -/
structure RawWholeOccurrenceCover (config : RawCostConfig) where
  redex : RawWholeRedex
  source : RawCostTerm
  occurrence : (source, redex.index) ∈ config.zipIdx
  found : wholeAt? redex.index source = some redex
  selected : List RawSelectedPurse
  sourceOrdered : selected.Sublist config.purses
  located : ∀ purse ∈ selected, purse.location.normalize = redex.location.normalize
  exactSpend : rawSelectedSpend selected = redex.sig.toMultiset

/-- Two separately sealed occurrences and one exact physical funding selection. -/
structure RawSplitOccurrenceCover (config : RawCostConfig) where
  receiver : RawRecvEndpoint
  sender : RawSendEndpoint
  recvSource : RawCostTerm
  sendSource : RawCostTerm
  recvOccurrence : (recvSource, receiver.index) ∈ config.zipIdx
  sendOccurrence : (sendSource, sender.index) ∈ config.zipIdx
  recvFound : recvAt? receiver.index recvSource = some receiver
  sendFound : sendAt? sender.index sendSource = some sender
  sameLocation : receiver.location.normalize = sender.location.normalize
  selected : List RawSelectedPurse
  sourceOrdered : selected.Sublist config.purses
  located : ∀ purse ∈ selected, purse.location.normalize = receiver.location.normalize
  exactSpend : rawSelectedSpend selected = (receiver.sig ++ sender.sig).normalize.toMultiset

namespace RawWholeOccurrenceCover

/-- Read the existing worker's candidate fields from retained source evidence. -/
def runtimeStep {config : RawCostConfig} (cover : RawWholeOccurrenceCover config) : RawRuntimeStep :=
  let contractum := (cover.redex.body.commSubst cover.redex.payload).normalize
  { shape := match config[cover.redex.index]? with
      | some (.signed (.par (.send _ _) (.recv _ _)) _) => .wholeSendRecv
      | _ => .wholeRecvSend
    location := cover.redex.location
    spend := cover.redex.sig
    participantIndices := [cover.redex.index]
    selectedPurses := cover.selected
    contractum
    residual := residualFor config [cover.redex.index] cover.selected contractum }

/-- The independently stated funding contract enumerates this exact cover. -/
theorem enabled {config : RawCostConfig} (cover : RawWholeOccurrenceCover config)
    (wellFormed : config.Forall (fun term => term.wellFormed = true)) :
    cover.runtimeStep ∈ runtimeCostCandidatesFromConfig config := by
  have selected := (exact_matching_cover_iff wellFormed _ _ _).mpr
    ⟨cover.sourceOrdered, cover.located, cover.exactSpend⟩
  have redexMember := mem_collectWholesAux_of_mem_zipIdx cover.occurrence cover.found
  have candidate : cover.runtimeStep ∈ wholeCandidates config config.purses cover.redex := by
    unfold wholeCandidates
    exact List.mem_map.mpr ⟨cover.selected, selected, rfl⟩
  unfold runtimeCostCandidatesFromConfig
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨cover.redex, redexMember, candidate⟩)

/-- The same selected occurrence yields the existing declarative funded
step, retaining the runtime's explicit structural successor seam. -/
theorem declarative {config : RawCostConfig} (cover : RawWholeOccurrenceCover config)
    (canonical : config.Canonical)
    (wellFormed : config.Forall (fun term => term.wellFormed = true)) :
    RuntimeCostStepSound config cover.runtimeStep :=
  costStep_sound_runtime canonical wellFormed (cover.enabled wellFormed)

@[simp] theorem selected_exact {config : RawCostConfig} (cover : RawWholeOccurrenceCover config) :
    cover.runtimeStep.selectedPurses = cover.selected := rfl

@[simp] theorem participants_exact {config : RawCostConfig} (cover : RawWholeOccurrenceCover config) :
    cover.runtimeStep.participantIndices = [cover.redex.index] := rfl

end RawWholeOccurrenceCover

namespace RawSplitOccurrenceCover

def runtimeStep {config : RawCostConfig} (cover : RawSplitOccurrenceCover config) : RawRuntimeStep :=
  let contractum := (cover.receiver.body.commSubst cover.sender.payload).normalize
  { shape := .split
    location := cover.receiver.location
    spend := (cover.receiver.sig ++ cover.sender.sig).normalize
    participantIndices := [cover.receiver.index, cover.sender.index]
    selectedPurses := cover.selected
    contractum
    residual := residualFor config [cover.receiver.index, cover.sender.index] cover.selected contractum }

theorem enabled {config : RawCostConfig} (cover : RawSplitOccurrenceCover config)
    (wellFormed : config.Forall (fun term => term.wellFormed = true)) :
    cover.runtimeStep ∈ runtimeCostCandidatesFromConfig config := by
  have selected := (exact_matching_cover_iff wellFormed _ _ _).mpr
    ⟨cover.sourceOrdered, cover.located, cover.exactSpend⟩
  have recvMember := mem_collectRecvsAux_of_mem_zipIdx cover.recvOccurrence cover.recvFound
  have sendMember := mem_collectSendsAux_of_mem_zipIdx cover.sendOccurrence cover.sendFound
  have candidate : cover.runtimeStep ∈ splitCandidates config config.purses cover.receiver cover.sender := by
    unfold splitCandidates
    rw [if_pos cover.sameLocation]
    exact List.mem_map.mpr ⟨cover.selected, selected, rfl⟩
  unfold runtimeCostCandidatesFromConfig
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨cover.receiver, recvMember,
    List.mem_flatMap.mpr ⟨cover.sender, sendMember, candidate⟩⟩

/-- Split funding is justified by the concrete rho relation, independently
of the one-rule generated language, which does not declare R2 or R3. -/
theorem declarative {config : RawCostConfig} (cover : RawSplitOccurrenceCover config)
    (canonical : config.Canonical)
    (wellFormed : config.Forall (fun term => term.wellFormed = true)) :
    RuntimeCostStepSound config cover.runtimeStep :=
  costStep_sound_runtime canonical wellFormed (cover.enabled wellFormed)

@[simp] theorem selected_exact {config : RawCostConfig} (cover : RawSplitOccurrenceCover config) :
    cover.runtimeStep.selectedPurses = cover.selected := rfl

@[simp] theorem participants_exact {config : RawCostConfig} (cover : RawSplitOccurrenceCover config) :
    cover.runtimeStep.participantIndices = [cover.receiver.index, cover.sender.index] := rfl

end RawSplitOccurrenceCover

/-- Actual catalogue membership inverts to the same participant and purse
indices, with no replacement by an equivalent selection. -/
theorem runtime_candidate_exact_occurrence_cover {config : RawCostConfig} {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    (∃ cover : RawWholeOccurrenceCover config, cover.runtimeStep = step) ∨
      (∃ cover : RawSplitOccurrenceCover config, cover.runtimeStep = step) := by
  have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
  rcases runtimeCostCandidatesFromConfig_origin enabled with
    ⟨redex, source, _redexMember, sourceMember, found, candidate⟩ |
      ⟨recv, send, recvSource, sendSource, _recvMember, _sendMember,
        recvMember, sendMember, recvFound, sendFound, candidate⟩
  · simp only [wholeCandidates] at candidate
    obtain ⟨selected, _selectedMember, rfl⟩ := List.mem_map.mp candidate
    exact .inl ⟨⟨redex, source, sourceMember, found, selected,
      funding.selected_from_config, funding.selected_at_location, funding.exact_spend⟩, rfl⟩
  · unfold splitCandidates at candidate
    split at candidate
    · rename_i sameLocation
      obtain ⟨selected, _selectedMember, rfl⟩ := List.mem_map.mp candidate
      exact .inr ⟨⟨recv, send, recvSource, sendSource, recvMember, sendMember,
        recvFound, sendFound, sameLocation, selected, funding.selected_from_config,
        funding.selected_at_location, funding.exact_spend⟩, rfl⟩
    · contradiction

/-- Algorithmic completeness and soundness preserve the same physical cover. -/
theorem runtime_candidate_iff_exact_occurrence_cover {config : RawCostConfig}
    (wellFormed : config.Forall (fun term => term.wellFormed = true)) (step : RawRuntimeStep) :
    step ∈ runtimeCostCandidatesFromConfig config ↔
      (∃ cover : RawWholeOccurrenceCover config, cover.runtimeStep = step) ∨
        (∃ cover : RawSplitOccurrenceCover config, cover.runtimeStep = step) := by
  constructor
  · exact runtime_candidate_exact_occurrence_cover
  · rintro (⟨cover, rfl⟩ | ⟨cover, rfl⟩) <;> exact cover.enabled wellFormed

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
