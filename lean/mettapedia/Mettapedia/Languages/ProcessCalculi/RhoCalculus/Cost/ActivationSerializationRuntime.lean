import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSerializationSubstitution

/-!
# Actual runtime successors retain serialized admission

The existing participant collectors expose the admitted receiver and payload.
Actual funding selection retains purse occurrences from the source, so every
selected tail still has its accepted ordered keys at the same fixed location.
The traced successor combines those tails with the admitted communication
contractum and the exact retained source occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission

theorem ConfigAdmitted.whole_code {location : RawCostName} {source : RawCostTerm}
    {index : Nat} {redex : RawWholeRedex} (image : ConfigAdmitted location source)
    (found : wholeAt? index source = some redex) :
    CodeAdmitted 1 redex.body ∧ CodeAdmitted 0 redex.payload := by
  cases image with
  | purse stack => simp [wholeAt?] at found
  | par first second => simp [wholeAt?] at found
  | code image =>
      cases image with
      | zero => simp [wholeAt?] at found
      | drop name => simp [wholeAt?] at found
      | par first second => simp [wholeAt?] at found
      | signed process signature =>
          cases process with
          | zero => simp [wholeAt?] at found
          | send name code => simp [wholeAt?] at found
          | recv name code => simp [wholeAt?] at found
          | par first second =>
              cases first <;> cases second <;> simp [wholeAt?] at found
              all_goals
                obtain ⟨_same, rfl⟩ := found
                constructor <;> assumption

theorem ConfigAdmitted.recv_code {location : RawCostName} {source : RawCostTerm}
    {index : Nat} {endpoint : RawRecvEndpoint} (image : ConfigAdmitted location source)
    (found : recvAt? index source = some endpoint) : CodeAdmitted 1 endpoint.body := by
  cases image with
  | purse stack => simp [recvAt?] at found
  | par first second => simp [recvAt?] at found
  | code image =>
      cases image with
      | zero => simp [recvAt?] at found
      | drop name => simp [recvAt?] at found
      | par first second => simp [recvAt?] at found
      | signed process signature =>
          cases process <;> simp [recvAt?] at found
          subst endpoint
          assumption

theorem ConfigAdmitted.send_code {location : RawCostName} {source : RawCostTerm}
    {index : Nat} {endpoint : RawSendEndpoint} (image : ConfigAdmitted location source)
    (found : sendAt? index source = some endpoint) : CodeAdmitted 0 endpoint.payload := by
  cases image with
  | purse stack => simp [sendAt?] at found
  | par first second => simp [sendAt?] at found
  | code image =>
      cases image with
      | zero => simp [sendAt?] at found
      | drop name => simp [sendAt?] at found
      | par first second => simp [sendAt?] at found
      | signed process signature =>
          cases process <;> simp [sendAt?] at found
          subst endpoint
          assumption

theorem ConfigAdmitted.purse_tail {location purseLocation : RawCostName}
    {head : RawCostSig} {tail : RawCostStack}
    (image : ConfigAdmitted location (.purse purseLocation (head :: tail))) :
    purseLocation = location ∧ StackAdmitted tail := by
  cases image with
  | code image => cases image
  | purse stack =>
      cases stack with
      | cons signature rest => exact ⟨rfl, rest⟩

/-- Participant inversion and actual COMM give an admitted contractum. -/
theorem runtime_candidate_code {location : RawCostName} {config : RawCostConfig}
    {step : RawRuntimeStep} (images : config.Forall (ConfigAdmitted location))
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    CodeAdmitted 0 step.contractum := by
  rcases runtimeCostCandidatesFromConfig_origin enabled with
    ⟨redex, source, _redexMember, sourceMember, found, candidate⟩ |
      ⟨recv, send, recvSource, sendSource, _recvMember, _sendMember,
        recvMember, sendMember, recvFound, sendFound, candidate⟩
  · simp only [wholeCandidates] at candidate
    obtain ⟨selected, _selectedMember, rfl⟩ := List.mem_map.mp candidate
    have sourceImage := List.forall_iff_forall_mem.mp images source
      (List.fst_mem_of_mem_zipIdx sourceMember)
    obtain ⟨body, payload⟩ := sourceImage.whole_code found
    exact body.commSubst_normalize payload
  · unfold splitCandidates at candidate
    split at candidate
    · obtain ⟨selected, _selectedMember, rfl⟩ := List.mem_map.mp candidate
      have recvImage := List.forall_iff_forall_mem.mp images recvSource
        (List.fst_mem_of_mem_zipIdx recvMember)
      have sendImage := List.forall_iff_forall_mem.mp images sendSource
        (List.fst_mem_of_mem_zipIdx sendMember)
      exact (recvImage.recv_code recvFound).commSubst_normalize (sendImage.send_code sendFound)
    · contradiction

theorem selected_tails_admitted {location : RawCostName} {config : RawCostConfig}
    {selected : List RawSelectedPurse} (images : config.Forall (ConfigAdmitted location))
    (fromSource : selected.Sublist config.purses) :
    (selected.map RawIndexedPurse.toTailTerm).Forall (ConfigAdmitted location) := by
  rw [List.forall_iff_forall_mem]
  intro term member
  obtain ⟨purse, purseMember, rfl⟩ := List.mem_map.mp member
  have mapped : purse.toTerm ∈ config.filter RawCostTerm.isActivePurse := by
    rw [← RawCostConfig.purses_map_toTerm config]
    exact List.mem_map.mpr ⟨purse, fromSource.subset purseMember, rfl⟩
  have sourceImage := List.forall_iff_forall_mem.mp images purse.toTerm
    (List.mem_filter.mp mapped).1
  obtain ⟨sameLocation, tail⟩ := ConfigAdmitted.purse_tail sourceImage
  change ConfigAdmitted location (.purse purse.location purse.tail)
  rw [sameLocation]
  exact .purse tail

/-- Every existing enabled occurrence preserves the exact admission invariant. -/
theorem applyTracedStep_admitted {location : RawCostName}
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    (images : (components.map RawTraceComponent.term).Forall (ConfigAdmitted location))
    (enabled : step ∈ runtimeCostCandidatesFromConfig (components.map RawTraceComponent.term))
    (eventId : Nat) :
    ((applyTracedStep components step eventId).map RawTraceComponent.term).Forall
      (ConfigAdmitted location) := by
  have retained := eraseIndices_forall images
    (step.participantIndices ++ step.selectedPurses.map RawIndexedPurse.index)
  have code := (runtime_candidate_code images enabled).normalize.components
  have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
  have tails := selected_tails_admitted images funding.selected_from_config
  rw [applyTracedStep_terms]
  apply stableKeySort_forall
  simp only [List.forall_append]
  exact ⟨⟨retained, code.imp (fun _ image => ConfigAdmitted.code image)⟩, tails⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission
