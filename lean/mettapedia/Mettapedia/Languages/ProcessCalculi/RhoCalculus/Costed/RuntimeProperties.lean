import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.Encoding
import Mathlib.Data.Multiset.AddSub
import Mathlib.Tactic

/-!
# Invariants of the independent executable cost-rho runtime

These facts concern the raw traversal algorithm itself.  In particular, exact
cover soundness is proved from list erasure and occurrence-preserving search;
it is not inherited from the declarative `CostStep` relation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

/-! ## Exact signature subtraction and purse covers -/

/-- View a raw canonical signature as the corresponding free commutative
monoid element. -/
def RawCostSig.toMultiset (sig : RawCostSig) : Multiset String := sig

/-- Successful executable subtraction has the expected multiset balance. -/
theorem RawCostSig.subtract_sound {available required remaining : RawCostSig}
    (success : RawCostSig.subtract available required = some remaining) :
    remaining.toMultiset + required.toMultiset = available.toMultiset := by
  induction required generalizing available remaining with
  | nil =>
      simp [RawCostSig.subtract] at success
      subst remaining
      simp [RawCostSig.toMultiset]
  | cons atom rest ih =>
      simp only [RawCostSig.subtract, List.foldlM_cons] at success
      split at success <;> rename_i member
      · have balance := ih success
        have member_multiset : atom ∈ (available : Multiset String) := by
          simpa using member
        have restore :
            RawCostSig.toMultiset (available.erase atom) + {atom} =
              RawCostSig.toMultiset available := by
          change (↑(available.erase atom) : Multiset String) + {atom} =
            (↑available : Multiset String)
          rw [add_comm, Multiset.singleton_add]
          rw [← Multiset.coe_erase]
          exact Multiset.cons_erase member_multiset
        change remaining.toMultiset + (atom :: rest : List String) =
          available.toMultiset
        change remaining.toMultiset +
          (atom ::ₘ RawCostSig.toMultiset rest) =
          available.toMultiset
        calc
          remaining.toMultiset +
              (atom ::ₘ RawCostSig.toMultiset rest) =
              remaining.toMultiset +
                ({atom} + RawCostSig.toMultiset rest) := by
                  rw [Multiset.singleton_add]
          _ =
              (remaining.toMultiset + RawCostSig.toMultiset rest) + {atom} := by
                ac_rfl
          _ = RawCostSig.toMultiset (available.erase atom) + {atom} := by
                rw [balance]
          _ = available.toMultiset := restore
      · simp at success

/-- Executable subtraction succeeds exactly when the required signature is a
submultiset of the available signature. -/
theorem RawCostSig.subtract_complete {available required : RawCostSig}
    (covered : RawCostSig.toMultiset required ≤
      RawCostSig.toMultiset available) :
    ∃ remaining, RawCostSig.subtract available required = some remaining := by
  induction required generalizing available with
  | nil => exact ⟨available, rfl⟩
  | cons atom rest ih =>
      have atom_mem_multiset : atom ∈ RawCostSig.toMultiset available :=
        Multiset.mem_of_le covered (by simp [RawCostSig.toMultiset])
      have atom_mem_list : atom ∈ available := by
        simpa [RawCostSig.toMultiset] using atom_mem_multiset
      have rest_covered : RawCostSig.toMultiset rest ≤
          RawCostSig.toMultiset (available.erase atom) := by
        have erased := Multiset.erase_le_erase atom covered
        simpa [RawCostSig.toMultiset] using erased
      obtain ⟨remaining, success⟩ := ih rest_covered
      refine ⟨remaining, ?_⟩
      simp [RawCostSig.subtract, atom_mem_list, success]

/-- Signature measure of selected executable purse heads. -/
def rawSelectedSpend (selected : List RawSelectedPurse) : Multiset String :=
  (selected.map fun purse => purse.head.toMultiset).sum

/-- A well-formed selected family has zero spend exactly when it is empty. -/
theorem rawSelectedSpend_eq_zero_iff
    {selected : List RawSelectedPurse}
    (valid : selected.Forall fun purse => purse.head.valid = true) :
    rawSelectedSpend selected = 0 ↔ selected = [] := by
  cases selected with
  | nil => simp [rawSelectedSpend]
  | cons purse rest =>
      have valid' :=
        (List.forall_cons (fun candidate : RawSelectedPurse =>
          candidate.head.valid = true) purse rest).mp valid
      constructor
      · intro zero
        have head_zero : purse.head.toMultiset = 0 := by
          apply le_antisymm
          · rw [← zero]
            exact Multiset.le_add_right _ _
          · exact zero_le
        have head_empty : purse.head = [] := by
          simpa [RawCostSig.toMultiset] using head_zero
        simp [RawCostSig.valid, head_empty] at valid'
      · intro impossible
        contradiction

/-- Every exact cover returned by the executable search spends precisely the
demanded multiset. -/
theorem exactPurseCovers_spend_sound
    {demand : RawCostSig} {purses cover : List RawIndexedPurse}
    (member : cover ∈ exactPurseCovers demand purses) :
    rawSelectedSpend cover = demand.toMultiset := by
  induction purses generalizing demand cover with
  | nil =>
      cases empty : demand.isEmpty with
      | false => simp [exactPurseCovers, exactPurseCoversAux, empty] at member
      | true =>
          have demand_nil : demand = [] := List.isEmpty_iff.mp empty
          have cover_nil : cover = [] := by
            simpa [exactPurseCovers, exactPurseCoversAux, empty] using member
          subst demand
          subst cover
          rfl
  | cons purse rest ih =>
      cases empty : demand.isEmpty with
      | true =>
          have demand_nil : demand = [] := List.isEmpty_iff.mp empty
          have cover_nil : cover = [] := by
            simpa [exactPurseCovers, exactPurseCoversAux, empty] using member
          subst demand
          subst cover
          rfl
      | false =>
          cases subtraction : RawCostSig.subtract demand purse.head with
          | none =>
              have skipping : cover ∈ exactPurseCovers demand rest := by
                simpa [exactPurseCovers, exactPurseCoversAux, empty,
                  subtraction] using member
              exact ih skipping
          | some remaining =>
              have alternatives :
                  (∃ subcover ∈ exactPurseCovers remaining rest,
                    purse :: subcover = cover) ∨
                  cover ∈ exactPurseCovers demand rest := by
                simpa [exactPurseCovers, exactPurseCoversAux, empty,
                  subtraction] using member
              rcases alternatives with ⟨subcover, subcover_member, rfl⟩ | skipping
              · have tail_balance := ih subcover_member
                have subtraction_balance :=
                  RawCostSig.subtract_sound subtraction
                simp only [rawSelectedSpend, List.map_cons, List.sum_cons]
                calc
                  purse.head.toMultiset + rawSelectedSpend subcover =
                      remaining.toMultiset + purse.head.toMultiset := by
                        rw [tail_balance]
                        ac_rfl
                  _ = demand.toMultiset := by
                        simpa [add_comm] using subtraction_balance
              · exact ih skipping

/-- Exact cover search never invents a purse occurrence: each returned cover
is a source-order sublist of the available occurrences. -/
theorem exactPurseCovers_sublist
    {demand : RawCostSig} {purses cover : List RawIndexedPurse}
    (member : cover ∈ exactPurseCovers demand purses) :
    cover.Sublist purses := by
  induction purses generalizing demand cover with
  | nil =>
      cases empty : demand.isEmpty with
      | false => simp [exactPurseCovers, exactPurseCoversAux, empty] at member
      | true =>
          have cover_nil : cover = [] := by
            simpa [exactPurseCovers, exactPurseCoversAux, empty] using member
          subst cover
          exact List.nil_sublist _
  | cons purse rest ih =>
      cases empty : demand.isEmpty with
      | true =>
          have cover_nil : cover = [] := by
            simpa [exactPurseCovers, exactPurseCoversAux, empty] using member
          subst cover
          exact List.nil_sublist _
      | false =>
          cases subtraction : RawCostSig.subtract demand purse.head with
          | none =>
              have skipping : cover ∈ exactPurseCovers demand rest := by
                simpa [exactPurseCovers, exactPurseCoversAux, empty,
                  subtraction] using member
              exact (ih skipping).cons purse
          | some remaining =>
              have alternatives :
                  (∃ subcover ∈ exactPurseCovers remaining rest,
                    purse :: subcover = cover) ∨
                  cover ∈ exactPurseCovers demand rest := by
                simpa [exactPurseCovers, exactPurseCoversAux, empty,
                  subtraction] using member
              rcases alternatives with ⟨subcover, subcover_member, rfl⟩ | skipping
              · exact (ih subcover_member).cons_cons purse
              · exact (ih skipping).cons purse

/-- The occurrence-sensitive search enumerates every valid source sublist
whose head signatures cover the demand exactly. -/
theorem exactPurseCovers_complete
    {demand : RawCostSig} {purses cover : List RawIndexedPurse}
    (sublist : cover.Sublist purses)
    (valid : cover.Forall fun purse => purse.head.valid = true)
    (exact : rawSelectedSpend cover = demand.toMultiset) :
    cover ∈ exactPurseCovers demand purses := by
  induction sublist generalizing demand with
  | slnil =>
      have demand_zero : demand.toMultiset = 0 := by
        simpa [rawSelectedSpend] using exact.symm
      have demand_nil : demand = [] := by
        simpa [RawCostSig.toMultiset] using demand_zero
      subst demand
      simp [exactPurseCovers, exactPurseCoversAux]
  | cons purse sublist ih =>
      cases empty : demand.isEmpty with
      | true =>
          have demand_nil : demand = [] := List.isEmpty_iff.mp empty
          have spend_zero := exact
          simp [demand_nil, RawCostSig.toMultiset] at spend_zero
          have cover_nil := (rawSelectedSpend_eq_zero_iff valid).mp spend_zero
          subst demand
          subst_vars
          simp [exactPurseCovers, exactPurseCoversAux]
      | false =>
          have tail_member := ih valid exact
          simp [exactPurseCovers, exactPurseCoversAux, empty, tail_member]
  | @cons_cons chosenTail sourceTail purse sublist ih =>
      have valid' := (List.forall_cons
        (fun candidate : RawSelectedPurse => candidate.head.valid = true)
        purse _).mp valid
      cases empty : demand.isEmpty with
      | true =>
          have demand_nil : demand = [] := List.isEmpty_iff.mp empty
          have spend_zero : rawSelectedSpend (purse :: chosenTail) = 0 := by
            simpa [demand_nil, RawCostSig.toMultiset] using exact
          have impossible := (rawSelectedSpend_eq_zero_iff valid).mp spend_zero
          contradiction
      | false =>
          have head_covered : purse.head.toMultiset ≤ demand.toMultiset := by
            rw [← exact]
            simp only [rawSelectedSpend, List.map_cons, List.sum_cons]
            exact Multiset.le_add_right _ _
          obtain ⟨remaining, subtraction⟩ :=
            RawCostSig.subtract_complete head_covered
          have subtraction_balance := RawCostSig.subtract_sound subtraction
          have tail_exact : rawSelectedSpend chosenTail = remaining.toMultiset := by
            apply add_left_cancel (a := purse.head.toMultiset)
            calc
              purse.head.toMultiset + rawSelectedSpend chosenTail =
                  demand.toMultiset := by
                simpa [rawSelectedSpend] using exact
              _ = remaining.toMultiset + purse.head.toMultiset :=
                subtraction_balance.symm
              _ = purse.head.toMultiset + remaining.toMultiset := add_comm _ _
          have tail_member := ih valid'.2 tail_exact
          simp [exactPurseCovers, exactPurseCoversAux, empty, subtraction,
            tail_member]

theorem mem_matchingPurses_surface {surface : RawCostName}
    {purses : List RawIndexedPurse} {purse : RawIndexedPurse}
    (member : purse ∈ matchingPurses surface purses) :
    purse.surface.normalize = surface.normalize := by
  simp [matchingPurses] at member
  exact member.2

/-- Covers selected after location filtering inherit both occurrence and
location fidelity. -/
theorem exact_matching_cover_sound {surface : RawCostName}
    {demand : RawCostSig} {purses cover : List RawIndexedPurse}
    (member : cover ∈ exactPurseCovers demand (matchingPurses surface purses)) :
    rawSelectedSpend cover = demand.toMultiset ∧
      cover.Sublist purses ∧
      ∀ purse ∈ cover, purse.surface.normalize = surface.normalize := by
  refine ⟨exactPurseCovers_spend_sound member, ?_, ?_⟩
  · exact (exactPurseCovers_sublist member).trans
      List.filter_sublist
  · intro purse purse_member
    have in_filtered := (exactPurseCovers_sublist member).mem purse_member
    exact mem_matchingPurses_surface in_filtered

/-! ## Candidate-firing funding invariants -/

/-- Funding facts retained by one raw executable candidate. -/
structure RawRuntimeStep.FundingValidFor (config : RawCostConfig)
    (step : RawRuntimeStep) : Prop where
  exact_spend : rawSelectedSpend step.selectedPurses = step.spend.toMultiset
  selected_from_config : step.selectedPurses.Sublist config.purses
  selected_at_surface :
    ∀ purse ∈ step.selectedPurses,
      purse.surface.normalize = step.surface.normalize

private theorem wholeCandidates_funding_valid
    {config : RawCostConfig} {purses : List RawIndexedPurse}
    {redex : RawWholeRedex} {step : RawRuntimeStep}
    (member : step ∈ wholeCandidates config purses redex) :
    rawSelectedSpend step.selectedPurses = step.spend.toMultiset ∧
      step.selectedPurses.Sublist purses ∧
      ∀ purse ∈ step.selectedPurses,
        purse.surface.normalize = step.surface.normalize := by
  simp only [wholeCandidates] at member
  obtain ⟨cover, cover_member, rfl⟩ := List.mem_map.mp member
  exact exact_matching_cover_sound cover_member

private theorem splitCandidates_funding_valid
    {config : RawCostConfig} {purses : List RawIndexedPurse}
    {recv : RawRecvEndpoint} {send : RawSendEndpoint}
    {step : RawRuntimeStep}
    (member : step ∈ splitCandidates config purses recv send) :
    rawSelectedSpend step.selectedPurses = step.spend.toMultiset ∧
      step.selectedPurses.Sublist purses ∧
      ∀ purse ∈ step.selectedPurses,
        purse.surface.normalize = step.surface.normalize := by
  unfold splitCandidates at member
  split at member <;> rename_i surfaces_match
  · obtain ⟨cover, cover_member, rfl⟩ := List.mem_map.mp member
    exact exact_matching_cover_sound cover_member
  · contradiction

/-- Every occurrence-sensitive candidate produced by the independent runtime
has exact, located, source-derived funding. -/
theorem runtimeCostCandidatesFromConfig_funding_valid
    {config : RawCostConfig} {step : RawRuntimeStep}
    (member : step ∈ runtimeCostCandidatesFromConfig config) :
    step.FundingValidFor config := by
  simp only [runtimeCostCandidatesFromConfig, List.mem_append] at member
  rcases member with whole | split
  · obtain ⟨redex, _redex_member, step_member⟩ := List.mem_flatMap.mp whole
    obtain ⟨exact_spend, selected, located⟩ :=
      wholeCandidates_funding_valid step_member
    exact ⟨exact_spend, selected, located⟩
  · obtain ⟨recv, _recv_member, send_branch⟩ := List.mem_flatMap.mp split
    obtain ⟨send, _send_member, step_member⟩ := List.mem_flatMap.mp send_branch
    obtain ⟨exact_spend, selected, located⟩ :=
      splitCandidates_funding_valid step_member
    exact ⟨exact_spend, selected, located⟩

@[simp]
theorem RawCostSig.valid_iff_toMultiset_ne_zero (sig : RawCostSig) :
    sig.valid = true ↔ sig.toMultiset ≠ 0 := by
  simp [RawCostSig.valid, RawCostSig.toMultiset]

/-- A valid demanded spend cannot arise from an empty selected cover. -/
theorem RawRuntimeStep.FundingValidFor.no_ambient_funding
    {config : RawCostConfig} {step : RawRuntimeStep}
    (funding : step.FundingValidFor config)
    (spend_valid : step.spend.valid = true) :
    step.selectedPurses ≠ [] := by
  intro selected_empty
  have spend_zero : step.spend.toMultiset = 0 := by
    rw [← funding.exact_spend, selected_empty]
    rfl
  exact (RawCostSig.valid_iff_toMultiset_ne_zero step.spend).mp spend_valid
    spend_zero

/-- Signature measure of raw emitted funding contributions. -/
def rawFundingSpend (funding : List RawFundingContribution) : Multiset String :=
  (funding.map fun contribution => contribution.spend.toMultiset).sum

/-- Event construction preserves one contribution per selected head and its
exact aggregate spend. -/
theorem eventFor_funding_eq_selected_heads
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    {eventId : Nat} {config : RawCostConfig}
    (funding : step.FundingValidFor config) :
    rawFundingSpend (eventFor components step eventId).funding =
      (eventFor components step eventId).rawSpend.toMultiset := by
  have exact := funding.exact_spend
  unfold rawSelectedSpend at exact
  unfold rawFundingSpend eventFor
  simpa only [List.map_map, Function.comp_def] using exact

/-- Every emitted funding entry reports the candidate's actual interaction
surface. -/
theorem eventFor_funding_surface
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    {eventId : Nat} {config : RawCostConfig}
    (funding : step.FundingValidFor config)
    {contribution : RawFundingContribution}
    (member : contribution ∈ (eventFor components step eventId).funding) :
    contribution.surface.normalize = step.surface.normalize := by
  simp only [List.mem_map] at member
  obtain ⟨purse, purse_member, rfl⟩ := member
  exact funding.selected_at_surface purse purse_member

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
