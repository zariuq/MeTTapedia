import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.BudgetedCover

/-!
# Budgeted occurrence-sensitive cost-rho execution

This module lifts budgeted exact-cover search to the canonical runtime task
order.  Reduction fuel and cover-search work are separate resources.  No
frontier search is attempted after reduction fuel reaches zero, and exhausting
search work is represented independently from quiescence.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

/-- One potential operational redex before funding-cover search. -/
inductive RawRuntimeTask where
  | whole (redex : RawWholeRedex)
  | split (recv : RawRecvEndpoint) (send : RawSendEndpoint)
  deriving Repr, DecidableEq

/-- Canonical task order: whole redexes first, followed by the recv-major,
send-minor split endpoint product used by the independent runtime. -/
def runtimeCandidateTasks (config : RawCostConfig) : List RawRuntimeTask :=
  config.wholeRedexes.map .whole ++
    config.recvEndpoints.flatMap fun recv =>
      config.sendEndpoints.map (.split recv)

/-- Construct a whole-redex transition from one exact concrete cover. -/
def wholeStepForCover (config : RawCostConfig) (redex : RawWholeRedex)
    (cover : List RawIndexedPurse) : RawRuntimeStep :=
  let contractum := RawCostTerm.commSubst redex.body redex.payload |>.normalize
  { shape :=
      match config[redex.index]? with
      | some (.signed (.par (.send _ _) (.recv _ _)) _) => .wholeSendRecv
      | _ => .wholeRecvSend
    surface := redex.surface
    spend := redex.sig
    participantIndices := [redex.index]
    selectedPurses := cover
    contractum
    residual := residualFor config [redex.index] cover contractum }

/-- Construct a split-endpoint transition from one exact concrete cover. -/
def splitStepForCover (config : RawCostConfig) (recv : RawRecvEndpoint)
    (send : RawSendEndpoint) (cover : List RawIndexedPurse) : RawRuntimeStep :=
  let spend := (recv.sig ++ send.sig).normalize
  let contractum := RawCostTerm.commSubst recv.body send.payload |>.normalize
  { shape := .split
    surface := recv.surface
    spend
    participantIndices := [recv.index, send.index]
    selectedPurses := cover
    contractum
    residual := residualFor config [recv.index, send.index] cover contractum }

/-- Eager denotation of one redex task, used only as the relational
specification for the budgeted task machine. -/
def RawRuntimeTask.denote (config : RawCostConfig)
    (purses : List RawIndexedPurse) : RawRuntimeTask → List RawRuntimeStep
  | .whole redex => wholeCandidates config purses redex
  | .split recv send => splitCandidates config purses recv send

/-- A first-candidate verdict with unused shared search allowance. -/
inductive RuntimeCandidateDecision where
  | found (step : RawRuntimeStep)
  | noCandidate
  | searchExhausted
  deriving Repr, DecidableEq

structure MeteredRuntimeCandidate where
  decision : RuntimeCandidateDecision
  remainingBudget : Nat
  deriving Repr, DecidableEq

/-- Search canonical redex tasks for one funded transition.  Inspecting a task
costs one unit; its exact-cover frames consume the remainder through
`CoverCursor.seekMetered`. -/
def seekRuntimeTasks (config : RawCostConfig)
    (purses : List RawIndexedPurse) :
    List RawRuntimeTask → Nat → MeteredRuntimeCandidate
  | [], budget => ⟨.noCandidate, budget⟩
  | _ :: _, 0 => ⟨.searchExhausted, 0⟩
  | task :: rest, budget + 1 =>
      match task with
      | .whole redex =>
          let coverResult :=
            (CoverCursor.initial redex.sig
              (matchingPurses redex.surface purses)).seekMetered budget
          match coverResult.decision with
          | .found cover _ =>
              ⟨.found (wholeStepForCover config redex cover),
                coverResult.remainingBudget⟩
          | .noCover =>
              seekRuntimeTasks config purses rest
                coverResult.remainingBudget
          | .searchExhausted _ =>
              ⟨.searchExhausted, coverResult.remainingBudget⟩
      | .split recv send =>
          if _surfacesMatch :
              recv.surface.normalize = send.surface.normalize then
            let spend := (recv.sig ++ send.sig).normalize
            let coverResult :=
              (CoverCursor.initial spend
                (matchingPurses recv.surface purses)).seekMetered budget
            match coverResult.decision with
            | .found cover _ =>
                ⟨.found (splitStepForCover config recv send cover),
                  coverResult.remainingBudget⟩
            | .noCover =>
                seekRuntimeTasks config purses rest
                  coverResult.remainingBudget
            | .searchExhausted _ =>
                ⟨.searchExhausted, coverResult.remainingBudget⟩
          else
            seekRuntimeTasks config purses rest budget

/-- Search one normalized configuration for its first occurrence-sensitive
funded transition. -/
def budgetedFirstRuntimeCandidate (searchBudget : Nat)
    (config : RawCostConfig) : MeteredRuntimeCandidate :=
  seekRuntimeTasks config config.purses (runtimeCandidateTasks config)
    searchBudget

/-! ## Candidate-search refinement -/

theorem wholeStepForCover_mem
    {config : RawCostConfig} {purses : List RawIndexedPurse}
    {redex : RawWholeRedex} {cover : List RawIndexedPurse}
    (coverMember : cover ∈ exactPurseCovers redex.sig
      (matchingPurses redex.surface purses)) :
    wholeStepForCover config redex cover ∈
      wholeCandidates config purses redex := by
  unfold wholeCandidates
  apply List.mem_map.mpr
  exact ⟨cover, coverMember, rfl⟩

theorem splitStepForCover_mem
    {config : RawCostConfig} {purses : List RawIndexedPurse}
    {recv : RawRecvEndpoint} {send : RawSendEndpoint}
    {cover : List RawIndexedPurse}
    (surfacesMatch : recv.surface.normalize = send.surface.normalize)
    (coverMember : cover ∈ exactPurseCovers
      ((recv.sig ++ send.sig).normalize)
      (matchingPurses recv.surface purses)) :
    splitStepForCover config recv send cover ∈
      splitCandidates config purses recv send := by
  unfold splitCandidates
  split
  · simp only [List.mem_map]
    exact ⟨cover, coverMember, rfl⟩
  · contradiction

/-- Every candidate found under a finite search allowance belongs to the eager
task denotation; search exhaustion proves no negative fact. -/
theorem seekRuntimeTasks_found_sound
    {config : RawCostConfig} {purses : List RawIndexedPurse}
    {tasks : List RawRuntimeTask} {budget remaining : Nat}
    {step : RawRuntimeStep}
    (found : seekRuntimeTasks config purses tasks budget =
      ⟨.found step, remaining⟩) :
    step ∈ tasks.flatMap (RawRuntimeTask.denote config purses) := by
  induction tasks generalizing budget remaining with
  | nil =>
      simp [seekRuntimeTasks] at found
  | cons task rest ih =>
      cases budget with
      | zero => simp [seekRuntimeTasks] at found
      | succ budget =>
          cases task with
          | whole redex =>
              cases cover_eq :
                (CoverCursor.initial redex.sig
                  (matchingPurses redex.surface purses)).seekMetered budget with
              | mk decision coverRemaining =>
                  cases decision with
                  | noCover =>
                      simp only [seekRuntimeTasks, cover_eq] at found
                      exact List.mem_append_right _ (ih found)
                  | searchExhausted cursor =>
                      simp [seekRuntimeTasks, cover_eq] at found
                  | found cover cursor =>
                      have foundEq :
                          MeteredRuntimeCandidate.mk
                              (.found (wholeStepForCover config redex cover))
                              coverRemaining =
                            MeteredRuntimeCandidate.mk (.found step) remaining := by
                        simpa [seekRuntimeTasks, cover_eq] using found
                      cases foundEq
                      apply List.mem_append_left
                      apply wholeStepForCover_mem
                      apply CoverCursor.seek_initial_found_sound
                      have verdict := CoverCursor.seekMetered_decision budget
                        (CoverCursor.initial redex.sig
                          (matchingPurses redex.surface purses))
                      rw [cover_eq] at verdict
                      exact verdict.symm
          | split recv send =>
              by_cases surfacesMatch :
                  recv.surface.normalize = send.surface.normalize
              · cases cover_eq :
                  (CoverCursor.initial ((recv.sig ++ send.sig).normalize)
                    (matchingPurses recv.surface purses)).seekMetered budget with
                | mk decision coverRemaining =>
                    cases decision with
                    | noCover =>
                        rw [seekRuntimeTasks] at found
                        simp only [dif_pos surfacesMatch] at found
                        rw [cover_eq] at found
                        exact List.mem_append_right _ (ih found)
                    | searchExhausted cursor =>
                        rw [seekRuntimeTasks] at found
                        simp only [dif_pos surfacesMatch] at found
                        rw [cover_eq] at found
                        simp at found
                    | found cover cursor =>
                        have foundEq :
                            MeteredRuntimeCandidate.mk
                                (.found
                                  (splitStepForCover config recv send cover))
                                coverRemaining =
                              MeteredRuntimeCandidate.mk (.found step)
                                remaining := by
                          rw [seekRuntimeTasks] at found
                          simp only [dif_pos surfacesMatch] at found
                          rw [cover_eq] at found
                          exact found
                        cases foundEq
                        apply List.mem_append_left
                        apply splitStepForCover_mem surfacesMatch
                        apply CoverCursor.seek_initial_found_sound
                        have verdict := CoverCursor.seekMetered_decision budget
                          (CoverCursor.initial
                            ((recv.sig ++ send.sig).normalize)
                            (matchingPurses recv.surface purses))
                        rw [cover_eq] at verdict
                        exact verdict.symm
              · rw [seekRuntimeTasks] at found
                simp only [dif_neg surfacesMatch] at found
                exact List.mem_append_right _ (ih found)

/-- Runtime-task search never creates candidate-search allowance. -/
theorem seekRuntimeTasks_remaining_le
    (config : RawCostConfig) (purses : List RawIndexedPurse)
    (tasks : List RawRuntimeTask) (budget : Nat) :
    (seekRuntimeTasks config purses tasks budget).remainingBudget ≤ budget := by
  induction tasks generalizing budget with
  | nil => simp [seekRuntimeTasks]
  | cons task rest ih =>
      cases budget with
      | zero => simp [seekRuntimeTasks]
      | succ budget =>
          cases task with
          | whole redex =>
              cases cover_eq :
                (CoverCursor.initial redex.sig
                  (matchingPurses redex.surface purses)).seekMetered budget with
              | mk decision coverRemaining =>
                  have cover_le : coverRemaining ≤ budget := by
                    have bound := CoverCursor.seekMetered_remaining_le budget
                      (CoverCursor.initial redex.sig
                        (matchingPurses redex.surface purses))
                    simpa [cover_eq] using bound
                  cases decision with
                  | found cover cursor =>
                      simp [seekRuntimeTasks, cover_eq]
                      omega
                  | searchExhausted cursor =>
                      simp [seekRuntimeTasks, cover_eq]
                      omega
                  | noCover =>
                      have recursive := ih coverRemaining
                      simp only [seekRuntimeTasks, cover_eq]
                      omega
          | split recv send =>
              by_cases surfacesMatch :
                  recv.surface.normalize = send.surface.normalize
              · cases cover_eq :
                  (CoverCursor.initial ((recv.sig ++ send.sig).normalize)
                    (matchingPurses recv.surface purses)).seekMetered budget with
                | mk decision coverRemaining =>
                    have cover_le : coverRemaining ≤ budget := by
                      have bound := CoverCursor.seekMetered_remaining_le budget
                        (CoverCursor.initial
                          ((recv.sig ++ send.sig).normalize)
                          (matchingPurses recv.surface purses))
                      rw [cover_eq] at bound
                      exact bound
                    rw [seekRuntimeTasks]
                    simp only [dif_pos surfacesMatch]
                    rw [cover_eq]
                    cases decision with
                    | found cover cursor =>
                        simp only
                        omega
                    | searchExhausted cursor =>
                        simp only
                        omega
                    | noCover =>
                        have recursive := ih coverRemaining
                        change
                          (seekRuntimeTasks config purses rest
                            coverRemaining).remainingBudget ≤ budget + 1
                        omega
              · have recursive := ih budget
                simp only [seekRuntimeTasks, dif_neg surfacesMatch]
                omega

/-- `noCandidate` is returned only after every task and every funding cover
has been inspected.  It therefore proves the eager candidate relation empty. -/
theorem seekRuntimeTasks_noCandidate_denote_empty
    {config : RawCostConfig} {purses : List RawIndexedPurse}
    {tasks : List RawRuntimeTask} {budget remaining : Nat}
    (absent : seekRuntimeTasks config purses tasks budget =
      ⟨RuntimeCandidateDecision.noCandidate, remaining⟩) :
    tasks.flatMap (RawRuntimeTask.denote config purses) = [] := by
  induction tasks generalizing budget remaining with
  | nil => simp
  | cons task rest ih =>
      cases budget with
      | zero => simp [seekRuntimeTasks] at absent
      | succ budget =>
          cases task with
          | whole redex =>
              cases cover_eq :
                (CoverCursor.initial redex.sig
                  (matchingPurses redex.surface purses)).seekMetered budget with
              | mk decision coverRemaining =>
                  cases decision with
                  | found cover cursor =>
                      simp [seekRuntimeTasks, cover_eq] at absent
                  | searchExhausted cursor =>
                      simp [seekRuntimeTasks, cover_eq] at absent
                  | noCover =>
                      have cover_empty : exactPurseCovers redex.sig
                          (matchingPurses redex.surface purses) = [] := by
                        have denotation :=
                          CoverCursor.seekMetered_noCover_denote_empty cover_eq
                        simpa only [CoverCursor.denote_initial] using denotation
                      have rest_absent :
                          seekRuntimeTasks config purses rest coverRemaining =
                            ⟨RuntimeCandidateDecision.noCandidate, remaining⟩ := by
                        simpa [seekRuntimeTasks, cover_eq] using absent
                      have rest_empty := ih rest_absent
                      simp [RawRuntimeTask.denote, wholeCandidates,
                        cover_empty, rest_empty]
          | split recv send =>
              by_cases surfacesMatch :
                  recv.surface.normalize = send.surface.normalize
              · cases cover_eq :
                  (CoverCursor.initial ((recv.sig ++ send.sig).normalize)
                    (matchingPurses recv.surface purses)).seekMetered budget with
                | mk decision coverRemaining =>
                    rw [seekRuntimeTasks] at absent
                    simp only [dif_pos surfacesMatch] at absent
                    rw [cover_eq] at absent
                    cases decision with
                    | found cover cursor =>
                        simp at absent
                    | searchExhausted cursor =>
                        simp at absent
                    | noCover =>
                        have cover_empty : exactPurseCovers
                            ((recv.sig ++ send.sig).normalize)
                            (matchingPurses recv.surface purses) = [] := by
                          have denotation :=
                            CoverCursor.seekMetered_noCover_denote_empty cover_eq
                          simpa only [CoverCursor.denote_initial] using denotation
                        have rest_absent :
                            seekRuntimeTasks config purses rest coverRemaining =
                              ⟨RuntimeCandidateDecision.noCandidate,
                                remaining⟩ := by
                          exact absent
                        have rest_empty := ih rest_absent
                        simp only [List.flatMap_cons,
                          RawRuntimeTask.denote]
                        rw [splitCandidates, if_pos surfacesMatch]
                        dsimp only
                        rw [cover_empty, rest_empty]
                        simp
              · have rest_absent :
                    seekRuntimeTasks config purses rest budget =
                      ⟨RuntimeCandidateDecision.noCandidate, remaining⟩ := by
                  simpa [seekRuntimeTasks, dif_neg surfacesMatch] using absent
                have rest_empty := ih rest_absent
                simp [RawRuntimeTask.denote, splitCandidates, surfacesMatch,
                  rest_empty]

theorem runtimeCandidateTasks_denote (config : RawCostConfig) :
    (runtimeCandidateTasks config).flatMap
        (RawRuntimeTask.denote config config.purses) =
      runtimeCostCandidatesFromConfig config := by
  simp [runtimeCandidateTasks, RawRuntimeTask.denote,
    runtimeCostCandidatesFromConfig, List.flatMap_map, List.flatMap_assoc]

/-- The budgeted first candidate refines the independent executable runtime
relation. -/
theorem budgetedFirstRuntimeCandidate_found_sound
    {searchBudget remaining : Nat} {config : RawCostConfig}
    {step : RawRuntimeStep}
    (found : budgetedFirstRuntimeCandidate searchBudget config =
      ⟨.found step, remaining⟩) :
    step ∈ runtimeCostCandidatesFromConfig config := by
  rw [← runtimeCandidateTasks_denote config]
  exact seekRuntimeTasks_found_sound found

/-- A public exhaustive negative verdict is an exact quiescence certificate
for the independent executable runtime relation. -/
theorem budgetedFirstRuntimeCandidate_noCandidate
    {searchBudget remaining : Nat} {config : RawCostConfig}
    (absent : budgetedFirstRuntimeCandidate searchBudget config =
      ⟨RuntimeCandidateDecision.noCandidate, remaining⟩) :
    runtimeCostCandidatesFromConfig config = [] := by
  rw [← runtimeCandidateTasks_denote config]
  exact seekRuntimeTasks_noCandidate_denote_empty absent

/-- Public candidate search never creates candidate-search allowance. -/
theorem budgetedFirstRuntimeCandidate_remaining_le
    (searchBudget : Nat) (config : RawCostConfig) :
    (budgetedFirstRuntimeCandidate searchBudget config).remainingBudget ≤
      searchBudget :=
  seekRuntimeTasks_remaining_le config config.purses
    (runtimeCandidateTasks config) searchBudget

/-! ## Two-budget causal prefixes -/

inductive BudgetedPrefixStatus where
  | quiescent
  | fuelExhausted
  | searchExhausted
  deriving Repr, DecidableEq

structure BudgetedCausalPrefix where
  receipt : RawReceipt
  residual : RawCostTerm
  status : BudgetedPrefixStatus
  remainingSearchBudget : Nat
  deriving Repr, DecidableEq

/-- Execute with distinct firing and candidate-search allowances.  Reduction
fuel is checked first; only exhaustive candidate failure establishes
quiescence. -/
def runBudgetedCausalPrefix : Nat → Nat → Nat →
    List RawTraceComponent → RawReceipt → BudgetedCausalPrefix
  | 0, searchBudget, _, components, reverseReceipt =>
      { receipt := reverseReceipt.reverse
        residual := tracedResidual components
        status := .fuelExhausted
        remainingSearchBudget := searchBudget }
  | fuel + 1, searchBudget, eventId, components, reverseReceipt =>
      let search := budgetedFirstRuntimeCandidate searchBudget
        (components.map RawTraceComponent.term)
      match search.decision with
      | .searchExhausted =>
          { receipt := reverseReceipt.reverse
            residual := tracedResidual components
            status := .searchExhausted
            remainingSearchBudget := search.remainingBudget }
      | .noCandidate =>
          { receipt := reverseReceipt.reverse
            residual := tracedResidual components
            status := .quiescent
            remainingSearchBudget := search.remainingBudget }
      | .found step =>
          let event := eventFor components step eventId
          let next := applyTracedStep components step eventId
          runBudgetedCausalPrefix fuel search.remainingBudget (eventId + 1)
            next (event :: reverseReceipt)

def boundedBudgetedCausalPrefix (fuel searchBudget : Nat)
    (term : RawCostTerm) : Option BudgetedCausalPrefix :=
  if term.wellFormed then
    let initial := term.normalizeConfig.map fun component =>
      { term := component, producer := none }
    some (runBudgetedCausalPrefix fuel searchBudget 0 initial [])
  else none

/-! ## Executable status examples -/

example :
    (runBudgetedCausalPrefix 0 0 0 [] []).status =
      BudgetedPrefixStatus.fuelExhausted := rfl

example :
    (runBudgetedCausalPrefix 1 0 0 [] []).status =
      BudgetedPrefixStatus.quiescent := rfl

private def exampleRuntimeRedex : RawWholeRedex :=
  ⟨0, .signature ["pay"], .nil, .nil, ["alice"]⟩

example :
    (seekRuntimeTasks [] [] [.whole exampleRuntimeRedex] 0).decision =
      RuntimeCandidateDecision.searchExhausted := rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
