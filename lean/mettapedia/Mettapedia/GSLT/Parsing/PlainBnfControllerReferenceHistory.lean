import Mettapedia.GSLT.Parsing.PlainBnfStructuredDiscoveryGraph

/-!
# Exact history and saturation of the existing discovery reference trace

Standard list folds replay the already defined ordered event trace. They
retain publication order in reversed name history and transport its known
meaning. No additional Run interpreter or controller state is introduced.
The fuel bound counts fresh publications, not source-contextual depth or
native-runtime work.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerReferenceHistory

open Algorithms.MeTTa.Simple.Parser (SExpr)
open PlainBnfOrderedGraphDiscovery
open PlainBnfDependencyWorklist (unpublished initialQueue)
open PlainBnfStructuredDiscoveryGraph
open PlainBnfReferenceCollectionSourceExecution (text)

variable {size : Nat}

theorem runEvents_succ (grammar : Grammar size) (fuel : Nat) (known : Known size)
    (round cursor : Nat) (event : Event size)
    (selected : nextEvent grammar known round cursor = some event) :
    runEvents grammar (fuel + 1) known round cursor =
      event :: runEvents grammar fuel (publish known event.position) event.round (event.position.val + 1) := by
  simp [runEvents, selected]

theorem nextEvent_ready (grammar : Grammar size) (known : Known size)
    (round cursor : Nat) (event : Event size)
    (selected : nextEvent grammar known round cursor = some event) :
    ready grammar known event.position = true := by
  have member := PlainBnfDependencyWorklist.selected_mem_queue (initialQueue grammar known) round cursor
    (by rwa [PlainBnfDependencyWorklist.select_eq_nextEvent])
  exact (Finset.mem_filter.mp member).2

theorem nextEvent_fresh (grammar : Grammar size) (known : Known size)
    (round cursor : Nat) (event : Event size)
    (selected : nextEvent grammar known round cursor = some event) : known event.position = false := by
  have enabled := nextEvent_ready grammar known round cursor event selected
  simp only [ready, Bool.and_eq_true] at enabled
  simpa using enabled.1

theorem nextEvent_none_iff (grammar : Grammar size) (known : Known size) (round cursor : Nat) :
    nextEvent grammar known round cursor = none ↔ ∀ position, ready grammar known position = false := by
  constructor
  · intro noneReady
    unfold nextEvent at noneReady
    cases suffix : nextReady grammar ((List.finRange size).drop cursor) known with
    | some pair => simp [suffix] at noneReady
    | none =>
        cases full : nextReady grammar (List.finRange size) known with
        | some pair => simp [suffix, full] at noneReady
        | none =>
            exact fun position => (nextReady_none_iff grammar _ known).mp full position (by simp)
  · intro noneReady
    have suffix : nextReady grammar ((List.finRange size).drop cursor) known = none :=
      (nextReady_none_iff grammar _ known).mpr (fun position _ => noneReady position)
    have full : nextReady grammar (List.finRange size) known = none :=
      (nextReady_none_iff grammar _ known).mpr (fun position _ => noneReady position)
    simp [nextEvent, suffix, full]

theorem zero_sufficient_no_event (grammar : Grammar size) (known : Known size) (round cursor : Nat)
    (enough : (unpublished known).card ≤ 0) : nextEvent grammar known round cursor = none := by
  rw [← PlainBnfDependencyWorklist.select_eq_nextEvent,
    PlainBnfDependencyWorklist.empty_unpublished_queue grammar known (Nat.eq_zero_of_le_zero enough)]
  simp [PlainBnfDependencyWorklist.select, PlainBnfDependencyWorklist.least]

theorem event_initially_unknown (grammar : Grammar size) (fuel : Nat) (known : Known size)
    (round cursor : Nat) (event : Event size)
    (member : event ∈ runEvents grammar fuel known round cursor) : known event.position = false := by
  induction fuel generalizing known round cursor with
  | zero => cases member
  | succ fuel ih =>
      cases selected : nextEvent grammar known round cursor with
      | none => simp [runEvents, selected] at member
      | some first =>
          rw [runEvents_succ grammar fuel known round cursor first selected] at member
          rcases List.mem_cons.mp member with same | rest
          · subst event
            exact nextEvent_fresh grammar known round cursor first selected
          · have fresh := ih (publish known first.position) first.round (first.position.val + 1) rest
            by_cases same : event.position = first.position
            · simp [publish, same] at fresh
            · simpa [publish, same] using fresh

theorem runEvents_positions_nodup (grammar : Grammar size) (fuel : Nat) (known : Known size)
    (round cursor : Nat) : ((runEvents grammar fuel known round cursor).map (·.position)).Nodup := by
  induction fuel generalizing known round cursor with
  | zero => simp [runEvents]
  | succ fuel ih =>
      cases selected : nextEvent grammar known round cursor with
      | none => simp [runEvents, selected]
      | some event =>
          rw [runEvents_succ grammar fuel known round cursor event selected, List.map_cons, List.nodup_cons]
          refine ⟨?_, ih _ _ _⟩
          intro member
          obtain ⟨later, inside, same⟩ := List.mem_map.mp member
          have fresh := event_initially_unknown grammar fuel (publish known event.position)
            event.round (event.position.val + 1) later inside
          simp [publish, same] at fresh

theorem runEvents_stable (grammar : Grammar size) (fuel extra : Nat) (known : Known size)
    (round cursor : Nat) (enough : (unpublished known).card ≤ fuel) :
    runEvents grammar (fuel + extra) known round cursor = runEvents grammar fuel known round cursor := by
  rw [← PlainBnfDependencyWorklist.run_eq_runEvents, ← PlainBnfDependencyWorklist.run_eq_runEvents]
  exact PlainBnfDependencyWorklist.run_stable grammar fuel extra known round cursor enough

/-- After enough publications, the replayed known state has no ready position. -/
theorem terminal_ready_false (grammar : Grammar size) (fuel : Nat) (known : Known size)
    (round cursor : Nat) (enough : (unpublished known).card ≤ fuel) :
    ∀ position, ready grammar
      ((runEvents grammar fuel known round cursor).foldl (fun current event => publish current event.position) known)
      position = false := by
  induction fuel generalizing known round cursor with
  | zero =>
      exact (nextEvent_none_iff grammar known round cursor).mp
        (zero_sufficient_no_event grammar known round cursor enough)
  | succ fuel ih =>
      cases selected : nextEvent grammar known round cursor with
      | none =>
          simpa [runEvents, selected] using (nextEvent_none_iff grammar known round cursor).mp selected
      | some event =>
          rw [runEvents_succ grammar fuel known round cursor event selected, List.foldl_cons]
          apply ih (publish known event.position) event.round (event.position.val + 1)
          have decrease := PlainBnfDependencyWorklist.publication_decreases_count known event.position
            (nextEvent_fresh grammar known round cursor event selected)
          omega

/-- Exact reversed history for any event list, including occurrence order. -/
theorem history_fold_exact (definitions : Definitions) (events : List (Event definitions.length))
    (history : List SExpr) :
    events.foldl (fun current event => text (nameAt definitions event.position) :: current) history =
      (events.map (fun event => text (nameAt definitions event.position))).reverse ++ history := by
  induction events generalizing history with
  | nil => rfl
  | cons event rest ih => simp [List.foldl_cons, ih, List.reverse_cons, List.append_assoc]

theorem history_fold_scoped (definitions : Definitions) (events : List (Event definitions.length))
    (history : List SExpr) (historyScoped : HistoryScoped definitions history) :
    HistoryScoped definitions
      (events.foldl (fun current event => text (nameAt definitions event.position) :: current) history) := by
  induction events generalizing history with
  | nil => exact historyScoped
  | cons event rest ih =>
      exact ih _ (history_publish_scoped definitions history historyScoped event.position)

theorem graphKnown_history_fold (definitions : Definitions) (unique : (names definitions).Nodup)
    (events : List (Event definitions.length)) (history : List SExpr) :
    graphKnown definitions
      (events.foldl (fun current event => text (nameAt definitions event.position) :: current) history) =
      events.foldl (fun current event => publish current event.position) (graphKnown definitions history) := by
  induction events generalizing history with
  | nil => rfl
  | cons event rest ih =>
      simp only [List.foldl_cons, ih, graphKnown_publish definitions unique]

theorem reference_history_nodup (definitions : Definitions) (unique : (names definitions).Nodup)
    (grammar : Grammar definitions.length) (fuel : Nat) (history : List SExpr)
    (historyUnique : history.Nodup) (round cursor : Nat) :
    ((runEvents grammar fuel (graphKnown definitions history) round cursor).foldl
      (fun current event => text (nameAt definitions event.position) :: current) history).Nodup := by
  induction fuel generalizing history round cursor with
  | zero => exact historyUnique
  | succ fuel ih =>
      cases selected : nextEvent grammar (graphKnown definitions history) round cursor with
      | none => simpa [runEvents, selected] using historyUnique
      | some event =>
          rw [runEvents_succ grammar fuel _ round cursor event selected, List.foldl_cons]
          have fresh := nextEvent_fresh grammar (graphKnown definitions history) round cursor event selected
          have absent : text (nameAt definitions event.position) ∉ history := by
            simpa [graphKnown, PlainBnfProductiveSourceExecution.member] using fresh
          rw [← graphKnown_publish definitions unique history event.position]
          exact ih _ (List.nodup_cons.mpr ⟨absent, historyUnique⟩) event.round (event.position.val + 1)

theorem reference_history_saturated (definitions : Definitions) (unique : (names definitions).Nodup)
    (grammar : Grammar definitions.length) (fuel : Nat) (history : List SExpr)
    (round cursor : Nat) (enough : (unpublished (graphKnown definitions history)).card ≤ fuel) :
    ∀ position, ready grammar
      (graphKnown definitions
        ((runEvents grammar fuel (graphKnown definitions history) round cursor).foldl
          (fun current event => text (nameAt definitions event.position) :: current) history))
      position = false := by
  rw [graphKnown_history_fold definitions unique]
  exact terminal_ready_false grammar fuel (graphKnown definitions history) round cursor enough

theorem two_events_reverse_exactly (definitions : Definitions) (first second : Event definitions.length)
    (history : List SExpr) :
    [first, second].foldl (fun current event => text (nameAt definitions event.position) :: current) history =
      text (nameAt definitions second.position) :: text (nameAt definitions first.position) :: history := rfl

theorem ready_seed_is_published :
    runEvents (fun _ : Fin 1 => [⟨[], true⟩]) 1 (fun _ => false) 0 0 = [⟨0, 0⟩] := by decide

/-- A short trace can be empty while a ready position remains. -/
theorem zero_fuel_is_not_saturation :
    let grammar : Grammar 1 := fun _ => [⟨[], true⟩]
    let before : Known 1 := fun _ => false
    runEvents grammar 0 before 0 0 = [] ∧
      ready grammar ((runEvents grammar 0 before 0 0).foldl
        (fun current event => publish current event.position) before) 0 = true := by decide

/-- Saturation means no further enabled publication, not every name known. -/
theorem cycle_saturates_without_publication :
    let grammar : Grammar 1 := fun _ => [⟨[0], true⟩]
    let before : Known 1 := fun _ => false
    runEvents grammar 1 before 0 0 = [] ∧ ready grammar before 0 = false ∧ before 0 = false := by decide

#print axioms runEvents_positions_nodup
#print axioms runEvents_stable
#print axioms terminal_ready_false
#print axioms history_fold_exact
#print axioms reference_history_nodup
#print axioms reference_history_saturated

end Mettapedia.GSLT.Parsing.PlainBnfControllerReferenceHistory
