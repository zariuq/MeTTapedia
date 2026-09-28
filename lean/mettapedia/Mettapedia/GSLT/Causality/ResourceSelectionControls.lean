import Mettapedia.GSLT.Causality.ResourceSelection
import Mettapedia.GSLT.Causality.ResourceConfluence

/-!
# Controls for resource counts, bindings and observations

The examples distinguish occurrence identity from payload equality, shared
bindings from independent matches, snapshot selection from current availability,
and a bag of explored runs from one committed final state.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceSelection.Controls

/-- Identifier and payload: equal payloads need not be the same occurrence. -/
abbrev Occurrence := ℕ × ℕ

def duplicates : Multiset Occurrence := {(0, 7), (1, 7), (2, 8)}

def payloadIs (value : ℕ) (resource : Occurrence) : Bool := decide (resource.2 = value)

def firstSeven : Multiset Occurrence := {(0, 7)}
def secondSeven : Multiset Occurrence := {(1, 7)}
def bothSevens : Multiset Occurrence := {(0, 7), (1, 7)}

/-- Two equal values give two choices of occurrence, not one set element. -/
theorem duplicate_occurrences_give_two_choices :
    choices (payloadIs 7) 1 duplicates = {firstSeven, secondSeven} := by
  decide

/-- Their payload observations coincide while their identities differ. -/
theorem equal_payloads_distinct_occurrences :
    firstSeven.map Prod.snd = secondSeven.map Prod.snd ∧ firstSeven ≠ secondSeven := by
  decide

/-- Forgetting occurrence identifiers retains multiplicity under a bag observer. -/
theorem duplicate_payload_observations :
    (choices (payloadIs 7) 1 duplicates).map (Multiset.map Prod.snd) =
      ({({7} : Multiset ℕ), {7}} : Multiset (Multiset ℕ)) := by
  decide

/-- With collective resources, two indistinguishable copies still give two
combinatorial choices of one occurrence, though both name the same subbag. -/
theorem collective_resources_identify_occurrence_choices :
    choices (fun _ : ℕ => true) 1 {7, 7} =
      ({({7} : Multiset ℕ), {7}} : Multiset (Multiset ℕ)) := by
  decide

/-- Exact-two consumes both occurrences. -/
theorem exact_two_and_atomic_consumption :
    choices (payloadIs 7) 2 duplicates = {bothSevens} ∧
      commit bothSevens duplicates = some {(2, 8)} := by
  decide

/-- Exact-three does not silently weaken the requested count to two. -/
theorem insufficient_matches_no_choice : choices (payloadIs 7) 3 duplicates = 0 := by
  decide

/-- Even when some requested resources are present, a failed commit keeps all
of them; the unknown identifier is not replaced by a value-equal occurrence. -/
theorem unavailable_occurrence_no_partial_deletion :
    commitOrKeep ({(0, 7), (99, 7)} : Multiset Occurrence) duplicates =
      (false, duplicates) := by
  decide

theorem zero_takes_nothing :
    choices (payloadIs 7) 0 duplicates = {0} ∧
      commitOrKeep (0 : Multiset Occurrence) duplicates = (true, duplicates) := by
  decide

/-- Each exploratory branch starts from the same snapshot. -/
theorem alternatives_have_separate_residual_stores :
    branches (payloadIs 7) 1 duplicates =
      {(firstSeven, {(1, 7), (2, 8)}), (secondSeven, {(0, 7), (2, 8)})} := by
  decide

/-- Availability must be checked again after a competing take: a formerly
valid take-all can fail, and no residual part of it is consumed. -/
theorem competing_taker_invalidates_snapshot_selection :
    allMatches (payloadIs 7) duplicates = bothSevens ∧
      commit firstSeven duplicates = some {(1, 7), (2, 8)} ∧
      commitOrKeep bothSevens {(1, 7), (2, 8)} =
        (false, ({(1, 7), (2, 8)} : Multiset Occurrence)) := by
  decide

/-- An old take-all can still validate after insertion while leaving a new
match behind. Availability validation alone is not snapshot freshness. -/
theorem insertion_changes_meaning_of_all :
    let enlarged := duplicates + {(3, 7)}
    commit (allMatches (payloadIs 7) duplicates) enlarged = some {(2, 8), (3, 7)} ∧
      allMatches (payloadIs 7) ({(2, 8), (3, 7)} : Multiset Occurrence) = {(3, 7)} := by
  decide

def twoValues : Multiset Occurrence := {(0, 7), (1, 8)}

/-- One shared binding must satisfy every selected match. Two independent
existential matches need not use the same binding. -/
theorem shared_binding_is_not_independent_matching :
    choices (payloadIs 7) 2 twoValues = 0 ∧
      choices (payloadIs 8) 2 twoValues = 0 ∧
      choices (fun _ => true) 2 twoValues = {twoValues} := by
  decide

/-- Purity of a predicate does not determine which enabled occurrence wins. -/
theorem pure_guard_does_not_determine_committed_store :
    choices (fun _ => true) 1 twoValues = {{(0, 7)}, {(1, 8)}} ∧
      commit {(0, 7)} twoValues = some {(1, 8)} ∧
      commit {(1, 8)} twoValues = some {(0, 7)} ∧
      ({(1, 8)} : Multiset Occurrence) ≠ {(0, 7)} := by
  decide

/-- Selecting one answer can select an effectful branch. The cursor bound does
not imply that evaluating the selected branch preserves its store. -/
theorem one_selected_branch_can_consume :
    ({(0, 7)}, {(1, 8)}) ∈ branches (fun _ => true) 1 twoValues ∧
      commit {(0, 7)} twoValues = some {(1, 8)} ∧
      ({(1, 8)} : Multiset Occurrence) ≠ twoValues := by
  decide

def takeSeven : (selectionSystem payloadIs).Instance (7, 1) :=
  ⟨firstSeven, by decide⟩

def takeOtherSeven : (selectionSystem payloadIs).Instance (7, 1) :=
  ⟨secondSeven, by decide⟩

def takeZero : (selectionSystem payloadIs).Instance (7, 0) :=
  ⟨0, by decide⟩

/-- A zero take is an identity on resource stores. A full execution machine
must still advance or consume its call, rather than repeatedly fire this
resource-only identity as a fresh request. -/
theorem zero_resource_firing_is_identity :
    (selectionSystem payloadIs).Enables duplicates takeZero ∧
      (selectionSystem payloadIs).fire duplicates takeZero = duplicates := by
  simp only [selectionSystem_enables, selectionSystem_fire]
  decide

/-- Distinct occurrences can be consumed concurrently even with equal values. -/
theorem distinct_equal_values_are_independent :
    (selectionSystem payloadIs).Concurrent duplicates takeSeven takeOtherSeven := by
  rw [selectionSystem_concurrent]
  decide

/-- Two requests for the same occurrence are separately enabled, but cannot
both commit from this store. -/
theorem same_occurrence_is_a_conflict :
    (selectionSystem payloadIs).Enables duplicates takeSeven ∧
      ¬ (selectionSystem payloadIs).Concurrent duplicates takeSeven takeSeven ∧
      ¬ (selectionSystem payloadIs).Enables
        ((selectionSystem payloadIs).fire duplicates takeSeven) takeSeven := by
  simp only [selectionSystem_enables, selectionSystem_concurrent, selectionSystem_fire]
  decide

/-- Existing conflict-free saturation has two legal interleavings. Its bag of
returned final states is not the singleton produced by one committed run. -/
theorem conflict_free_does_not_erase_run_multiplicity :
    let system := ResourceInteraction.inference
      ResourceInteraction.Controls.letterRules
    system.ConflictFree ResourceInteraction.Controls.letterCatalogue ∧
      system.outcomes ResourceInteraction.Controls.letterCatalogue 3
          ResourceInteraction.Controls.letterStart ≠
        [ResourceInteraction.Controls.saturated] := by
  constructor
  · exact ResourceInteraction.inference_conflictFree _ _
  · rw [ResourceInteraction.Controls.saturation_two_runs_one_outcome]
    intro equal
    have lengths := congrArg List.length equal
    simp at lengths

end Mettapedia.GSLT.Causality.ResourceSelection.Controls
