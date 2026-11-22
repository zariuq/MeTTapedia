import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceObservations

/-!
# Resource retention controls: future scope, refusal, identity and history

The positive example takes one occurrence, reads another twice and makes a
fresh third occurrence. An unrelated retained row is removed from the physical
presentation without changing any supported future observation. Countercontrols
show why the footprint must include future tests, why counts cannot replace
identity, and why equal occupation operators do not identify execution histories.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceObservationControls

open ResourceOccupation ResourceObservations
open Mettapedia.Cybernetics
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

def footprint : Finset Nat := {1, 2, 3}
def world : Finset Nat := {1, 2, 99}
def events : List (List Nat × List Nat × List Nat) :=
  [([1], [2, 2], [3]), ([], [3, 2], [])]

theorem mixed_events_supported : Supported footprint events := by
  simp [Supported, SupportedCommit, footprint, events]

theorem actual_mixed_execution :
    runs events world = some {2, 3, 99} ∧
      runs events (project footprint world) = some {2, 3} := by decide +kernel

theorem proper_retention_preserves_every_supported_future :
    project footprint world ≠ world ∧
      (futureObserver footprint).observe (project footprint world) =
        (futureObserver footprint).observe world := by
  exact ⟨by decide +kernel, retention_preserves_all_supported_futures footprint world⟩

theorem actual_mixed_prefixes_preserved (length : Nat) :
    (runs (events.take length) world).map (project footprint) =
      runs (events.take length) (project footprint world) :=
  every_prefix_preserved mixed_events_supported world length

def refusedEvents : List (List Nat × List Nat × List Nat) :=
  [([1], [2, 2], [3]), ([], [1], [])]

theorem refused_events_supported : Supported footprint refusedEvents := by
  simp [Supported, SupportedCommit, footprint, refusedEvents]

theorem actual_refused_execution :
    runs refusedEvents world = none ∧
      runs refusedEvents (project footprint world) = none := by decide +kernel

theorem supported_refusal_is_preserved :
    runs refusedEvents (project footprint world) = none ↔ runs refusedEvents world = none :=
  runs_refusal_iff refused_events_supported world

theorem supported_absence_composes_with_the_mixed_commit :
    Preserves footprint (andThen (commit [1] [2, 2] [3]) (absentOn {1})) := by
  apply preserves_andThen
  · exact preserves_commit (by simp [SupportedCommit, footprint])
  · exact preserves_absentOn (by simp [footprint])

theorem actual_absence_success_and_refusal :
    andThen (commit [1] [2, 2] [3]) (absentOn {1}) world = some {2, 3, 99} ∧
      andThen (commit [1] [2, 2] [3]) (absentOn {2}) world = none := by decide +kernel

def picked : Selection Nat := ⟨[1], [2, 2], [3]⟩
def labels (_ : Nat) : Unit := ()

theorem actual_selection_resource_conditions_preserved :
    (picked.taken.Nodup ∧ picked.made.Nodup ∧ Enabled labels world picked.commit) ↔
      picked.taken.Nodup ∧ picked.made.Nodup ∧
        Enabled labels (project footprint world) picked.commit :=
  selection_enabled_iff labels picked (by simp [SupportedCommit, picked, footprint]) world

def readSeven : List (List Nat × List Nat × List Nat) := [([], [7], [])]

theorem discarded_needed_row_changes_future_refusal :
    (runs readSeven {7}).map (project (∅ : Finset Nat)) = some ∅ ∧
      runs readSeven (project (∅ : Finset Nat) {7}) = none := by decide +kernel

theorem immediate_agreement_is_insufficient_without_future_support :
    project ({1} : Finset Nat) {1, 7} = project {1} {1} ∧
      (runs readSeven {1, 7}).map (project ({1} : Finset Nat)) ≠
        (runs readSeven {1}).map (project ({1} : Finset Nat)) := by decide +kernel

theorem separating_future_is_outside_the_footprint :
    ¬ Supported ({1} : Finset Nat) readSeven := by
  simp [Supported, SupportedCommit, readSeven]

theorem count_equality_does_not_license_identity_forgetting :
    ({7} : Finset Nat).card = ({8} : Finset Nat).card ∧
      runs readSeven {7} ≠ runs readSeven {8} := by decide +kernel

theorem complete_membership_still_observes_the_removed_row :
    (membershipObserver (O := Nat)).Distinguishes world (project footprint world) := by
  intro same
  have identical := all_membership_observers_separate same
  exact (by decide +kernel : world ≠ project footprint world) identical

theorem membership_preservation_forbids_changing_the_world
    (change : Finset Nat → Finset Nat)
    (preserved : ∀ input, (membershipObserver (O := Nat)).observe (change input) =
      (membershipObserver (O := Nat)).observe input) :
    ∀ input, change input = input := fun input =>
  all_membership_observers_separate (preserved input)

theorem retained_count_is_a_factored_observation :
    ∃ readout : Retained footprint → Nat,
      ∀ input, readout (retain footprint input) = (project footprint input).card :=
  ⟨fun kept => kept.val.card, fun _ => rfl⟩

theorem equal_occupation_does_not_erase_read_history :
    ([([], [7], [])] : List (List Nat × List Nat × List Nat)) ≠ [([], [7, 7], [])] ∧
      runs [([], [7], [])] ({7} : Finset Nat) = runs [([], [7, 7], [])] {7} := by decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceObservationControls
