import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourcePublication
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes.Facets

/-!
# Failable region publication retains the exact completed prefix

All replacement regions have been prepared before this loop starts. A
successful transfer installs one complete region. A refused transfer has
not changed that region and stops publication. The report records the
completed region prefix and the actual resource world. Previous successful
transfers are retained, including when the report records terminal failure.

This is an explicit contract for the native region transfer boundary, not a
proof that a C transfer satisfies it. A transfer that can fail after changing
part of its own region needs a finer failure receipt. No rollback is modeled,
and a terminal transfer failure does not imply source-level refusal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourcePublicationFailure

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
open ResourcePublication

variable {O R T S N : Type*} [DecidableEq O] [DecidableEq R]

inductive Outcome (R : Type*) where
  | complete
  | failed (next : R)
  deriving DecidableEq

structure TransferReport (O R : Type*) where
  completed : List R
  world : Finset O
  outcome : Outcome R
  deriving DecidableEq

/-- Success moves one complete prepared region; refusal leaves the current
world in the report and does not proceed to later destinations. -/
def transfer (location : O → R) (prepared : R → Finset O) (accepted : R → Bool) :
    List R → Finset O → TransferReport O R
  | [], current => ⟨[], current, .complete⟩
  | region :: later, current =>
      if accepted region then
        let following := transfer location prepared accepted later
          (install location region (prepared region) current)
        ⟨region :: following.completed, following.world, following.outcome⟩
      else ⟨[], current, .failed region⟩

theorem completed_is_prefix (location : O → R) (prepared : R → Finset O)
    (accepted : R → Bool) (regions : List R) (before : Finset O) :
    ∃ later, regions = (transfer location prepared accepted regions before).completed ++ later := by
  induction regions generalizing before with
  | nil => exact ⟨[], rfl⟩
  | cons region later ih =>
      by_cases succeeds : accepted region = true
      · obtain ⟨rest, split⟩ := ih (install location region (prepared region) before)
        refine ⟨rest, ?_⟩
        simpa [transfer, succeeds] using congrArg (List.cons region) split
      · exact ⟨region :: later, by simp [transfer, succeeds]⟩

theorem completed_are_accepted (location : O → R) (prepared : R → Finset O)
    (accepted : R → Bool) (regions : List R) (before : Finset O) :
    ∀ region ∈ (transfer location prepared accepted regions before).completed, accepted region = true := by
  induction regions generalizing before with
  | nil => simp [transfer]
  | cons region later ih =>
      by_cases succeeds : accepted region = true
      · simpa [transfer, succeeds] using And.intro succeeds
          (ih (install location region (prepared region) before))
      · simp [transfer, succeeds]

theorem complete_has_all_regions (location : O → R) (prepared : R → Finset O)
    (accepted : R → Bool) (regions : List R) (before : Finset O)
    (finished : (transfer location prepared accepted regions before).outcome = .complete) :
    (transfer location prepared accepted regions before).completed = regions := by
  induction regions generalizing before with
  | nil => rfl
  | cons region later ih =>
      by_cases succeeds : accepted region = true
      · simp only [transfer, succeeds, ↓reduceIte] at finished ⊢
        exact congrArg (List.cons region) (ih _ finished)
      · simp [transfer, succeeds] at finished

theorem failure_reports_next_region (location : O → R) (prepared : R → Finset O)
    (accepted : R → Bool) (regions : List R) (before : Finset O) (next : R)
    (failed : (transfer location prepared accepted regions before).outcome = .failed next) :
    ∃ later, regions = (transfer location prepared accepted regions before).completed ++ next :: later ∧
      accepted next = false := by
  induction regions generalizing before with
  | nil => cases failed
  | cons region later ih =>
      by_cases succeeds : accepted region = true
      · simp only [transfer, succeeds, ↓reduceIte] at failed ⊢
        obtain ⟨rest, split, refused⟩ := ih _ failed
        exact ⟨rest, congrArg (List.cons region) split, refused⟩
      · have same : region = next := by simpa [transfer, succeeds] using failed
        subst region
        exact ⟨later, by simp [transfer, succeeds], Bool.eq_false_iff.mpr succeeds⟩

/-- The report's world is proved to equal the actual sequence of installations
named by its completed list, independently of success or failure. -/
theorem actual_world_is_published_prefix (location : O → R) (prepared : R → Finset O)
    (accepted : R → Bool) (regions : List R) (before : Finset O) :
    (transfer location prepared accepted regions before).world =
      publish location prepared (transfer location prepared accepted regions before).completed before := by
  induction regions generalizing before with
  | nil => rfl
  | cons region later ih =>
      by_cases succeeds : accepted region = true
      · simpa [transfer, succeeds, publish] using ih (install location region (prepared region) before)
      · simp [transfer, succeeds, publish]

theorem transfer_selected_membership (location : O → R) (picked : Selection O)
    (before : Finset O) (accepted : R → Bool) (regions : List R) (o : O) :
    o ∈ (transfer location (replacement (T := T) location picked before) accepted regions before).world ↔
      if location o ∈ (transfer location (replacement (T := T) location picked before)
          accepted regions before).completed
      then o ∈ fire before (picked.commit (T := T)) else o ∈ before := by
  rw [actual_world_is_published_prefix]
  exact selected_publication_membership location picked before _ o

theorem completed_transfer_is_selected_successor (A : SubstitutionAction T S) (label : O → T)
    (location : O → R) (picked : Selection O) (rule : RuleInstance T)
    (before : Configuration T O) (valid : picked.Valid A label rule before)
    (accepted : R → Bool) (regions : List R)
    (covers : ∀ o ∈ picked.taken ++ picked.made, location o ∈ regions)
    (finished : (transfer location (replacement (T := T) location picked before.present)
      accepted regions before.present).outcome = .complete) :
    Step A label rule before
      ⟨(picked.result label rule before).equations,
        (transfer location (replacement (T := T) location picked before.present)
          accepted regions before.present).world⟩ := by
  refine ⟨picked, valid, ?_⟩
  have complete := complete_has_all_regions location (replacement (T := T) location picked before.present)
    accepted regions before.present finished
  rw [actual_world_is_published_prefix, complete, publish_all_eq_source location picked before.present regions covers]
  rfl

theorem refusal_before_first_keeps_world (location : O → R) (prepared : R → Finset O)
    (accepted : R → Bool) (region : R) (later : List R) (before : Finset O)
    (refused : accepted region = false) :
    transfer location prepared accepted (region :: later) before = ⟨[], before, .failed region⟩ := by
  simp [transfer, refused]

/-- Even a failed publication cannot acquire a new send right. Any newly
visible row belongs to the source selection and needs its original authority. -/
theorem newly_visible_has_send_right (label : O → T) (logicalLocation : T → N)
    (rights : Rights N) (location : O → R) (picked : Selection O) (before : Finset O)
    (formed : FormedUnder label logicalLocation rights picked.commit)
    (accepted : R → Bool) (regions : List R) {o : O}
    (visible : o ∈ (transfer location (replacement (T := T) location picked before)
      accepted regions before).world) (newlyVisible : o ∉ before) :
    rights (logicalLocation (label o)) .send = true := by
  rw [transfer_selected_membership] at visible
  split at visible
  · rcases mem_fire.mp visible with old | made
    · exact False.elim (newlyVisible old.1)
    · exact formed.made o made
  · exact False.elim (newlyVisible visible)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourcePublicationFailure
