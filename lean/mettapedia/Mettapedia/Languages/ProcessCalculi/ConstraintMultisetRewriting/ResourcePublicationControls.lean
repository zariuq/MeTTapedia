import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourcePublicationFailure

/-!
# Publication controls over actual occurrence resources

The source selection below is valid. One region can nevertheless fail to
transfer after another has moved, leaving neither the old nor the complete
source successor. Other controls distinguish physical-region grouping from
independent alias snapshots, and complete replacement from a patch that
accidentally drops an in-region retained read.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourcePublicationControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ResourcePublication ResourcePublicationFailure

def action : SubstitutionAction Nat Unit where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := fun _ value => value
  identity := ()
  compose := fun _ _ => ()
  apply_identity := fun _ => rfl
  apply_compose := fun _ _ _ => rfl
  preserves := fun _ {_ _} equal => equal

def location (occurrence : Nat) : Nat := occurrence / 10
def picked : Selection Nat := ⟨[1, 11], [3], [2, 12]⟩
def rule : RuleInstance Nat := ⟨[1, 11], [3], [], [], [2, 12]⟩
def before : Configuration Nat Nat := ⟨[], {1, 3, 11}⟩
def prepared : Nat → Finset Nat := replacement (T := Nat) location picked before.present

theorem selected_source_is_valid : picked.Valid action id rule before := by
  apply (ResourceOccupation.valid_iff_resource_information action picked id rule before).mpr
  refine ⟨⟨rfl, rfl, rfl⟩, ⟨⟨{2, 3, 12}, ?_⟩, ?_⟩, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · refine ⟨(), ?_⟩
    simp [Selection.problem, Selection.equations, picked, rule, before,
      SubstitutionAction.Models, SubstitutionAction.Solves, action]
  · intro check member
    cases member

theorem both_regions_prepare_with_the_frame :
    prepareRegion location picked before.present 0 = some {2, 3} ∧
      prepareRegion location picked before.present 1 = some {12} := by decide +kernel

theorem all_regions_complete_the_selected_world :
    transfer location prepared (fun _ => true) [0, 1] before.present =
      ⟨[0, 1], {2, 3, 12}, .complete⟩ ∧
    (picked.result id rule before).present = {2, 3, 12} := by
  constructor
  · apply congrArg (fun world : Finset Nat => (⟨[0, 1], world, .complete⟩ : TransferReport Nat Nat))
    decide +kernel
  · decide +kernel

theorem fail_before_first_is_unchanged :
    transfer location prepared (fun _ => false) [0, 1] before.present =
      ⟨[], before.present, .failed 0⟩ := rfl

theorem fail_after_first_has_exact_nonempty_prefix :
    transfer location prepared (fun region => decide (region = 0)) [0, 1] before.present =
      ⟨[0], {2, 3, 11}, .failed 1⟩ := by
  apply congrArg (fun world : Finset Nat => (⟨[0], world, .failed 1⟩ : TransferReport Nat Nat))
  decide +kernel

/-- Terminal transfer failure occurs despite a valid source selection. It
must not be reported as ordinary refusal with the original world restored. -/
theorem partial_failure_is_neither_refusal_nor_completion :
    picked.Valid action id rule before ∧
      let report := transfer location prepared (fun region => decide (region = 0)) [0, 1] before.present
      report.outcome = .failed 1 ∧ report.completed ≠ [] ∧
        report.world ≠ before.present ∧ report.world ≠ (picked.result id rule before).present := by
  refine ⟨selected_source_is_valid, ?_⟩
  decide +kernel

theorem every_publication_prefix_preserves_the_read (regions : List Nat) :
    3 ∈ publish location prepared regions before.present :=
  selected_read_survives_prefix action id location picked rule before selected_source_is_valid
    regions (by decide)

def sharedRegion (_ : Nat) : Nat := 0
def aliasOne : Selection Nat := ⟨[0], [], [2]⟩
def aliasTwo : Selection Nat := ⟨[1], [], [3]⟩
def grouped : Selection Nat := ⟨[0, 1], [], [2, 3]⟩
def sharedBefore : Finset Nat := {0, 1, 9}

theorem alias_handles_schedule_one_physical_region :
    destinations (fun _ : Bool => (0 : Nat)) [true, false] = [0] := by decide +kernel

/-- Two overlapping handle snapshots cannot be published independently:
the second snapshot loses the first output and resurrects its consumed row. -/
theorem ungrouped_alias_snapshots_lose_an_update :
    install sharedRegion 0 (replacement (T := Nat) sharedRegion aliasTwo sharedBefore 0)
      (install sharedRegion 0 (replacement (T := Nat) sharedRegion aliasOne sharedBefore 0) sharedBefore) =
        {0, 3, 9} ∧
    publish sharedRegion (replacement (T := Nat) sharedRegion grouped sharedBefore) [0] sharedBefore =
      {2, 3, 9} ∧ ({0, 3, 9} : Finset Nat) ≠ {2, 3, 9} := by decide +kernel

def readSelection : Selection Nat := ⟨[0], [9], [2]⟩

theorem an_output_only_patch_drops_the_retained_read :
    ResourceOccupation.commit readSelection.taken readSelection.read readSelection.made {0, 9} =
      some {2, 9} ∧
    replacement (T := Nat) sharedRegion readSelection {0, 9} 0 = {2, 9} ∧
    install sharedRegion 0 {2} {0, 9} = {2} ∧
    9 ∉ install sharedRegion 0 {2} {0, 9} := by decide +kernel

/-- Distinct physical fibres cannot overlap; aliases must be grouped before
using this disjointness fact. -/
theorem the_actual_regions_are_disjoint :
    Disjoint (slice location 0 before.present) (slice location 1 before.present) :=
  slices_disjoint location (by decide) before.present

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourcePublicationControls
