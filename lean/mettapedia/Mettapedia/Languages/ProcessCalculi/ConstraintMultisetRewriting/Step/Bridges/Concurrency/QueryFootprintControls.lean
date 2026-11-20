import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionObservations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Counting

/-!
# A query footprint does not check the observation

A single actual row supplies the same nonempty physical footprint for two count queries.
The query-only selection is valid, and both footprint commits are physically enabled.
Counting one is admitted; counting two is refused by the region observation at the actual
solution. Thus physical enabling of a footprint does not recover region-query admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.QueryFootprintControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open PredicateQueryAdmission

abbrev action : SubstitutionAction Nat PUnit.{1} :=
  RuleSyntax.RuleOccurrences.Closed.action Nat

def before : Configuration Nat Nat := ⟨[], {7}⟩

def label (_ : Nat) : Nat := 42

def selection : Selection Nat := ⟨[], [], []⟩

def instruction : RuleInstance Nat := ⟨[], [], [], [], []⟩

def region (_ : PUnit.{1}) (value : Nat) : Bool := decide (value = 42)

def query (number : Nat) : RegionQuery Nat PUnit.{1} Nat :=
  RegionQuery.count region number

theorem world_nonempty : before.present.Nonempty := by
  exact ⟨7, by simp [before]⟩

theorem actual_region (model : PUnit.{1}) :
    regionOf label before.present (region model) = {7} := by
  simp [regionOf, before, label, region]

theorem problem_empty : selection.problem label instruction before = [] := rfl

theorem problem_model (model : PUnit.{1}) :
    action.Models model (selection.problem label instruction before) := by
  rw [problem_empty]
  exact action.models_nil model

theorem selection_enabled : Enabled label before.present selection.commit := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [selection, Selection.commit]
  · simp [selection, Selection.commit]
  · simp [selection, Selection.commit]
  · simp [selection, Selection.commit]
  · simp [selection, Selection.commit]

theorem selection_valid : selection.Valid action label instruction before := by
  refine ⟨?_, ?_, ?_, ?_, ?_, selection_enabled,
    ⟨PUnit.unit, problem_model PUnit.unit⟩, ?_⟩
  · simp [selection]
  · simp [selection]
  · rfl
  · rfl
  · rfl
  · intro check member
    simp [instruction] at member

theorem footprint_seen (number : Nat) (model : PUnit.{1}) :
    ((query number).footprintAt model label before.present).seen = {7} :=
  actual_region model

theorem footprint_holds (number : Nat) (model : PUnit.{1}) :
    ((query number).footprintAt model label before.present).Holds label before.present :=
  RegionQuery.footprintAt_holds (query number) model label before.present

theorem footprint_commit_enabled (number : Nat) (model : PUnit.{1}) :
    Enabled label before.present
      (regionCommit selection [query number] model label before.present) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [regionCommit, selection, Selection.commit]
  · simp [regionCommit, selection, Selection.commit]
  · simp [regionCommit, selection, Selection.commit]
  · simp [regionCommit, selection, Selection.commit]
  · intro observed member
    change observed ∈ [(query number).footprintAt model label before.present] at member
    have same := List.mem_singleton.mp member
    subst observed
    exact footprint_holds number model

theorem footprints_equal (model : PUnit.{1}) :
    (query 1).footprintAt model label before.present =
      (query 2).footprintAt model label before.present := rfl

theorem footprint_commits_equal (model : PUnit.{1}) :
    regionCommit selection [query 1] model label before.present =
      regionCommit selection [query 2] model label before.present := rfl

theorem count_one_holds (model : PUnit.{1}) :
    (query 1).Holds model label before.present := by
  change (regionOf label before.present (region model)).card = 1
  rw [actual_region]
  rfl

theorem count_two_not_holds (model : PUnit.{1}) :
    ¬ (query 2).Holds model label before.present := by
  change ¬ (regionOf label before.present (region model)).card = 2
  rw [actual_region]
  decide

theorem count_one_asked :
    (query 1).Ask action (selection.problem label instruction before) label before.present := by
  intro model _
  exact count_one_holds model

theorem count_two_not_asked :
    ¬ (query 2).Ask action (selection.problem label instruction before) label before.present := by
  intro asked
  exact count_two_not_holds PUnit.unit (asked PUnit.unit (problem_model PUnit.unit))

theorem count_one_valid :
    RegionValid action label instruction [query 1] before selection := by
  refine ⟨selection_valid, ?_⟩
  intro observed member
  have same := List.mem_singleton.mp member
  subst observed
  exact count_one_asked

theorem count_two_not_valid :
    ¬ RegionValid action label instruction [query 2] before selection := by
  intro valid
  exact count_two_not_asked (valid.observations (query 2) (by simp))

/-- The base selection and the nonempty footprint are valid; only the requested count fails. -/
theorem enabled_footprint_does_not_imply_admission :
    before.present.Nonempty ∧
      selection.Valid action label instruction before ∧
      ((query 2).footprintAt PUnit.unit label before.present).seen = {7} ∧
      ((query 2).footprintAt PUnit.unit label before.present).Holds label before.present ∧
      Enabled label before.present
        (regionCommit selection [query 2] PUnit.unit label before.present) ∧
      ¬ (query 2).Holds PUnit.unit label before.present ∧
      ¬ (query 2).Ask action (selection.problem label instruction before) label before.present ∧
      ¬ RegionValid action label instruction [query 2] before selection :=
  ⟨world_nonempty, selection_valid, footprint_seen 2 PUnit.unit,
    footprint_holds 2 PUnit.unit, footprint_commit_enabled 2 PUnit.unit,
    count_two_not_holds PUnit.unit, count_two_not_asked, count_two_not_valid⟩

/-- Admission differs even when the actual physical footprint commits are equal. -/
theorem same_footprint_different_admission :
    regionCommit selection [query 1] PUnit.unit label before.present =
        regionCommit selection [query 2] PUnit.unit label before.present ∧
      RegionValid action label instruction [query 1] before selection ∧
      ¬ RegionValid action label instruction [query 2] before selection :=
  ⟨footprint_commits_equal PUnit.unit, count_one_valid, count_two_not_valid⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.QueryFootprintControls
