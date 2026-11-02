import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadResourceLifting

/-!
# Read-compatible resource firings lift to ordinary CMR selections

Read support is allocated first. Consumption uses the remaining physical
world, so no consumed row is also read. The existing no-read lift allocates
fresh raw outputs against the whole original world. One shared model solves
all source equations, and the resulting observation is the complete bag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.Causality
open PositiveResourceProjection (realized readFootprint)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} {assignment : S} {label : O → T}

theorem lift_enabled [DecidableEq T] (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (source : AdmittedRule A assignment) (plan : ReadPlan A assignment label source.rule)
    (before : Configuration T O) (oldSolved : A.Models assignment before.equations)
    (enabled : (resources A assignment label).Enables
      (labels (realized A assignment label) before.present) (site := ⟨source⟩) ⟨plan⟩) :
    ∃ selection : Selection O,
      selection.Valid A label source.rule before ∧
      A.Models assignment (selection.result label source.rule before).equations ∧
      Nonempty (ReadRealization A assignment label plan selection) ∧
      labels (realized A assignment label) (selection.result label source.rule before).present =
        (resources A assignment label).fire
          (labels (realized A assignment label) before.present) (site := ⟨source⟩) ⟨plan⟩ := by
  have demandFits : (source.rule.take.map (A.apply assignment) : Multiset T) +
      readFootprint A assignment label plan.selection ≤ labels (realized A assignment label) before.present := enabled
  have readFits : readFootprint A assignment label plan.selection ≤ labels (realized A assignment label) before.present :=
    le_trans (Multiset.le_add_left _ _) demandFits
  obtain ⟨allocation⟩ := allocate_reads plan before.present readFits
  let readRows := allocation.slots.toFinset
  have readSubset : readRows ⊆ before.present := by
    intro occurrence member
    exact allocation.occupied occurrence (List.mem_toFinset.mp member)
  have observedRead : labels (realized A assignment label) readRows =
      readFootprint A assignment label plan.selection := allocation.allocated_bag
  have split : labels (realized A assignment label) before.present =
      labels (realized A assignment label) (before.present \ readRows) +
        readFootprint A assignment label plan.selection := by
    rw [← observedRead, ← labels_union_of_disjoint _ Finset.sdiff_disjoint,
      Finset.sdiff_union_of_subset readSubset]
  rw [split] at demandFits
  have takeFits : (source.rule.take.map (A.apply assignment) : Multiset T) ≤
      labels (realized A assignment label) (before.present \ readRows) :=
    (add_le_add_iff_right (readFootprint A assignment label plan.selection)).mp demandFits
  obtain ⟨taken, distinctTakes, takenPresent, takeValues⟩ :=
    GuardedMultisetRewriting.exists_occurrences (realized A assignment label)
      (source.rule.take.map (A.apply assignment)) (before.present \ readRows) takeFits
  obtain ⟨made, distinctMade, freshMade, outputValues⟩ := fresh_outputs structural supply source.rule.produce before.present
  let selection : Selection O := ⟨taken, allocation.readList, made⟩
  have takeLength : source.rule.take.length = taken.length := by
    have lengths := congrArg List.length takeValues
    simpa only [List.length_map] using lengths.symm
  have takeMatch : List.Forall₂ (fun pattern occurrence =>
      A.E (A.apply assignment pattern) (A.apply assignment (label occurrence))) source.rule.take taken := by
    have values : List.Forall₂ Eq (source.rule.take.map (A.apply assignment))
        (taken.map (realized A assignment label)) := by
      rw [List.forall₂_eq_eq_eq]
      exact takeValues.symm
    simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff, realized, structural] using values
  have readMatch := allocation.readList_matches structural
  have solved : A.Models assignment (selection.problem label source.rule before) := by
    simp only [Selection.problem, SubstitutionAction.models_append]
    exact ⟨⟨⟨oldSolved, (Selection.models_equations_iff A assignment label takeLength).mpr takeMatch⟩,
      (Selection.models_equations_iff A assignment label readMatch.length_eq).mpr readMatch⟩, source.tells⟩
  have valid : selection.Valid A label source.rule before := by
    refine ⟨distinctTakes, distinctMade, takeLength, readMatch.length_eq, outputValues, ?_, ⟨assignment, solved⟩, ?_⟩
    · refine ⟨?_, ?_, ?_, freshMade, ?_⟩
      · intro occurrence member
        exact (Finset.mem_sdiff.mp
          (takenPresent occurrence (by simpa [selection, Selection.commit] using member))).1
      · intro occurrence member
        have supported : occurrence ∈ readRows := by
          simpa only [selection, Selection.commit, allocation.readList_support] using member
        exact readSubset supported
      · apply Finset.disjoint_left.mpr
        intro occurrence takenMember readMember
        have outside := (Finset.mem_sdiff.mp
          (takenPresent occurrence (by simpa [selection, Selection.commit] using takenMember))).2
        apply outside
        simpa only [selection, Selection.commit, allocation.readList_support] using readMember
      · intro query member
        cases member
    · intro check member
      rw [source.noChecks] at member
      cases member
  refine ⟨selection, valid, solved, ⟨allocation.realization taken made⟩, ?_⟩
  have observed := (PositiveResourceProjection.resource_firing A structural valid solved).2
  exact observed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning
