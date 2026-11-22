import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Step
import Mettapedia.GSLT.Causality.ResourceReads

/-!
# Realized constraint firings in the existing resource semantics

One solution of the complete post-firing equation store interprets every
selected and surviving occurrence together. The actual selection then gives
an enabled firing of `ResourceInteraction.System`: take and produce retain
their list multiplicities, while reads are counted once per physical identity.

For the no-read, no-check profile, every bag frame decomposition lifts back
to an ordinary constraint firing, provided the occurrence supply has a fresh
identity for every output value. This is a resource-planning comparison, not
a theorem about linear connection proof objects, concurrency, or a native
runtime. Atomic take-and-republish keeps the sequential firing observation;
it does not assert preservation of concurrent independence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceProjection

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.Causality

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S)

def realized (assignment : S) (label : O → T) : O → T :=
  fun occurrence => A.apply assignment (label occurrence)

/-- The read resource is the physical support of the selection, rather than
the possibly repeated list of pattern ports. -/
def readFootprint (assignment : S) (label : O → T) (selection : Selection O) : Multiset T :=
  labels (realized A assignment label) selection.read.toFinset

/-- Ground resource instances retain the source rule and its actual physical
selection. Solving their equations remains an independent constraint receipt. -/
def resources (assignment : S) (label : O → T) :
    ResourceInteraction.System.{uT, max uT uO} T where
  Site := ULift.{uO} (RuleInstance T)
  Instance _ := ULift.{uT} (Selection O)
  consume := fun {rule} _ => (rule.down.take.map (A.apply assignment) : Multiset T)
  read := fun selection => readFootprint A assignment label selection.down
  produce := fun {rule} _ => (rule.down.produce.map (A.apply assignment) : Multiset T)

omit [DecidableEq O] in
private theorem mapped_matching {assignment : S} {label : O → T}
    (structural : A.E = Eq) {patterns : List T} {selected : List O}
    (matched : List.Forall₂ (fun pattern occurrence =>
      A.E (A.apply assignment pattern) (A.apply assignment (label occurrence))) patterns selected) :
    patterns.map (A.apply assignment) = selected.map (realized A assignment label) := by
  induction matched with
  | nil => rfl
  | cons same rest earlier =>
      rw [structural] at same
      exact congrArg₂ List.cons same earlier

theorem take_observation {assignment : S} {label : O → T} {selection : Selection O}
    {rule : RuleInstance T} {before : Configuration T O} (structural : A.E = Eq)
    (valid : selection.Valid A label rule before)
    (solved : A.Models assignment (selection.problem label rule before)) :
    labels (realized A assignment label) selection.taken.toFinset =
      (rule.take.map (A.apply assignment) : Multiset T) := by
  rw [GuardedMultisetRewriting.labels_toFinset _ valid.take_distinct]
  exact congrArg (fun values : List T => (values : Multiset T))
    (mapped_matching A structural (Selection.models_problem A valid solved).2.1).symm

theorem output_observation {assignment : S} {label : O → T} {selection : Selection O}
    {rule : RuleInstance T} {before : Configuration T O}
    (valid : selection.Valid A label rule before) :
    labels (realized A assignment label) selection.made.toFinset =
      (rule.produce.map (A.apply assignment) : Multiset T) := by
  rw [GuardedMultisetRewriting.labels_toFinset _ valid.output_distinct]
  have outputs := congrArg (List.map (A.apply assignment)) valid.outputs
  change (selection.made.map (fun occurrence => A.apply assignment (label occurrence)) : Multiset T) = _
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun values : List T => (values : Multiset T)) outputs

/-- The surviving frame contains every selected read occurrence. Every term
is interpreted under the same solution, including unchanged frame syntax. -/
theorem observed_frame [DecidableEq T] {assignment : S} {label : O → T}
    {selection : Selection O} {rule : RuleInstance T} {before : Configuration T O}
    (structural : A.E = Eq) (valid : selection.Valid A label rule before)
    (solved : A.Models assignment (selection.problem label rule before)) :
    ∃ frame : Multiset T,
      labels (realized A assignment label) before.present =
        frame + (rule.take.map (A.apply assignment) : Multiset T) ∧
      labels (realized A assignment label) (selection.result label rule before).present =
        frame + (rule.produce.map (A.apply assignment) : Multiset T) ∧
      readFootprint A assignment label selection ≤ frame := by
  let frame := labels (realized A assignment label) (before.present \ selection.taken.toFinset)
  have split : labels (realized A assignment label) before.present =
      frame + labels (realized A assignment label) selection.taken.toFinset := by
    have takenSubset : selection.taken.toFinset ⊆ before.present := valid.occurrences.taken_subset
    rw [← labels_union_of_disjoint _ Finset.sdiff_disjoint,
      Finset.sdiff_union_of_subset takenSubset]
  have takeValue := take_observation A structural valid solved
  refine ⟨frame, by rw [← takeValue]; exact split, ?_, ?_⟩
  · have physical := valid.occurrences
    have enabled : Enabled (realized A assignment label) before.present selection.commit :=
      ⟨physical.taken_subset, physical.kept_subset, physical.apart, physical.fresh,
        fun query member => by cases member⟩
    change labels (realized A assignment label) (fire before.present selection.commit) = _
    rw [labels_fire enabled, show selection.commit.taken = selection.taken.toFinset from rfl,
      show selection.commit.made = selection.made.toFinset from rfl,
      output_observation A valid, split, add_tsub_cancel_right]
  · apply labels_mono
    intro occurrence read
    exact Finset.mem_sdiff.mpr ⟨valid.occurrences.kept_subset read,
      fun taken => Finset.disjoint_left.mp valid.occurrences.apart taken read⟩

theorem resource_firing [DecidableEq T] {assignment : S} {label : O → T}
    {selection : Selection O} {rule : RuleInstance T} {before : Configuration T O}
    (structural : A.E = Eq) (valid : selection.Valid A label rule before)
    (solved : A.Models assignment (selection.problem label rule before)) :
    (resources A assignment label).Enables
        (labels (realized A assignment label) before.present) (site := ⟨rule⟩) ⟨selection⟩ ∧
      labels (realized A assignment label) (selection.result label rule before).present =
        (resources A assignment label).fire
          (labels (realized A assignment label) before.present) (site := ⟨rule⟩) ⟨selection⟩ := by
  obtain ⟨frame, source, destination, reads⟩ := observed_frame A structural valid solved
  constructor
  · change (rule.take.map (A.apply assignment) : Multiset T) +
      readFootprint A assignment label selection ≤ _
    rw [source, add_comm frame]
    exact add_le_add le_rfl reads
  · change _ = _ - (rule.take.map (A.apply assignment) : Multiset T) +
      (rule.produce.map (A.apply assignment) : Multiset T)
    rw [source, add_tsub_cancel_right, destination]

/-- The established atomic take-and-republish rendering applies after the
read ports have been normalized to their actual physical support. -/
theorem atomic_linear_rendering [DecidableEq T] {assignment : S} {label : O → T}
    {selection : Selection O} {rule : RuleInstance T} {before : Configuration T O}
    (structural : A.E = Eq) (valid : selection.Valid A label rule before)
    (solved : A.Models assignment (selection.problem label rule before)) :
    (resources A assignment label).takeRepublish.Enables
        (labels (realized A assignment label) before.present) (site := ⟨rule⟩) ⟨selection⟩ ∧
      labels (realized A assignment label) (selection.result label rule before).present =
        (resources A assignment label).takeRepublish.fire
          (labels (realized A assignment label) before.present) (site := ⟨rule⟩) ⟨selection⟩ := by
  obtain ⟨enabled, target⟩ := resource_firing A structural valid solved
  exact ⟨((resources A assignment label).takeRepublish_enables_iff _ ⟨selection⟩).mpr enabled,
    target.trans ((resources A assignment label).takeRepublish_fire _ ⟨selection⟩ enabled).symm⟩

private theorem fresh_outputs (label : O → T)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value) :
    ∀ (values : List T) (world : Finset O), ∃ made : List O,
      made.Nodup ∧ Disjoint made.toFinset world ∧ made.map label = values
  | [], _ => ⟨[], by simp, by simp, rfl⟩
  | value :: values, world => by
      obtain ⟨occurrence, fresh, atValue⟩ := supply world value
      obtain ⟨made, distinct, away, outputs⟩ := fresh_outputs label supply values (insert occurrence world)
      have absent : occurrence ∉ made := fun member =>
        Finset.disjoint_left.mp away (by simpa using member) (by simp)
      refine ⟨occurrence :: made, List.nodup_cons.mpr ⟨absent, distinct⟩, ?_, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro item inMade inWorld
        rcases List.mem_cons.mp (by simpa using inMade) with rfl | member
        · exact fresh inWorld
        · exact Finset.disjoint_left.mp away (by simpa using member) (by simp [inWorld])
      · simp [outputs, atValue]

/-- A complete bag frame lifts to a real selection of distinct consumed
occurrences and fresh raw outputs. Equal observed values need not have equal
identities. No local matching or solver completeness is assumed. -/
theorem lift_no_read_frame [DecidableEq T] (assignment : S) (label : O → T)
    (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (rule : RuleInstance T) (noReads : rule.read = []) (noChecks : rule.checks = [])
    (before : Configuration T O) (oldSolved : A.Models assignment before.equations)
    (tellsSolved : A.Models assignment rule.tell)
    (frame : Multiset T)
    (source : labels (realized A assignment label) before.present =
      frame + (rule.take.map (A.apply assignment) : Multiset T)) :
    ∃ selection : Selection O, selection.Valid A label rule before ∧
      A.Models assignment (selection.result label rule before).equations ∧
      labels (realized A assignment label) (selection.result label rule before).present =
        frame + (rule.produce.map (A.apply assignment) : Multiset T) := by
  have fits : (rule.take.map (A.apply assignment) : Multiset T) ≤
      labels (realized A assignment label) before.present := by
    rw [source]
    exact Multiset.le_add_left _ _
  obtain ⟨taken, distinctTakes, inWorld, takeValues⟩ :=
    GuardedMultisetRewriting.exists_occurrences (realized A assignment label)
      (rule.take.map (A.apply assignment)) before.present fits
  obtain ⟨made, distinctOutputs, freshOutputs, outputs⟩ := fresh_outputs label supply rule.produce before.present
  let selection : Selection O := ⟨taken, [], made⟩
  have takeLengths : rule.take.length = taken.length := by
    have count := congrArg List.length takeValues
    simpa using count.symm
  have takeMatch : List.Forall₂ (fun pattern occurrence =>
      A.E (A.apply assignment pattern) (A.apply assignment (label occurrence))) rule.take taken := by
    rw [structural]
    have same : List.Forall₂ Eq (rule.take.map (A.apply assignment))
        (taken.map (realized A assignment label)) := by
      rw [List.forall₂_eq_eq_eq]
      exact takeValues.symm
    simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff, realized] using same
  have solved : A.Models assignment (selection.problem label rule before) := by
    simp only [Selection.problem, SubstitutionAction.models_append]
    refine ⟨⟨⟨oldSolved, ?_⟩, ?_⟩, tellsSolved⟩
    · exact (Selection.models_equations_iff A assignment label takeLengths).mpr takeMatch
    · simp [noReads, selection, Selection.equations]
  have valid : selection.Valid A label rule before := by
    refine ⟨distinctTakes, distinctOutputs, takeLengths, by simp [noReads, selection], outputs, ?_, ⟨assignment, solved⟩, ?_⟩
    · refine ⟨?_, by simp [selection, Selection.commit], by simp [selection, Selection.commit], freshOutputs, ?_⟩
      · intro occurrence member
        exact inWorld occurrence (by simpa [selection, Selection.commit] using member)
      · intro query member
        cases member
    · simp [noChecks]
  obtain ⟨actualFrame, actualSource, actualTarget, _⟩ := observed_frame A structural valid solved
  have sameFrame : actualFrame = frame := by
    apply add_right_cancel (b := (rule.take.map (A.apply assignment) : Multiset T))
    exact actualSource.symm.trans source
  exact ⟨selection, valid, solved, sameFrame ▸ actualTarget⟩

/-- Exact bag-observed adequacy of take/produce planning under one shared
solution. The forward direction retains the original tell and equation
obligations; the reverse constructs the actual physical selection. This does
not identify different selections with the same bag observation. -/
theorem no_read_firing_iff_frame [DecidableEq T] (assignment : S) (label : O → T)
    (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (rule : RuleInstance T) (noReads : rule.read = []) (noChecks : rule.checks = [])
    (before : Configuration T O) (afterBag : Multiset T) :
    (∃ selection : Selection O, selection.Valid A label rule before ∧
      A.Models assignment (selection.result label rule before).equations ∧
      labels (realized A assignment label) (selection.result label rule before).present = afterBag) ↔
      A.Models assignment before.equations ∧ A.Models assignment rule.tell ∧
        ∃ frame : Multiset T,
          labels (realized A assignment label) before.present =
            frame + (rule.take.map (A.apply assignment) : Multiset T) ∧
          afterBag = frame + (rule.produce.map (A.apply assignment) : Multiset T) := by
  constructor
  · rintro ⟨selection, valid, solved, observed⟩
    have models := Selection.models_problem A valid solved
    obtain ⟨frame, source, destination, _⟩ := observed_frame A structural valid solved
    exact ⟨models.1, models.2.2.2, frame, source, observed.symm.trans destination⟩
  · rintro ⟨oldSolved, tellsSolved, frame, source, rfl⟩
    exact lift_no_read_frame A assignment label structural supply rule noReads noChecks
      before oldSolved tellsSolved frame source

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceProjection
