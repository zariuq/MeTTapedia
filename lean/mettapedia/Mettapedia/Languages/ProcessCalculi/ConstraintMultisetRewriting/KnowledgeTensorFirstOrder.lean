import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceSchedules
import Mettapedia.Logic.LinearLogic.KnowledgeTensor

/-!
# The first-order step as tensor proofs over its knowledge

A configuration is read as two zones. Its knowledge is the set of solutions of its equation
store, ordered by inclusion, so that telling is intersection and equivalent stores are equal.
Its resources are the labels of its present occurrences, as a multiset of terms. Labels are
syntax and are not instantiated.

A use of a rule instance names the labels its take and read positions select. In the step a
position accepts any occurrence, and tells the equation between its pattern and the selected
label. So a use

* takes the selected take labels;
* reads one copy of each distinct selected read label and returns it, because read positions of
  one firing may share an occurrence;
* makes the rule's products;
* tells the position equations and the rule's own tell;
* is guarded by the rule's equality checks, asked of the knowledge after the tell.

Absence and counting checks are not guards on knowledge (`Asked`); they read the frame.

## Results

* `fires_of_valid`: an admitted firing whose checks are equality checks is a firing of the
  declared transition, with the complete residual frame.
* `valid_of_fires`: a firing of the declared transition whose resulting knowledge is consistent
  is realized by an admitted selection of occurrences, given a supply of fresh occurrences.
* `schedule_iff_proof`: executable schedules of equality-guarded rule instances are exactly the
  tensor proofs over the knowledge zone whose final knowledge is consistent, with the same uses
  in the same order. No assumption is made on the declared equality of terms, and no solution of
  the final store is fixed in advance.

Consistency is required only of the final knowledge, since knowledge only refines.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorFirstOrder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Logic.LinearLogic

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- A use of a rule instance: the instance and the labels its take and read positions select. -/
structure Use (T : Type uT) where
  rule : RuleInstance T
  taken : List T
  read : List T

/-- Each pattern with the label its position selected. -/
def pairs (patterns values : List T) : EquationStore T :=
  patterns.zipWith (fun pattern value => (pattern, value)) values

/-- What a use tells: its position equations and the rule's tell. -/
def Use.told (use : Use T) : EquationStore T :=
  pairs use.rule.take use.taken ++ pairs use.rule.read use.read ++ use.rule.tell

/-- A check as a guard on knowledge. Only equality checks are such guards. -/
def Asked (A : SubstitutionAction T S) (σ : S) : Check T → Prop
  | .equal left right => A.Solves σ (left, right)
  | .absent _ => False
  | .count _ _ => False

/-- All checks of the rule are equality checks. -/
def GuardsOnly (rule : RuleInstance T) : Prop :=
  ∀ check ∈ rule.checks, ∃ left right, check = Check.equal left right

theorem guard_of_asked {A : SubstitutionAction T S} {σ : S} {check : Check T}
    (asked : Asked A σ check) : ∃ left right, check = Check.equal left right := by
  cases check with
  | equal left right => exact ⟨left, right, rfl⟩
  | absent pattern => exact asked.elim
  | count pattern number => exact asked.elim

theorem holds_of_asked (A : SubstitutionAction T S) (σ : S) (label : O → T) (store : Finset O)
    {check : Check T} (asked : Asked A σ check) : check.Holds A σ label store := by
  cases check with
  | equal left right => exact asked
  | absent pattern => exact asked.elim
  | count pattern number => exact asked.elim

theorem asked_of_holds (A : SubstitutionAction T S) (σ : S) (label : O → T) (store : Finset O)
    {check : Check T} (guard : ∃ left right, check = Check.equal left right)
    (holds : check.Holds A σ label store) : Asked A σ check := by
  obtain ⟨left, right, rfl⟩ := guard
  exact holds

/-- The first-order step as declared transitions over sets of solutions. -/
def system [DecidableEq T] (A : SubstitutionAction T S) (program : Set (RuleInstance T)) :
    KnowledgeTensor.System (Set S) T (Use T) where
  take use := (use.taken : Multiset T)
  read use := (use.read.dedup : Multiset T)
  make use := (use.rule.produce : Multiset T)
  tell use := {σ | A.Models σ use.told}
  guard use known := use.rule ∈ program ∧ use.rule.take.length = use.taken.length ∧
    use.rule.read.length = use.read.length ∧
    ∀ check ∈ use.rule.checks, ∀ σ ∈ known, Asked A σ check
  guard_mono := fun _ _ _ refines holds =>
    ⟨holds.1, holds.2.1, holds.2.2.1,
      fun check member σ inside => holds.2.2.2 check member σ (refines inside)⟩

/-- The knowledge of a configuration: the solutions of its store. -/
def knowledge (A : SubstitutionAction T S) (C : Configuration T O) : Set S :=
  {σ | A.Models σ C.equations}

/-- The resources of a configuration: the labels of its present occurrences. -/
def resources (label : O → T) (C : Configuration T O) : Multiset T := labels label C.present

/-- The use a firing makes of its rule instance. -/
def useOf (label : O → T) (firing : ConditionalSchedule.Firing T O) : Use T :=
  ⟨firing.1, firing.2.taken.map label, firing.2.read.map label⟩

theorem equations_eq_pairs (label : O → T) (patterns : List T) (selected : List O) :
    Selection.equations label patterns selected = pairs patterns (selected.map label) := by
  simp only [Selection.equations, pairs, List.zipWith_map_right]

/-- The solutions of a firing's problem are the old knowledge refined by what the use tells. -/
theorem models_problem_iff [DecidableEq T] (A : SubstitutionAction T S) (program : Set (RuleInstance T))
    (label : O → T) (firing : ConditionalSchedule.Firing T O) (C : Configuration T O) (σ : S) :
    A.Models σ (firing.2.problem label firing.1 C) ↔
      σ ∈ knowledge A C ⊓ (system A program).tell (useOf label firing) := by
  show A.Models σ (firing.2.problem label firing.1 C) ↔
    A.Models σ C.equations ∧ A.Models σ (useOf label firing).told
  simp only [Selection.problem, Use.told, useOf, equations_eq_pairs, SubstitutionAction.models_append,
    and_assoc]

theorem labels_toFinset [DecidableEq O] (label : O → T) {items : List O} (distinct : items.Nodup) :
    labels label items.toFinset = ((items.map label : List T) : Multiset T) := by
  unfold labels
  rw [List.toFinset_val, distinct.dedup, Multiset.map_coe]

/-- Occurrences carrying given labels; they need not be distinct. -/
theorem exists_readers (label : O → T) : ∀ (values : List T) (world : Finset O),
    (∀ value ∈ values, value ∈ labels label world) →
      ∃ readers : List O, (∀ o ∈ readers, o ∈ world) ∧ readers.map label = values
  | [], _, _ => ⟨[], (fun _ member => (List.not_mem_nil member).elim), rfl⟩
  | value :: values, world, present => by
      obtain ⟨o, inWorld, atValue⟩ := Multiset.mem_map.mp (present value (List.mem_cons_self ..))
      obtain ⟨readers, inside, same⟩ := exists_readers label values world
        (fun other member => present other (List.mem_cons_of_mem _ member))
      refine ⟨o :: readers, ?_, ?_⟩
      · intro other member
        rcases List.mem_cons.mp member with rfl | later
        · exact Finset.mem_val.mp inWorld
        · exact inside other later
      · rw [List.map_cons, atValue, same]

/-- Fresh occurrences carrying given labels. -/
theorem fresh_outputs [DecidableEq O] (label : O → T)
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

/-- The labels of an admitted firing split into what it takes, one copy of each distinct label it
reads, and a frame; the result keeps the read labels and the frame and adds the products. -/
theorem resources_split [DecidableEq T] [DecidableEq O] (A : SubstitutionAction T S) (label : O → T)
    {rule : RuleInstance T} {selection : Selection O} {C : Configuration T O}
    (valid : selection.Valid A label rule C) :
    ∃ frame : Multiset T,
      labels label C.present = ((selection.taken.map label : List T) : Multiset T) +
        (((selection.read.map label).dedup : List T) : Multiset T) + frame ∧
      labels label (selection.result label rule C).present =
        (((selection.read.map label).dedup : List T) : Multiset T) +
          ((rule.produce : List T) : Multiset T) + frame := by
  have takenSub : selection.taken.toFinset ⊆ C.present := valid.occurrences.taken_subset
  have split : labels label C.present =
      labels label selection.taken.toFinset + labels label (C.present \ selection.taken.toFinset) := by
    rw [← labels_union_of_disjoint label Finset.disjoint_sdiff, Finset.union_sdiff_of_subset takenSub]
  have readLe : (((selection.read.map label).dedup : List T) : Multiset T) ≤
      labels label (C.present \ selection.taken.toFinset) := by
    unfold labels
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (List.nodup_dedup _))]
    intro value member
    rw [Multiset.mem_coe, List.mem_dedup, List.mem_map] at member
    obtain ⟨o, inRead, rfl⟩ := member
    refine Multiset.mem_map.mpr ⟨o, ?_, rfl⟩
    rw [Finset.mem_val, Finset.mem_sdiff]
    exact ⟨valid.occurrences.kept_subset (List.mem_toFinset.mpr inRead),
      fun inTaken => Finset.disjoint_left.mp valid.occurrences.apart inTaken (List.mem_toFinset.mpr inRead)⟩
  have restored := add_tsub_cancel_of_le readLe
  have apart : Disjoint (C.present \ selection.taken.toFinset) selection.made.toFinset :=
    Finset.disjoint_left.mpr fun o inRest inMade =>
      Finset.disjoint_left.mp valid.occurrences.fresh inMade (Finset.mem_sdiff.mp inRest).1
  have after : labels label (selection.result label rule C).present =
      labels label (C.present \ selection.taken.toFinset) + labels label selection.made.toFinset :=
    labels_union_of_disjoint label apart
  refine ⟨labels label (C.present \ selection.taken.toFinset) -
    (((selection.read.map label).dedup : List T) : Multiset T), ?_, ?_⟩
  · rw [split, labels_toFinset label valid.take_distinct, add_assoc, restored]
  · rw [after, labels_toFinset label valid.output_distinct, valid.outputs, add_right_comm, restored]

/-- **Soundness of one firing.** -/
theorem fires_of_valid [DecidableEq T] [DecidableEq O] (A : SubstitutionAction T S)
    (program : Set (RuleInstance T)) (label : O → T) {firing : ConditionalSchedule.Firing T O}
    {C : Configuration T O} (declared : firing.1 ∈ program) (guards : GuardsOnly firing.1)
    (valid : firing.2.Valid A label firing.1 C) :
    (system A program).Fires (useOf label firing) (knowledge A C) (resources label C)
      (knowledge A (firing.2.result label firing.1 C))
      (resources label (firing.2.result label firing.1 C)) := by
  obtain ⟨frame, source, target⟩ := resources_split A label valid
  have takeLength : firing.1.take.length = (firing.2.taken.map label).length := by
    rw [List.length_map]
    exact valid.take_length
  have readLength : firing.1.read.length = (firing.2.read.map label).length := by
    rw [List.length_map]
    exact valid.read_length
  have guarded : firing.1 ∈ program ∧ firing.1.take.length = (firing.2.taken.map label).length ∧
      firing.1.read.length = (firing.2.read.map label).length ∧
      ∀ check ∈ firing.1.checks,
        ∀ σ ∈ knowledge A C ⊓ (system A program).tell (useOf label firing), Asked A σ check :=
    ⟨declared, takeLength, readLength, fun check member σ inside =>
      asked_of_holds A σ label C.present (guards check member)
        (valid.checks check member σ ((models_problem_iff A program label firing C σ).mpr inside))⟩
  exact ⟨frame, source, guarded, Set.ext fun σ => models_problem_iff A program label firing C σ, target⟩

/-- **Completeness of one firing.** -/
theorem valid_of_fires [DecidableEq T] [DecidableEq O] (A : SubstitutionAction T S)
    (program : Set (RuleInstance T)) (label : O → T)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    {use : Use T} {C : Configuration T O} {known : Set S} {Γ' : Multiset T}
    (fires : (system A program).Fires use (knowledge A C) (resources label C) known Γ')
    (consistent : known.Nonempty) :
    ∃ selection : Selection O, selection.Valid A label use.rule C ∧
      useOf label (use.rule, selection) = use ∧ (use.rule ∈ program ∧ GuardsOnly use.rule) ∧
      knowledge A (selection.result label use.rule C) = known ∧
      resources label (selection.result label use.rule C) = Γ' := by
  have original := fires
  obtain ⟨frame, source, ⟨declared, takeLength, readLength, asked⟩, learned, -⟩ := fires
  obtain ⟨witness, inside⟩ := consistent
  rw [learned] at inside
  have guards : GuardsOnly use.rule := fun check member =>
    guard_of_asked (asked check member witness inside)
  have flat : labels label C.present =
      (use.taken : Multiset T) + ((use.read.dedup : Multiset T) + frame) :=
    source.trans (add_assoc _ _ _)
  have fits : (use.taken : Multiset T) ≤ labels label C.present := by
    rw [flat]
    exact Multiset.le_add_right _ _
  obtain ⟨taken, takenDistinct, takenIn, takenLabels⟩ :=
    GuardedMultisetRewriting.exists_occurrences label use.taken C.present fits
  have takenSub : taken.toFinset ⊆ C.present := fun o member => takenIn o (List.mem_toFinset.mp member)
  have split : labels label C.present =
      labels label taken.toFinset + labels label (C.present \ taken.toFinset) := by
    rw [← labels_union_of_disjoint label Finset.disjoint_sdiff, Finset.union_sdiff_of_subset takenSub]
  have restLabels : labels label (C.present \ taken.toFinset) =
      (use.read.dedup : Multiset T) + frame := by
    rw [labels_toFinset label takenDistinct, takenLabels] at split
    exact add_left_cancel (split.symm.trans flat)
  have readable : ∀ value ∈ use.read, value ∈ labels label (C.present \ taken.toFinset) := by
    intro value member
    rw [restLabels]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr (List.mem_dedup.mpr member)))
  obtain ⟨readers, readersIn, readerLabels⟩ :=
    exists_readers label use.read (C.present \ taken.toFinset) readable
  obtain ⟨made, madeDistinct, madeFresh, madeLabels⟩ :=
    fresh_outputs label supply use.rule.produce C.present
  have sameUse : useOf label (use.rule, (⟨taken, readers, made⟩ : Selection O)) = use :=
    congrArg₂ (Use.mk use.rule) takenLabels readerLabels
  have models := fun σ =>
    models_problem_iff A program label (use.rule, (⟨taken, readers, made⟩ : Selection O)) C σ
  rw [sameUse] at models
  have valid : (⟨taken, readers, made⟩ : Selection O).Valid A label use.rule C := by
    refine ⟨takenDistinct, madeDistinct, ?_, ?_, madeLabels, ⟨?_, ?_, ?_, madeFresh, ?_⟩,
      ⟨witness, (models witness).mpr inside⟩, ?_⟩
    · rw [takeLength, ← takenLabels, List.length_map]
    · rw [readLength, ← readerLabels, List.length_map]
    · exact fun o member => takenIn o (List.mem_toFinset.mp member)
    · exact fun o member => (Finset.mem_sdiff.mp (readersIn o (List.mem_toFinset.mp member))).1
    · exact Finset.disjoint_left.mpr fun o inTaken inRead =>
        (Finset.mem_sdiff.mp (readersIn o (List.mem_toFinset.mp inRead))).2 inTaken
    · intro query member
      cases member
    · intro check member σ solved
      exact holds_of_asked A σ label C.present (asked check member σ ((models σ).mp solved))
  have again := fires_of_valid A program label
    (firing := (use.rule, (⟨taken, readers, made⟩ : Selection O))) declared guards valid
  rw [sameUse] at again
  obtain ⟨sameKnowledge, sameResources⟩ := KnowledgeTensor.System.Fires.deterministic again original
  exact ⟨⟨taken, readers, made⟩, valid, sameUse, ⟨declared, guards⟩, sameKnowledge, sameResources⟩

/-- An executable schedule leaves a consistent store. -/
theorem follow_consistent [DecidableEq O] (A : SubstitutionAction T S) (label : O → T) :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) (C : Configuration T O),
      ConditionalSchedule.Executable A label C schedule →
        A.Consistent (ConditionalSchedule.follow label C schedule).equations
  | [], _, consistent => consistent
  | firing :: rest, C, executable =>
      follow_consistent A label rest (firing.2.result label firing.1 C) executable.2

/-- **Soundness.** An executable schedule of declared, equality-guarded rule instances is a run of
the declared transitions, from the reading of its start to the reading of its end. -/
theorem run_of_executable [DecidableEq T] [DecidableEq O] (A : SubstitutionAction T S)
    (program : Set (RuleInstance T)) (label : O → T) :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) (C : Configuration T O),
      ConditionalSchedule.Executable A label C schedule →
      (∀ firing ∈ schedule, firing.1 ∈ program ∧ GuardsOnly firing.1) →
      (system A program).Run (knowledge A C) (resources label C) (schedule.map (useOf label))
        (knowledge A (ConditionalSchedule.follow label C schedule))
        (resources label (ConditionalSchedule.follow label C schedule))
  | [], _, _, _ => KnowledgeTensor.System.Run.done _ _
  | firing :: rest, C, executable, declared =>
      KnowledgeTensor.System.Run.fire
        (fires_of_valid A program label (declared firing (List.mem_cons_self ..)).1
          (declared firing (List.mem_cons_self ..)).2 executable.1)
        (run_of_executable A program label rest (firing.2.result label firing.1 C) executable.2
          (fun other member => declared other (List.mem_cons_of_mem _ member)))

/-- **Completeness.** A run of the declared transitions that ends in consistent knowledge is
realized by an executable schedule from every configuration that reads as its start. -/
theorem executable_of_run [DecidableEq T] [DecidableEq O] (A : SubstitutionAction T S)
    (program : Set (RuleInstance T)) (label : O → T)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    {known finalKnown : Set S} {Γ Γ' : Multiset T} {uses : List (Use T)}
    (run : (system A program).Run known Γ uses finalKnown Γ') (consistent : finalKnown.Nonempty) :
    ∀ C : Configuration T O, knowledge A C = known → resources label C = Γ →
      ∃ schedule : List (ConditionalSchedule.Firing T O),
        ConditionalSchedule.Executable A label C schedule ∧
        (∀ firing ∈ schedule, firing.1 ∈ program ∧ GuardsOnly firing.1) ∧
        schedule.map (useOf label) = uses ∧
        knowledge A (ConditionalSchedule.follow label C schedule) = finalKnown ∧
        resources label (ConditionalSchedule.follow label C schedule) = Γ' := by
  induction run with
  | done known Γ =>
      intro C sameKnowledge sameResources
      subst sameKnowledge
      exact ⟨[], consistent, (fun _ member => (List.not_mem_nil member).elim), rfl, rfl, sameResources⟩
  | @fire use known middleKnown finalKnown Γ Γ₁ Γ' rest fires later ih =>
      intro C sameKnowledge sameResources
      subst sameKnowledge sameResources
      have middleConsistent : middleKnown.Nonempty :=
        Set.Nonempty.mono (KnowledgeTensor.System.Run.refines later) consistent
      obtain ⟨selection, valid, sameUse, declared, nextKnowledge, nextResources⟩ :=
        valid_of_fires A program label supply fires middleConsistent
      obtain ⟨schedule, executable, allDeclared, sameUses, finalKnowledge, finalResources⟩ :=
        ih consistent (selection.result label use.rule C) nextKnowledge nextResources
      refine ⟨(use.rule, selection) :: schedule, ⟨valid, executable⟩, ?_, ?_, finalKnowledge, finalResources⟩
      · intro firing member
        rcases List.mem_cons.mp member with rfl | inside
        · exact declared
        · exact allDeclared firing inside
      · rw [List.map_cons, sameUse, sameUses]

/-- **Runs correspond to proofs for the first-order step.** Executable schedules of declared,
equality-guarded rule instances are exactly the tensor proofs over the knowledge zone that end in
consistent knowledge, with the same uses in the same order. -/
theorem schedule_iff_proof [DecidableEq T] [DecidableEq O] (A : SubstitutionAction T S)
    (program : Set (RuleInstance T)) (label : O → T)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (C : Configuration T O) (uses : List (Use T)) (finalKnown : Set S) (Γ' : Multiset T) :
    (∃ schedule : List (ConditionalSchedule.Firing T O),
      ConditionalSchedule.Executable A label C schedule ∧
      (∀ firing ∈ schedule, firing.1 ∈ program ∧ GuardsOnly firing.1) ∧
      schedule.map (useOf label) = uses ∧
      knowledge A (ConditionalSchedule.follow label C schedule) = finalKnown ∧
      resources label (ConditionalSchedule.follow label C schedule) = Γ') ↔
      (system A program).Derives (knowledge A C) (resources label C) uses finalKnown Γ' ∧
        finalKnown.Nonempty := by
  constructor
  · rintro ⟨schedule, executable, declared, rfl, rfl, rfl⟩
    exact ⟨KnowledgeTensor.System.Run.derives (run_of_executable A program label schedule C executable declared),
      follow_consistent A label schedule C executable⟩
  · rintro ⟨proof, consistent⟩
    exact executable_of_run A program label supply (KnowledgeTensor.System.Derives.run proof) consistent C rfl rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorFirstOrder
