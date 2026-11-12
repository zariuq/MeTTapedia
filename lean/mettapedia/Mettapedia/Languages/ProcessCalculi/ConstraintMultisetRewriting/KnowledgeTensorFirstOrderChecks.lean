import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorFirstOrder
import Mettapedia.Logic.LinearLogic.KnowledgeTensorFrameGrades

/-!
# The first-order step with all its checks, as graded tensor proofs

An equality check is a guard on knowledge. An absence check and a counting check read every
present occurrence, through its label only (`holds_iff_holdsOn`). Read on the two zones, the
present labels are the premises of the use and the residual frame, so these checks are checks
on the frame in the sense of `CheckedSystem`.

## Results

* `checked_fires_of_valid`, `valid_of_checked_fires`: an admitted firing of any rule instance is
  a firing of the checked declared transition, and conversely given consistency and a supply of
  fresh occurrences.
* `schedule_iff_graded_proof`: executable schedules of declared rule instances, with every kind
  of check, are exactly the graded tensor proofs whose grade admits the empty frame and whose
  final knowledge is consistent, with the same uses in the same order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorFirstOrder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Logic.LinearLogic

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- A check read on the multiset of present labels. -/
def HoldsOn (A : SubstitutionAction T S) (σ : S) : Check T → Multiset T → Prop
  | .equal left right, _ => A.Solves σ (left, right)
  | .absent pattern, store => ∀ value ∈ store, ¬ A.E (A.apply σ pattern) (A.apply σ value)
  | .count pattern number, store => by
      classical
      exact Multiset.card (store.filter fun value => A.E (A.apply σ pattern) (A.apply σ value)) = number

/-- **A check reads the present occurrences through their labels only.** -/
theorem holds_iff_holdsOn (A : SubstitutionAction T S) (σ : S) (label : O → T) (store : Finset O)
    (check : Check T) : check.Holds A σ label store ↔ HoldsOn A σ check (labels label store) := by
  cases check with
  | equal left right => exact Iff.rfl
  | absent pattern =>
      constructor
      · intro clear value member
        obtain ⟨o, inside, rfl⟩ := Multiset.mem_map.mp member
        exact clear o (Finset.mem_val.mp inside)
      · intro clear o inside
        exact clear (label o) (Multiset.mem_map.mpr ⟨o, Finset.mem_val.mpr inside, rfl⟩)
  | count pattern number =>
      classical
      have same : (Check.matches A σ label store pattern).card =
          Multiset.card ((labels label store).filter
            fun value => A.E (A.apply σ pattern) (A.apply σ value)) := by
        unfold Check.matches labels
        rw [Multiset.filter_map, Multiset.card_map]
        rfl
      show (Check.matches A σ label store pattern).card = number ↔
        Multiset.card ((labels label store).filter
          fun value => A.E (A.apply σ pattern) (A.apply σ value)) = number
      rw [same]

/-- The first-order step with every check, as declared transitions whose check reads the frame. -/
def checkedSystem [DecidableEq T] (A : SubstitutionAction T S) (program : Set (RuleInstance T)) :
    KnowledgeTensor.CheckedSystem (Set S) T (Use T) where
  take use := (use.taken : Multiset T)
  read use := (use.read.dedup : Multiset T)
  make use := (use.rule.produce : Multiset T)
  tell use := {σ | A.Models σ use.told}
  check use known frame := use.rule ∈ program ∧ use.rule.take.length = use.taken.length ∧
    use.rule.read.length = use.read.length ∧
    ∀ check ∈ use.rule.checks, ∀ σ ∈ known,
      HoldsOn A σ check ((use.taken : Multiset T) + (use.read.dedup : Multiset T) + frame)
  check_mono := fun _ _ _ _ refines holds =>
    ⟨holds.1, holds.2.1, holds.2.2.1,
      fun check member σ inside => holds.2.2.2 check member σ (refines inside)⟩

/-- **Soundness of one firing, with every check.** -/
theorem checked_fires_of_valid [DecidableEq T] [DecidableEq O] (A : SubstitutionAction T S)
    (program : Set (RuleInstance T)) (label : O → T) {firing : ConditionalSchedule.Firing T O}
    {C : Configuration T O} (declared : firing.1 ∈ program)
    (valid : firing.2.Valid A label firing.1 C) :
    (checkedSystem A program).Fires (useOf label firing) (knowledge A C) (resources label C)
      (knowledge A (firing.2.result label firing.1 C))
      (resources label (firing.2.result label firing.1 C)) := by
  obtain ⟨frame, source, target⟩ := resources_split A label valid
  have takeLength : firing.1.take.length = (firing.2.taken.map label).length := by
    rw [List.length_map]
    exact valid.take_length
  have readLength : firing.1.read.length = (firing.2.read.map label).length := by
    rw [List.length_map]
    exact valid.read_length
  have checks : ∀ check ∈ firing.1.checks,
      ∀ σ ∈ knowledge A C ⊓ (checkedSystem A program).tell (useOf label firing),
        HoldsOn A σ check (((firing.2.taken.map label : List T) : Multiset T) +
          (((firing.2.read.map label).dedup : List T) : Multiset T) + frame) := by
    intro check member σ inside
    rw [← source]
    exact (holds_iff_holdsOn A σ label C.present check).mp
      (valid.checks check member σ ((models_problem_iff A program label firing C σ).mpr inside))
  have checked : firing.1 ∈ program ∧ firing.1.take.length = (firing.2.taken.map label).length ∧
      firing.1.read.length = (firing.2.read.map label).length ∧
      ∀ check ∈ firing.1.checks,
        ∀ σ ∈ knowledge A C ⊓ (checkedSystem A program).tell (useOf label firing),
          HoldsOn A σ check (((firing.2.taken.map label : List T) : Multiset T) +
            (((firing.2.read.map label).dedup : List T) : Multiset T) + frame) :=
    ⟨declared, takeLength, readLength, checks⟩
  exact ⟨frame, source, checked, Set.ext fun σ => models_problem_iff A program label firing C σ, target⟩

/-- **Completeness of one firing, with every check.** -/
theorem valid_of_checked_fires [DecidableEq T] [DecidableEq O] (A : SubstitutionAction T S)
    (program : Set (RuleInstance T)) (label : O → T)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    {use : Use T} {C : Configuration T O} {known : Set S} {Γ' : Multiset T}
    (fires : (checkedSystem A program).Fires use (knowledge A C) (resources label C) known Γ')
    (consistent : known.Nonempty) :
    ∃ selection : Selection O, selection.Valid A label use.rule C ∧
      useOf label (use.rule, selection) = use ∧ use.rule ∈ program ∧
      knowledge A (selection.result label use.rule C) = known ∧
      resources label (selection.result label use.rule C) = Γ' := by
  have original := fires
  obtain ⟨frame, source, ⟨declared, takeLength, readLength, checks⟩, learned, -⟩ := fires
  obtain ⟨witness, inside⟩ := consistent
  rw [learned] at inside
  have present : labels label C.present =
      (use.taken : Multiset T) + (use.read.dedup : Multiset T) + frame := source
  have flat : labels label C.present =
      (use.taken : Multiset T) + ((use.read.dedup : Multiset T) + frame) :=
    present.trans (add_assoc _ _ _)
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
      have on := checks check member σ ((models σ).mp solved)
      rw [← present] at on
      exact (holds_iff_holdsOn A σ label C.present check).mpr on
  have again := checked_fires_of_valid A program label
    (firing := (use.rule, (⟨taken, readers, made⟩ : Selection O))) declared valid
  rw [sameUse] at again
  obtain ⟨sameKnowledge, sameResources⟩ :=
    KnowledgeTensor.CheckedSystem.Fires.deterministic again original
  exact ⟨⟨taken, readers, made⟩, valid, sameUse, declared, sameKnowledge, sameResources⟩

/-- **Soundness, with every check.** -/
theorem checked_run_of_executable [DecidableEq T] [DecidableEq O] (A : SubstitutionAction T S)
    (program : Set (RuleInstance T)) (label : O → T) :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) (C : Configuration T O),
      ConditionalSchedule.Executable A label C schedule →
      (∀ firing ∈ schedule, firing.1 ∈ program) →
      (checkedSystem A program).Run (knowledge A C) (resources label C) (schedule.map (useOf label))
        (knowledge A (ConditionalSchedule.follow label C schedule))
        (resources label (ConditionalSchedule.follow label C schedule))
  | [], _, _, _ => KnowledgeTensor.CheckedSystem.Run.done _ _
  | firing :: rest, C, executable, declared =>
      KnowledgeTensor.CheckedSystem.Run.fire
        (checked_fires_of_valid A program label (declared firing (List.mem_cons_self ..)) executable.1)
        (checked_run_of_executable A program label rest (firing.2.result label firing.1 C) executable.2
          (fun other member => declared other (List.mem_cons_of_mem _ member)))

/-- **Completeness, with every check.** -/
theorem executable_of_checked_run [DecidableEq T] [DecidableEq O] (A : SubstitutionAction T S)
    (program : Set (RuleInstance T)) (label : O → T)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    {known finalKnown : Set S} {Γ Γ' : Multiset T} {uses : List (Use T)}
    (run : (checkedSystem A program).Run known Γ uses finalKnown Γ') (consistent : finalKnown.Nonempty) :
    ∀ C : Configuration T O, knowledge A C = known → resources label C = Γ →
      ∃ schedule : List (ConditionalSchedule.Firing T O),
        ConditionalSchedule.Executable A label C schedule ∧
        (∀ firing ∈ schedule, firing.1 ∈ program) ∧
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
        Set.Nonempty.mono (KnowledgeTensor.CheckedSystem.Run.refines later) consistent
      obtain ⟨selection, valid, sameUse, declared, nextKnowledge, nextResources⟩ :=
        valid_of_checked_fires A program label supply fires middleConsistent
      obtain ⟨schedule, executable, allDeclared, sameUses, finalKnowledge, finalResources⟩ :=
        ih consistent (selection.result label use.rule C) nextKnowledge nextResources
      refine ⟨(use.rule, selection) :: schedule, ⟨valid, executable⟩, ?_, ?_, finalKnowledge, finalResources⟩
      · intro firing member
        rcases List.mem_cons.mp member with rfl | inside
        · exact declared
        · exact allDeclared firing inside
      · rw [List.map_cons, sameUse, sameUses]

/-- **Runs correspond to graded proofs for the first-order step with every check.** Executable
schedules of declared rule instances are exactly the graded tensor proofs whose grade admits the
empty frame and whose final knowledge is consistent, with the same uses in the same order. -/
theorem schedule_iff_graded_proof [DecidableEq T] [DecidableEq O] (A : SubstitutionAction T S)
    (program : Set (RuleInstance T)) (label : O → T)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (C : Configuration T O) (uses : List (Use T)) (finalKnown : Set S) (Γ' : Multiset T) :
    (∃ schedule : List (ConditionalSchedule.Firing T O),
      ConditionalSchedule.Executable A label C schedule ∧
      (∀ firing ∈ schedule, firing.1 ∈ program) ∧
      schedule.map (useOf label) = uses ∧
      knowledge A (ConditionalSchedule.follow label C schedule) = finalKnown ∧
      resources label (ConditionalSchedule.follow label C schedule) = Γ') ↔
      (∃ grade : Multiset T → Prop, grade 0 ∧
        (checkedSystem A program).Proves (knowledge A C) (resources label C) grade uses finalKnown Γ') ∧
        finalKnown.Nonempty := by
  constructor
  · rintro ⟨schedule, executable, declared, rfl, rfl, rfl⟩
    exact ⟨KnowledgeTensor.CheckedSystem.Run.proves
        (checked_run_of_executable A program label schedule C executable declared),
      follow_consistent A label schedule C executable⟩
  · rintro ⟨⟨grade, atZero, proof⟩, consistent⟩
    have run : (checkedSystem A program).Run (knowledge A C) (resources label C) uses finalKnown Γ' := by
      simpa only [add_zero] using KnowledgeTensor.CheckedSystem.Proves.run proof 0 atZero
    exact executable_of_checked_run A program label supply run consistent C rfl rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorFirstOrder
