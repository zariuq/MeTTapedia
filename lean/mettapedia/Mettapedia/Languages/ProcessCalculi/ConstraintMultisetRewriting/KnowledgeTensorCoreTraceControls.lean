import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreFootprint
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreGrade
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreInterchange
import Mettapedia.Logic.LinearLogic.KnowledgeTensorTraces

/-!
# Controls for grades, tokens and the interchange law

* **The grade functor on the two controls.** It is defined at the placement beside the
  occurrence `9` for the run that reads (`grade_functor_defined_for_reads`) and undefined there
  for the run that checks absence (`grade_functor_undefined_for_absence`).
* **Absence has no guard transport** (`absence_has_no_guard_transport`), and its firing is a
  framed leaf at its footprint (`unless_nine_is_a_framed_leaf`).
* **A swap of uses is not a swap of events.** Two tokens are labelled `5`. The firing `move`
  takes one and makes a new one; `turn` takes the one `move` made. On labels the two uses are
  independent and the swapped word runs (`the_uses_are_independent`,
  `the_swapped_uses_run_on_labels`). On occurrences `move` then `turn` is a native run and no
  native run has the word `turn`, `move` (`no_transposed_run`). Proof identity on labels and
  the native trace quotient on occurrence identities are different relations.
* **The interchange law fails for counting, with all three tensors present.** On one side a
  firing counts exactly one occurrence. On the other side one firing adds an occurrence and a
  second removes it. The cut of the two tensors runs `adds`, `removes`, `counts`; the tensor of
  the two cuts runs `counts`, `adds`, `removes`. Both are native runs and they are not one trace
  (`not_one_trace`, `interchange_fails_for_counting`): between `adds` and `removes` the count is
  two. So the three grades do not imply the interchange law; separation does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Logic.LinearLogic
open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrder
open KnowledgeTensorFirstOrderControls (plain one unlessNine makeSeven)

/-! ## The grade functor on the two controls -/

theorem grade_functor_defined_for_reads :
    (runAction (contextualRunInterpretation plain id) nine readsRun PUnit.unit).Dom :=
  (gradeFunctor_dom (contextualRunInterpretation plain id) nine readsRun PUnit.unit).mpr
    ⟨⟨reads_frames_nine, (valid_tensor_iff plain id reads reads_admitted).mp
      reads_is_admitted_beside_nine⟩, trivial⟩

theorem grade_functor_undefined_for_absence :
    ¬ (runAction (contextualRunInterpretation plain id) nine unlessNineRun PUnit.unit).Dom :=
  fun defined => absence_grade_is_not_structural.2
    ((gradeFunctor_dom (contextualRunInterpretation plain id) nine unlessNineRun PUnit.unit).mp defined)

/-! ## Absence: no guard transport, and a framed leaf at its footprint -/

theorem absence_has_no_guard_transport :
    IsEmpty (GuardTransportAt (contextualRunInterpretation plain id) (left := one) (right := nine)
      PUnit.unit unlessNineFiring) :=
  ⟨fun transport => absence_is_not_stable
    (stableAt_of_guardTransport (contextualRunInterpretation plain id) transport)⟩

theorem unless_nine_is_a_framed_leaf :
    ∃ (leaf : unlessNineFiring.Valid plain id (FirstOrder.footprint one unlessNineFiring))
      (native : (firstOrder plain id).toStep.Run
        (AnnotatedRuns.tensor (FirstOrder.footprint one unlessNineFiring)
          (FirstOrder.rest one unlessNineFiring))),
      Places (contextualRunInterpretation plain id)
        (left := FirstOrder.footprint one unlessNineFiring)
        (right := FirstOrder.rest one unlessNineFiring) PUnit.unit (.cons unlessNineFiring leaf (.nil _))
        native ∧
      Nonempty ((firstOrderTransport plain id).Iso
        (AnnotatedRuns.tensor (FirstOrder.footprint one unlessNineFiring)
          (FirstOrder.rest one unlessNineFiring)) one) :=
  FirstOrder.event_is_framed_leaf plain id unless_nine_admitted FirstOrder.absence_shrinks rfl

/-! ## A swap of uses is not a swap of events -/

/-- Occurrence `2` is labelled `6`; every other occurrence is labelled `5`. -/
def tokenLabel (occurrence : Nat) : Nat := if occurrence = 2 then 6 else 5

def moveRule : RuleInstance Nat := ⟨[5], [], [], [], [5]⟩

def turnRule : RuleInstance Nat := ⟨[5], [], [], [], [6]⟩

/-- Takes occurrence `0` and makes occurrence `1`. -/
def move : Firing Nat Unit Nat := ⟨moveRule, [], ⟨[0], [], [1]⟩⟩

/-- Takes occurrence `1`, the one `move` makes, and makes occurrence `2`. -/
def turn : Firing Nat Unit Nat := ⟨turnRule, [], ⟨[1], [], [2]⟩⟩

/-- Two tokens labelled `5`: occurrences `0` and `3`. -/
def start : Configuration Nat Nat := ⟨[], {0, 3}⟩

theorem move_admitted : move.Valid plain tokenLabel start := by
  refine ⟨⟨List.nodup_singleton 0, List.nodup_singleton 1, rfl, rfl, rfl, by decide, ⟨(), ?_⟩, ?_⟩, ?_⟩
  · intro equation member
    have shape : move.selection.problem tokenLabel move.rule start = [(5, 5)] := rfl
    rw [shape] at member
    obtain rfl := List.mem_singleton.mp member
    exact rfl
  · intro check member
    cases member
  · intro query member
    cases member

theorem turn_after_move : turn.Valid plain tokenLabel (move.result tokenLabel start) := by
  refine ⟨⟨List.nodup_singleton 1, List.nodup_singleton 2, rfl, rfl, rfl, by decide, ⟨(), ?_⟩, ?_⟩, ?_⟩
  · intro equation member
    have shape : turn.selection.problem tokenLabel turn.rule (move.result tokenLabel start) =
        [(5, 5), (5, 5)] := rfl
    rw [shape] at member
    rcases List.mem_cons.mp member with rfl | later
    · exact rfl
    · obtain rfl := List.mem_singleton.mp later
      exact rfl
  · intro check member
    cases member
  · intro query member
    cases member

theorem turn_not_first : ¬ turn.Valid plain tokenLabel start := by
  intro valid
  have inside : ([1] : List Nat).toFinset ⊆ ({0, 3} : Finset Nat) :=
    valid.firing.occurrences.taken_subset
  exact absurd inside (by decide)

/-- The native run: `move`, then `turn`. -/
def straight : (firstOrder plain tokenLabel).toStep.Run start :=
  .cons move move_admitted (.cons turn turn_after_move (.nil _))

theorem straight_word : sites plain tokenLabel straight = [move, turn] := rfl

theorem no_transposed_run :
    ¬ ∃ run : (firstOrder plain tokenLabel).toStep.Run start,
      sites plain tokenLabel run = [turn, move] := by
  rintro ⟨run, word⟩
  have executable := executable_of_nonempty plain tokenLabel run
    (by rw [word]; exact List.cons_ne_nil _ _)
  rw [word] at executable
  exact turn_not_first executable.1

theorem the_uses_are_independent :
    (system plain {moveRule, turnRule}).Independent (useOf tokenLabel move.plain)
      (useOf tokenLabel turn.plain) (knowledge plain start) (resources tokenLabel start) := by
  refine ⟨0, by decide, le_of_eq rfl, le_of_eq rfl, ?_, ?_⟩
  · exact ⟨Set.mem_insert moveRule _, rfl, rfl, fun check member => by cases member⟩
  · exact ⟨Set.mem_insert_of_mem _ (Set.mem_singleton turnRule), rfl, rfl,
      fun check member => by cases member⟩

theorem the_swapped_uses_run_on_labels :
    ∃ (known : Set Unit) (left : Multiset Nat),
      (system plain {moveRule, turnRule}).Run (knowledge plain start) (resources tokenLabel start)
        [useOf tokenLabel turn.plain, useOf tokenLabel move.plain] known left := by
  obtain ⟨known, left, _, swapped⟩ := the_uses_are_independent.diamond
  exact ⟨known, left, swapped⟩

/-- **A swap of uses is not a swap of events.** -/
theorem a_swap_of_uses_is_not_a_swap_of_events :
    (∃ (known : Set Unit) (left : Multiset Nat),
      (system plain {moveRule, turnRule}).Run (knowledge plain start) (resources tokenLabel start)
        [useOf tokenLabel turn.plain, useOf tokenLabel move.plain] known left) ∧
      sites plain tokenLabel straight = [move, turn] ∧
      ¬ ∃ run : (firstOrder plain tokenLabel).toStep.Run start,
        sites plain tokenLabel run = [turn, move] :=
  ⟨the_swapped_uses_run_on_labels, straight_word, no_transposed_run⟩

/-! ## The interchange law fails for counting -/

/-- Makes occurrence `7`. -/
def adds : Firing Nat Unit Nat := ⟨⟨[], [], [], [], [5]⟩, [], ⟨[], [], [7]⟩⟩

/-- Takes occurrence `7`. -/
def removes : Firing Nat Unit Nat := ⟨⟨[5], [], [], [], []⟩, [], ⟨[7], [], []⟩⟩

/-- No knowledge and no occurrence. -/
def empty : Configuration Nat Nat := ⟨[], ∅⟩

theorem counts_problem_solved (number : Nat) {C : Configuration Nat Nat}
    (solved : plain.Models () C.equations) :
    plain.Models () ((counts number).selection.problem five (counts number).rule C) := by
  have shape : (counts number).selection.problem five (counts number).rule C =
      C.equations ++ [] ++ [] ++ [] := rfl
  rw [shape, List.append_nil, List.append_nil, List.append_nil]
  exact solved

theorem adds_problem_solved {C : Configuration Nat Nat} (solved : plain.Models () C.equations) :
    plain.Models () (adds.selection.problem five adds.rule C) := by
  have shape : adds.selection.problem five adds.rule C = C.equations ++ [] ++ [] ++ [] := rfl
  rw [shape, List.append_nil, List.append_nil, List.append_nil]
  exact solved

theorem removes_problem_solved {C : Configuration Nat Nat} (solved : plain.Models () C.equations) :
    plain.Models () (removes.selection.problem five removes.rule C) := by
  have shape : removes.selection.problem five removes.rule C =
      C.equations ++ [(5, 5)] ++ [] ++ [] := rfl
  rw [shape, List.append_nil, List.append_nil]
  refine (plain.models_append () _ _).mpr ⟨solved, ?_⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  exact rfl

theorem tensor_solved {C D : Configuration Nat Nat} (one : plain.Models () C.equations)
    (two : plain.Models () D.equations) :
    plain.Models () (AnnotatedRuns.tensor C D).equations :=
  (plain.models_append () _ _).mpr ⟨one, two⟩

theorem counts_valid_of_models (number : Nat) {C : Configuration Nat Nat}
    (solved : plain.Models () C.equations) (size : C.present.card = number) :
    (counts number).Valid plain five C := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ?_,
    ⟨(), counts_problem_solved number solved⟩, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Selection.commit, counts]
  · intro check member σ _
    have only : check = Check.count 5 number := List.mem_singleton.mp member
    subst only
    show (Check.matches plain σ five C.present 5).card = number
    rw [all_match]
    exact size
  · intro query member
    cases member

theorem card_of_counts_valid (number : Nat) {C : Configuration Nat Nat}
    (solved : plain.Models () C.equations) (valid : (counts number).Valid plain five C) :
    C.present.card = number := by
  have holds := valid.firing.checks (Check.count 5 number) (List.mem_singleton.mpr rfl) ()
    (counts_problem_solved number solved)
  have counted : (Check.matches plain () five C.present 5).card = number := holds
  rw [all_match] at counted
  exact counted

theorem adds_valid {C : Configuration Nat Nat} (solved : plain.Models () C.equations)
    (fresh : 7 ∉ C.present) : adds.Valid plain five C := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton 7, rfl, rfl, rfl, ?_,
    ⟨(), adds_problem_solved solved⟩, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Selection.commit, adds, fresh]
  · intro check member
    cases member
  · intro query member
    cases member

theorem removes_valid {C : Configuration Nat Nat} (solved : plain.Models () C.equations)
    (present : 7 ∈ C.present) : removes.Valid plain five C := by
  refine ⟨⟨List.nodup_singleton 7, List.nodup_nil, rfl, rfl, rfl, ?_,
    ⟨(), removes_problem_solved solved⟩, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Selection.commit, removes, present]
  · intro check member
    cases member
  · intro query member
    cases member

theorem seven_of_removes_valid {C : Configuration Nat Nat} (valid : removes.Valid plain five C) :
    7 ∈ C.present :=
  valid.firing.occurrences.taken_subset (List.mem_toFinset.mpr (List.mem_singleton.mpr rfl))

theorem zero_solved : plain.Models () zero.equations := fun _ member => by cases member

theorem empty_solved : plain.Models () empty.equations := fun _ member => by cases member

/-- The occurrence `0` beside nothing. -/
def joint : Configuration Nat Nat := AnnotatedRuns.tensor zero empty

theorem joint_solved : plain.Models () joint.equations := tensor_solved zero_solved empty_solved

/-! ### The two native runs -/

theorem adds_first : adds.Valid plain five joint := adds_valid joint_solved (by decide)

theorem removes_second : removes.Valid plain five (adds.result five joint) :=
  removes_valid (adds_problem_solved joint_solved) (by decide)

theorem counts_third : (counts 1).Valid plain five (removes.result five (adds.result five joint)) :=
  counts_valid_of_models 1 (removes_problem_solved (adds_problem_solved joint_solved)) (by decide)

theorem counts_first : (counts 1).Valid plain five joint :=
  counts_valid_of_models 1 joint_solved (by decide)

theorem adds_second : adds.Valid plain five ((counts 1).result five joint) :=
  adds_valid (counts_problem_solved 1 joint_solved) (by decide)

theorem removes_third :
    removes.Valid plain five (adds.result five ((counts 1).result five joint)) :=
  removes_valid (adds_problem_solved (counts_problem_solved 1 joint_solved)) (by decide)

/-- `adds`, `removes`, then `counts`. -/
def countsLast : (firstOrder plain five).toStep.Run joint :=
  .cons adds adds_first (.cons removes removes_second (.cons (counts 1) counts_third (.nil _)))

/-- `counts`, then `adds`, `removes`. -/
def countsFirst : (firstOrder plain five).toStep.Run joint :=
  .cons (counts 1) counts_first (.cons adds adds_second (.cons removes removes_third (.nil _)))

theorem removes_not_first : ¬ removes.Valid plain five joint :=
  fun valid => absurd (seven_of_removes_valid valid) (by decide)

theorem counts_not_between : ¬ (counts 1).Valid plain five (adds.result five joint) :=
  fun valid => absurd (card_of_counts_valid 1 (adds_problem_solved joint_solved) valid) (by decide)

/-- No admitted pair of the word `adds`, `removes`, `counts` can be swapped. -/
theorem no_swap_from_counts_last (later : List (Firing Nat Unit Nat)) :
    ¬ WordSwap plain five joint [adds, removes, counts 1] later := by
  intro swapped
  generalize shape : [adds, removes, counts 1] = word at swapped
  cases swapped with
  | swap before suffix f g independent =>
      match before, shape, independent with
      | [], shape, independent =>
          obtain ⟨rfl, rest⟩ := List.cons.inj shape
          obtain ⟨rfl, _⟩ := List.cons.inj rest
          exact removes_not_first
            ((AnnotatedRuns.firstOrder_independent_iff plain five).mp independent).2.1
      | [first], shape, independent =>
          obtain ⟨rfl, rest⟩ := List.cons.inj shape
          obtain ⟨rfl, rest'⟩ := List.cons.inj rest
          obtain ⟨rfl, _⟩ := List.cons.inj rest'
          exact counts_not_between
            ((AnnotatedRuns.firstOrder_independent_iff plain five).mp independent).2.1
      | first :: second :: more, shape, _ =>
          have lengths := congrArg List.length shape
          simp only [List.length_cons, List.length_append, List.length_nil] at lengths
          omega

theorem counts_ne_adds : counts 1 ≠ adds := by
  intro same
  have produce := congrArg (fun firing : Firing Nat Unit Nat => firing.rule.produce) same
  exact absurd produce (by decide)

/-- **A block exchange between two native runs that is not a trace equation.** -/
theorem not_one_trace :
    ¬ WordTrace plain five joint [adds, removes, counts 1] [counts 1, adds, removes] := by
  have invariant : ∀ first second : List (Firing Nat Unit Nat),
      WordTrace plain five joint first second →
        (first = [adds, removes, counts 1] ↔ second = [adds, removes, counts 1]) := by
    intro first second related
    induction related with
    | rel one two swapped =>
        constructor
        · intro same
          subst same
          exact absurd swapped (no_swap_from_counts_last two)
        · intro same
          subst same
          exact absurd (swapped.symm plain five) (no_swap_from_counts_last one)
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ left right => exact left.trans right
  intro related
  have same := (invariant _ _ related).mp rfl
  exact counts_ne_adds (List.cons.inj same).1

theorem counts_last_word : sites plain five countsLast = [adds, removes, counts 1] := rfl

theorem counts_first_word : sites plain five countsFirst = [counts 1, adds, removes] := rfl

/-- The two native runs are not trace equivalent. -/
theorem native_block_exchange_is_not_a_trace :
    ¬ (firstOrderTransport plain five).TraceEquiv joint countsLast countsFirst := by
  intro related
  have words := (native_trace_iff_word_trace plain five countsLast countsFirst).mp related
  rw [counts_last_word, counts_first_word] at words
  exact not_one_trace words

/-! ### The same two runs as a cut of tensors and a tensor of cuts -/

theorem counts_alone : (counts 1).Valid plain five zero :=
  counts_valid_of_models 1 zero_solved (by decide)

theorem adds_alone : adds.Valid plain five empty := adds_valid empty_solved (by decide)

theorem removes_alone : removes.Valid plain five (adds.result five empty) :=
  removes_valid (adds_problem_solved empty_solved) (by decide)

/-- The first side does nothing before the cut. -/
def idle : (firstOrder plain five).toStep.Run zero := .nil zero

/-- The second side adds and removes an occurrence. -/
def addsRemoves : (firstOrder plain five).toStep.Run empty :=
  .cons adds adds_alone (.cons removes removes_alone (.nil _))

/-- After the cut the first side counts. -/
def countsRun : (firstOrder plain five).toStep.Run idle.last := .cons (counts 1) counts_alone (.nil _)

/-- After the cut the second side does nothing. -/
def rests : (firstOrder plain five).toStep.Run addsRemoves.last := .nil _

/-- The first tensor: nothing beside `adds`, `removes`. -/
def beforePlan : (contextualRunInterpretation plain five).TensorPlan (contextualFlip plain five)
    PUnit.unit idle addsRemoves where
  leftPlan := .nil _
  rightPlan :=
    (.cons (I := contextualRunInterpretation plain five) (left := empty) (right := zero)
      (place := PUnit.unit) (by show Disjoint ([] : List Nat).toFinset ({0} : Finset Nat); decide)
      (adds_valid (tensor_solved empty_solved zero_solved) (by decide))
      (.cons (I := contextualRunInterpretation plain five) (left := adds.result five empty)
        (right := zero) (place := PUnit.unit)
        (by show Disjoint ([7] : List Nat).toFinset ({0} : Finset Nat); decide)
        (removes_valid (tensor_solved (adds_problem_solved empty_solved) zero_solved) (by decide))
        (.nil _)))

/-- The second tensor: `counts` beside nothing. -/
def afterPlan : (contextualRunInterpretation plain five).TensorPlan (contextualFlip plain five)
    (beforePlan.realize (contextualRunInterpretation plain five) (contextualFlip plain five)).target
    countsRun rests where
  leftPlan :=
    (.cons (I := contextualRunInterpretation plain five) (left := zero) (right := addsRemoves.last)
      (place := PUnit.unit)
      (by show Disjoint ([] : List Nat).toFinset addsRemoves.last.present; decide)
      (counts_valid_of_models 1
        (tensor_solved zero_solved (removes_problem_solved (adds_problem_solved empty_solved)))
        (by decide))
      (.nil _))
  rightPlan := .nil _

/-- The tensor of the two cuts: `counts` beside `adds`, `removes`. -/
def wholePlan : (contextualRunInterpretation plain five).TensorPlan (contextualFlip plain five)
    PUnit.unit (idle.append countsRun) (addsRemoves.append rests) where
  leftPlan :=
    (.cons (I := contextualRunInterpretation plain five) (left := zero) (right := empty)
      (place := PUnit.unit) (by show Disjoint ([] : List Nat).toFinset (∅ : Finset Nat); decide)
      counts_first (.nil _))
  rightPlan :=
    (.cons (I := contextualRunInterpretation plain five) (left := empty)
      (right := (counts 1).result five zero) (place := PUnit.unit)
      (by show Disjoint ([] : List Nat).toFinset ((counts 1).result five zero).present; decide)
      (adds_valid (tensor_solved empty_solved (counts_problem_solved 1 zero_solved)) (by decide))
      (.cons (I := contextualRunInterpretation plain five) (left := adds.result five empty)
        (right := (counts 1).result five zero) (place := PUnit.unit)
        (by show Disjoint ([7] : List Nat).toFinset ((counts 1).result five zero).present; decide)
        (removes_valid
          (tensor_solved (adds_problem_solved empty_solved) (counts_problem_solved 1 zero_solved))
          (by decide))
        (.nil _)))

/-- **The interchange law fails for counting, with all three tensors present.** -/
theorem interchange_fails_for_counting :
    ¬ InterchangeAt (contextualRunInterpretation plain five) (contextualFlip plain five)
      beforePlan afterPlan wholePlan := by
  intro law
  have words := (native_trace_iff_word_trace plain five _ _).mp law
  have cut : sites plain five (cutOfTensors (contextualRunInterpretation plain five)
      (contextualFlip plain five) beforePlan afterPlan) = [adds, removes, counts 1] :=
    sites_sequentialTensor plain five beforePlan afterPlan
  have tensor : sites plain five (wholePlan.realize (contextualRunInterpretation plain five)
      (contextualFlip plain five)).execution = [counts 1, adds, removes] :=
    tensor_sites plain five wholePlan
  rw [cut, tensor] at words
  exact not_one_trace words

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls
