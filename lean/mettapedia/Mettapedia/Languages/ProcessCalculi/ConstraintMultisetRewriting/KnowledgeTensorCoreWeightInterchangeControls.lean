import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreTraceControls

/-!
# Control: the interchange law fails for absence too

`interchange_fails_for_counting` exchanges a counting firing with a block that adds and then
removes a counted occurrence. The same exchange with an **absence** check fails in the same way,
with all three tensors present (`interchange_fails_for_absence`): on one side a firing checks that
no occurrence labelled `5` is present; on the other side `adds` makes one and `removes` takes it.
The cut of the two tensors runs `adds`, `removes`, `unlessFive`; the tensor of the two cuts runs
`unlessFive`, `adds`, `removes`. Both are native runs, and they are not one trace: between `adds`
and `removes` the absence fails.

So the failure of the interchange law is not a feature of counting. Absence grades are positively
correlated in every random surrounding (`cut_harris`), and the interchange law still fails for
them; separation, not the shape of the grade, is what restores it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.AbsenceInterchange

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrder
open KnowledgeTensorFirstOrderControls (plain)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls

/-- Takes, reads and makes nothing, and checks that no occurrence labelled `5` is present. -/
def unlessFive : Firing Nat Unit Nat := ⟨⟨[], [], [], [Check.absent 5], []⟩, [], ⟨[], [], []⟩⟩

theorem unlessFive_problem_solved {C : Configuration Nat Nat}
    (solved : plain.Models () C.equations) :
    plain.Models () (unlessFive.selection.problem five unlessFive.rule C) := by
  have shape : unlessFive.selection.problem five unlessFive.rule C = C.equations ++ [] ++ [] ++ [] :=
    rfl
  rw [shape, List.append_nil, List.append_nil, List.append_nil]
  exact solved

/-- `unlessFive` is admitted where nothing is present. -/
theorem unlessFive_valid {C : Configuration Nat Nat} (solved : plain.Models () C.equations)
    (bare : C.present = ∅) : unlessFive.Valid plain five C := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ?_,
    ⟨(), unlessFive_problem_solved solved⟩, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Selection.commit, unlessFive]
  · intro check member σ _
    have only : check = Check.absent 5 := List.mem_singleton.mp member
    subst only
    intro o inside
    rw [bare] at inside
    exact absurd inside (Finset.notMem_empty o)
  · intro query member
    cases member

/-- Where `unlessFive` is admitted, nothing is present: every occurrence is labelled `5`. -/
theorem present_empty_of_unlessFive {C : Configuration Nat Nat}
    (solved : plain.Models () C.equations) (valid : unlessFive.Valid plain five C) :
    C.present = ∅ := by
  have holds := valid.firing.checks (Check.absent 5) (List.mem_singleton.mpr rfl) ()
    (unlessFive_problem_solved solved)
  exact Finset.eq_empty_of_forall_notMem fun o inside => holds o inside rfl

/-- Both sides start from nothing. -/
def bare : Configuration Nat Nat := AnnotatedRuns.tensor empty empty

theorem bare_solved : plain.Models () bare.equations := tensor_solved empty_solved empty_solved

/-! ## The runs and the three tensors -/

/-- The first side does nothing before the cut. -/
def idleSide : (firstOrder plain five).toStep.Run empty := .nil empty

theorem unlessFive_alone : unlessFive.Valid plain five empty := unlessFive_valid empty_solved rfl

/-- After the cut the first side checks absence. -/
def unlessRun : (firstOrder plain five).toStep.Run idleSide.last :=
  .cons unlessFive unlessFive_alone (.nil _)

/-- The first tensor: nothing beside `adds`, `removes`. -/
def beforeAbsent : (contextualRunInterpretation plain five).TensorPlan (contextualFlip plain five)
    PUnit.unit idleSide addsRemoves where
  leftPlan := .nil _
  rightPlan :=
    (.cons (I := contextualRunInterpretation plain five) (left := empty) (right := empty)
      (place := PUnit.unit) (by show Disjoint ([] : List Nat).toFinset (∅ : Finset Nat); decide)
      (adds_valid (tensor_solved empty_solved empty_solved) (by decide))
      (.cons (I := contextualRunInterpretation plain five) (left := adds.result five empty)
        (right := empty) (place := PUnit.unit)
        (by show Disjoint ([7] : List Nat).toFinset (∅ : Finset Nat); decide)
        (removes_valid (tensor_solved (adds_problem_solved empty_solved) empty_solved) (by decide))
        (.nil _)))

/-- The second tensor: `unlessFive` beside nothing. -/
def afterAbsent : (contextualRunInterpretation plain five).TensorPlan (contextualFlip plain five)
    (beforeAbsent.realize (contextualRunInterpretation plain five) (contextualFlip plain five)).target
    unlessRun rests where
  leftPlan :=
    (.cons (I := contextualRunInterpretation plain five) (left := empty) (right := addsRemoves.last)
      (place := PUnit.unit)
      (by show Disjoint ([] : List Nat).toFinset addsRemoves.last.present; decide)
      (unlessFive_valid
        (tensor_solved empty_solved (removes_problem_solved (adds_problem_solved empty_solved)))
        (by decide))
      (.nil _))
  rightPlan := .nil _

/-- The tensor of the two cuts: `unlessFive` beside `adds`, `removes`. -/
def wholeAbsent : (contextualRunInterpretation plain five).TensorPlan (contextualFlip plain five)
    PUnit.unit (idleSide.append unlessRun) (addsRemoves.append rests) where
  leftPlan :=
    (.cons (I := contextualRunInterpretation plain five) (left := empty) (right := empty)
      (place := PUnit.unit) (by show Disjoint ([] : List Nat).toFinset (∅ : Finset Nat); decide)
      (unlessFive_valid (tensor_solved empty_solved empty_solved) (by decide)) (.nil _))
  rightPlan :=
    (.cons (I := contextualRunInterpretation plain five) (left := empty)
      (right := unlessFive.result five empty) (place := PUnit.unit)
      (by show Disjoint ([] : List Nat).toFinset (unlessFive.result five empty).present; decide)
      (adds_valid (tensor_solved empty_solved (unlessFive_problem_solved empty_solved)) (by decide))
      (.cons (I := contextualRunInterpretation plain five) (left := adds.result five empty)
        (right := unlessFive.result five empty) (place := PUnit.unit)
        (by show Disjoint ([7] : List Nat).toFinset (unlessFive.result five empty).present; decide)
        (removes_valid
          (tensor_solved (adds_problem_solved empty_solved) (unlessFive_problem_solved empty_solved))
          (by decide))
        (.nil _)))

/-! ## The two sides are not one trace -/

theorem removes_not_first_bare : ¬ removes.Valid plain five bare :=
  fun valid => absurd (seven_of_removes_valid valid) (by decide)

theorem unlessFive_not_between : ¬ unlessFive.Valid plain five (adds.result five bare) :=
  fun valid => absurd (present_empty_of_unlessFive (adds_problem_solved bare_solved) valid)
    (by decide)

/-- No admitted pair of the word `adds`, `removes`, `unlessFive` can be swapped. -/
theorem no_swap_from_absence_last (later : List (Firing Nat Unit Nat)) :
    ¬ WordSwap plain five bare [adds, removes, unlessFive] later := by
  intro swapped
  generalize shape : [adds, removes, unlessFive] = word at swapped
  cases swapped with
  | swap before suffix f g independent =>
      match before, shape, independent with
      | [], shape, independent =>
          obtain ⟨rfl, rest⟩ := List.cons.inj shape
          obtain ⟨rfl, _⟩ := List.cons.inj rest
          exact removes_not_first_bare
            ((AnnotatedRuns.firstOrder_independent_iff plain five).mp independent).2.1
      | [first], shape, independent =>
          obtain ⟨rfl, rest⟩ := List.cons.inj shape
          obtain ⟨rfl, rest'⟩ := List.cons.inj rest
          obtain ⟨rfl, _⟩ := List.cons.inj rest'
          exact unlessFive_not_between
            ((AnnotatedRuns.firstOrder_independent_iff plain five).mp independent).2.1
      | first :: second :: more, shape, _ =>
          have lengths := congrArg List.length shape
          simp only [List.length_cons, List.length_append, List.length_nil] at lengths
          omega

theorem unlessFive_ne_adds : unlessFive ≠ adds := by
  intro same
  have produce := congrArg (fun firing : Firing Nat Unit Nat => firing.rule.produce) same
  exact absurd produce (by decide)

/-- **A block exchange around an absence check that is not a trace equation.** -/
theorem not_one_trace_for_absence :
    ¬ WordTrace plain five bare [adds, removes, unlessFive] [unlessFive, adds, removes] := by
  have invariant : ∀ first second : List (Firing Nat Unit Nat),
      WordTrace plain five bare first second →
        (first = [adds, removes, unlessFive] ↔ second = [adds, removes, unlessFive]) := by
    intro first second related
    induction related with
    | rel one two swapped =>
        constructor
        · intro same
          subst same
          exact absurd swapped (no_swap_from_absence_last two)
        · intro same
          subst same
          exact absurd (swapped.symm plain five) (no_swap_from_absence_last one)
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ left right => exact left.trans right
  intro related
  have same := (invariant _ _ related).mp rfl
  exact unlessFive_ne_adds (List.cons.inj same).1

/-- **The interchange law fails for absence, with all three tensors present.** -/
theorem interchange_fails_for_absence :
    ¬ InterchangeAt (contextualRunInterpretation plain five) (contextualFlip plain five)
      beforeAbsent afterAbsent wholeAbsent := by
  intro law
  have words := (native_trace_iff_word_trace plain five _ _).mp law
  have cut : sites plain five (cutOfTensors (contextualRunInterpretation plain five)
      (contextualFlip plain five) beforeAbsent afterAbsent) = [adds, removes, unlessFive] :=
    sites_sequentialTensor plain five beforeAbsent afterAbsent
  have tensor : sites plain five (wholeAbsent.realize (contextualRunInterpretation plain five)
      (contextualFlip plain five)).execution = [unlessFive, adds, removes] :=
    tensor_sites plain five wholeAbsent
  rw [cut, tensor] at words
  exact not_one_trace_for_absence words

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.AbsenceInterchange
