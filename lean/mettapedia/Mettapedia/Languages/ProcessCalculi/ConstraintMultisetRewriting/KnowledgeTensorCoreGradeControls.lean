import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreControls

/-!
# Control: the grade is a property of the run, not of its trace

Terms have one variable. The firing `pins` tells that the variable is `5`. The firing `asks`
checks the absence of `9`. Where no occurrence is present the two are admitted in both orders, so
the two local runs are one trace (`the_two_orders_are_one_trace`).

Beside a context that holds one occurrence labelled by the variable:

* `pins` then `asks` is in the grade (`tell_first_is_in_the_grade`): after the tell every
  solution reads the occurrence as `5`;
* `asks` then `pins` is not (`ask_first_is_not_in_the_grade`): before the tell some solution
  reads it as `9`.

So the frame rule does not descend to traces (`the_grade_is_not_a_property_of_traces`). It does
respect a swap wherever both orders are in the grade (`FirstOrder.framed_swap_one_trace`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.GradeControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open FirstOrderNativeRuns

/-- Terms with one variable: `none` is the variable and `some n` the constant `n`. A
substitution is `none`, which leaves the variable, or `some n`, which replaces it by `n`. -/
def oneVariable : SubstitutionAction (Option Nat) (Option Nat) where
  E := Eq
  equivalence := eq_equivalence
  apply := fun σ term => match term with
    | some n => some n
    | none => σ
  identity := none
  compose := fun outer inner => match inner with
    | some n => some n
    | none => outer
  apply_identity := fun term => by cases term <;> rfl
  apply_compose := fun outer inner term => by cases term <;> cases inner <;> rfl
  preserves := fun _ _ _ same => by rw [same]

/-- Every occurrence is labelled by the variable. -/
def unknown (_ : Nat) : Option Nat := none

/-- Tells that the variable is `5`. -/
def pins : Firing (Option Nat) (Option Nat) Nat :=
  ⟨⟨[], [], [(none, some 5)], [], []⟩, [], ⟨[], [], []⟩⟩

/-- Checks the absence of `9`. -/
def asks : Firing (Option Nat) (Option Nat) Nat :=
  ⟨⟨[], [], [], [Check.absent (some 9)], []⟩, [], ⟨[], [], []⟩⟩

theorem pins_valid {C : Configuration (Option Nat) Nat}
    (solved : oneVariable.Models (some 5) C.equations) : pins.Valid oneVariable unknown C := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ?_, ⟨some 5, ?_⟩, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Selection.commit, pins]
  · have shape : pins.selection.problem unknown pins.rule C =
        C.equations ++ [] ++ [] ++ [(none, some 5)] := rfl
    rw [shape, List.append_nil, List.append_nil]
    refine (oneVariable.models_append (some 5) _ _).mpr ⟨solved, ?_⟩
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    exact rfl
  · intro check member
    cases member
  · intro query member
    cases member

theorem asks_problem (C : Configuration (Option Nat) Nat) :
    asks.selection.problem unknown asks.rule C = C.equations := by
  have shape : asks.selection.problem unknown asks.rule C = C.equations ++ [] ++ [] ++ [] := rfl
  rw [shape, List.append_nil, List.append_nil, List.append_nil]

/-- Where the store pins the variable, the absence of `9` holds whatever is present. -/
theorem asks_valid_of_pinned {C : Configuration (Option Nat) Nat}
    (pinned : ((none : Option Nat), some 5) ∈ C.equations)
    (solved : oneVariable.Models (some 5) C.equations) : asks.Valid oneVariable unknown C := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ?_, ⟨some 5, ?_⟩, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Selection.commit, asks]
  · rw [asks_problem]
    exact solved
  · intro check member σ models
    have only : check = Check.absent (some 9) := List.mem_singleton.mp member
    subst only
    rw [asks_problem] at models
    have fixed : σ = some 5 := models _ pinned
    intro occurrence _ same
    have read : (some 9 : Option Nat) = σ := same
    exact absurd (read.trans fixed) (by decide)
  · intro query member
    cases member

/-- Where nothing is present, the absence of `9` holds. -/
theorem asks_valid_of_empty {equations : EquationStore (Option Nat)}
    (consistent : oneVariable.Consistent equations) :
    asks.Valid oneVariable unknown ⟨equations, ∅⟩ := by
  obtain ⟨σ, solved⟩ := consistent
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ?_, ⟨σ, ?_⟩, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Selection.commit, asks]
  · rw [asks_problem]
    exact solved
  · intro check member τ _
    have only : check = Check.absent (some 9) := List.mem_singleton.mp member
    subst only
    intro occurrence present
    exact absurd present (Finset.notMem_empty occurrence)
  · intro query member
    cases member

/-- No knowledge and no occurrence. -/
def hollow : Configuration (Option Nat) Nat := ⟨[], ∅⟩

/-- One occurrence, labelled by the variable. -/
def holdsVariable : Configuration (Option Nat) Nat := ⟨[], {20}⟩

theorem pins_first : pins.Valid oneVariable unknown hollow :=
  pins_valid (fun _ member => by cases member)

theorem pinned_after_pins (C : Configuration (Option Nat) Nat)
    (solved : oneVariable.Models (some 5) C.equations) :
    ((none : Option Nat), some 5) ∈ (pins.result unknown C).equations ∧
      oneVariable.Models (some 5) (pins.result unknown C).equations := by
  have shape : (pins.result unknown C).equations = C.equations ++ [] ++ [] ++ [(none, some 5)] :=
    rfl
  rw [shape, List.append_nil, List.append_nil]
  refine ⟨List.mem_append_right _ (List.mem_singleton.mpr rfl),
    (oneVariable.models_append (some 5) _ _).mpr ⟨solved, ?_⟩⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  exact rfl

theorem asks_second : asks.Valid oneVariable unknown (pins.result unknown hollow) :=
  asks_valid_of_pinned (pinned_after_pins hollow (fun _ member => by cases member)).1
    (pinned_after_pins hollow (fun _ member => by cases member)).2

theorem asks_first : asks.Valid oneVariable unknown hollow :=
  asks_valid_of_empty ⟨none, fun _ member => by cases member⟩

theorem pins_second : pins.Valid oneVariable unknown (asks.result unknown hollow) := by
  apply pins_valid
  have shape : (asks.result unknown hollow).equations = [] := rfl
  rw [shape]
  intro equation member
  cases member

/-- `pins`, then `asks`. -/
def tellFirst : (firstOrder oneVariable unknown).toStep.Run hollow :=
  .cons pins pins_first (.cons asks asks_second (.nil _))

/-- `asks`, then `pins`. -/
def askFirst : (firstOrder oneVariable unknown).toStep.Run hollow :=
  .cons asks asks_first (.cons pins pins_second (.nil _))

theorem the_two_orders_are_one_trace :
    (firstOrderTransport oneVariable unknown).TraceEquiv hollow tellFirst askFirst :=
  FirstOrder.native_transposition oneVariable unknown tellFirst askFirst [] [] pins asks rfl rfl

theorem joint_solved :
    oneVariable.Models (some 5) (AnnotatedRuns.tensor hollow holdsVariable).equations :=
  fun _ member => by cases member

theorem pins_beside : pins.Valid oneVariable unknown (AnnotatedRuns.tensor hollow holdsVariable) :=
  pins_valid joint_solved

theorem asks_after_pins_beside :
    asks.Valid oneVariable unknown
      (AnnotatedRuns.tensor (pins.result unknown hollow) holdsVariable) := by
  have alone := pinned_after_pins hollow (fun _ member => by cases member)
  refine asks_valid_of_pinned (List.mem_append_left _ alone.1) ?_
  exact (oneVariable.models_append (some 5) _ _).mpr ⟨alone.2, fun _ member => by cases member⟩

theorem asks_refused_beside :
    ¬ asks.Valid oneVariable unknown (AnnotatedRuns.tensor hollow holdsVariable) := by
  intro valid
  have solved : oneVariable.Models (some 9)
      (asks.selection.problem unknown asks.rule (AnnotatedRuns.tensor hollow holdsVariable)) := by
    rw [asks_problem]
    intro equation member
    cases member
  have holds := valid.firing.checks (Check.absent (some 9)) (List.mem_singleton.mpr rfl) (some 9)
    solved
  exact holds 20 (by decide) rfl

theorem framed : Disjoint ([] : List Nat).toFinset ({20} : Finset Nat) := by decide

theorem tell_first_is_in_the_grade :
    (contextualRunInterpretation oneVariable unknown).Checks (left := hollow)
      (right := holdsVariable) PUnit.unit tellFirst :=
  ⟨⟨framed, (valid_tensor_iff oneVariable unknown pins pins_first).mp pins_beside⟩,
    ⟨framed, (valid_tensor_iff oneVariable unknown asks asks_second).mp asks_after_pins_beside⟩,
    trivial⟩

theorem ask_first_is_not_in_the_grade :
    ¬ (contextualRunInterpretation oneVariable unknown).Checks (left := hollow)
      (right := holdsVariable) PUnit.unit askFirst :=
  fun checked => asks_refused_beside
    ((valid_tensor_iff oneVariable unknown asks asks_first).mpr checked.1.2)

/-- **The grade is a property of the run, not of its trace.** -/
theorem the_grade_is_not_a_property_of_traces :
    (firstOrderTransport oneVariable unknown).TraceEquiv hollow tellFirst askFirst ∧
      (contextualRunInterpretation oneVariable unknown).Checks (left := hollow)
        (right := holdsVariable) PUnit.unit tellFirst ∧
      ¬ (contextualRunInterpretation oneVariable unknown).Checks (left := hollow)
        (right := holdsVariable) PUnit.unit askFirst :=
  ⟨the_two_orders_are_one_trace, tell_first_is_in_the_grade, ask_first_is_not_in_the_grade⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.GradeControls

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls

open FirstOrderNativeRuns
open KnowledgeTensorFirstOrderControls (plain one)

/-- Every firing of the run that reads is stable where it is placed. -/
theorem reads_run_is_stable_along :
    StableAlong (contextualRunInterpretation plain id) (left := one) (right := nine) PUnit.unit
      readsRun :=
  ⟨reads_is_stable one nine, trivial⟩

/-- The run that checks absence is not stable along its placement beside the occurrence `9`. -/
theorem absence_run_is_not_stable_along :
    ¬ StableAlong (contextualRunInterpretation plain id) (left := one) (right := nine) PUnit.unit
      unlessNineRun :=
  fun stable => absence_is_not_stable stable.1

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls
