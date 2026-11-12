import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderContextRuns

/-!
# Two source-local runs may share a read occurrence

Both components read physical occurrence one. The shared implementation
executes both events and retains one physical occurrence. The older disjoint
space criterion excludes this example, so it is strictly stronger here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns.SharedReadsControls

open Mettapedia.Logic.LP
open AnnotatedRuns (Firing firstOrder)
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label zeros onlyReads)
open AnnotatedRuns.TensorControls (readerSide)

theorem information_models {state : Configuration (Term signature) Nat}
    (base : A.Models zeros state.equations) :
    A.Models zeros (onlyReads.selection.problem label onlyReads.rule state) := by
  intro equation member
  have origin : equation ∈ state.equations ∨ equation = (.var 1, label 1) := by
    simpa [Selection.problem, Selection.equations, onlyReads] using member
  rcases origin with original | rfl
  · exact base equation original
  · rfl

theorem valid {state : Configuration (Term signature) Nat}
    (base : A.Models zeros state.equations) (present : 1 ∈ state.present) : onlyReads.Valid A label state := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, ?_, ⟨zeros, information_models base⟩,
    by simp [onlyReads]⟩, by simp [onlyReads]⟩
  refine ⟨by simp [Selection.commit, onlyReads], ?_, by simp [Selection.commit, onlyReads],
    by simp [Selection.commit, onlyReads], by simp [Selection.commit]⟩
  simpa [Selection.commit, onlyReads] using present

theorem source_allowed : onlyReads.Valid A label readerSide := valid (by simp [readerSide]) (by decide)

def run : (firstOrder A label).toStep.Run readerSide := .cons onlyReads source_allowed (.nil _)

abbrev I := contextualRunInterpretation A label
abbrev flip := contextualFlip A label

theorem first_allowed : onlyReads.Valid A label (AnnotatedRuns.tensor readerSide readerSide) :=
  valid (by simp [AnnotatedRuns.tensor, readerSide]) (by decide)

def leftPlan : I.Plan (right := readerSide) PUnit.unit run :=
  .cons (I := I) (left := readerSide) (right := readerSide) (place := PUnit.unit)
    (by decide) first_allowed (.nil _)

theorem second_allowed : onlyReads.Valid A label (AnnotatedRuns.tensor readerSide run.last) := by
  apply valid
  · change A.Models zeros ([] ++ (onlyReads.result label readerSide).equations)
    exact information_models (by simp [readerSide])
  · change 1 ∈ readerSide.present ∪ run.last.present
    exact Finset.mem_union_left _ (by decide)

def rightPlan : I.Plan (right := run.last) (flip.swap (leftPlan.realize I PUnit.unit run).target) run :=
  .cons (I := I) (left := readerSide) (right := run.last) (place := PUnit.unit)
    (by decide) second_allowed (.nil _)

def plan : I.TensorPlan flip PUnit.unit run run := ⟨leftPlan, rightPlan⟩
def result : I.TensorResult PUnit.unit run run := plan.realize I flip

theorem both_event_occurrences_retained : sites A label result.execution = [onlyReads, onlyReads] :=
  tensor_sites A label plan

theorem one_physical_read_occurrence : result.execution.last.present = {1} := by
  calc
    result.execution.last.present = (AnnotatedRuns.tensor run.last run.last).present := result.resultIso.down.2
    _ = {1} := by decide

theorem disjoint_space_condition_unnecessary :
    Nonempty (I.TensorPlan flip PUnit.unit run run) ∧
      ¬Disjoint (AnnotatedRuns.space readerSide (sites A label run))
        (AnnotatedRuns.space readerSide (sites A label run)) := ⟨⟨plan⟩, by decide⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns.SharedReadsControls
