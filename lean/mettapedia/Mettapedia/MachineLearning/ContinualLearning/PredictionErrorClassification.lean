import Mathlib

/-!
# Prediction-error classification and its no-forgetting boundary

Zając, Tuytelaars, and van de Ven, *Prediction Error-based Classification
for Class-Incremental Learning* (ICLR 2024, arXiv:2305.18806), Algorithms 1
and 2 train one student per class against a shared frozen teacher and select
the class with the smallest student--teacher prediction error.

This file isolates the exact support argument behind the source's
no-forgetting discussion:

* updating one class-specific student leaves every other class score
  unchanged;
* disjoint class updates commute;
* consequently, the prediction-error ordering within an untouched finite
  class set is invariant;
* nevertheless, a newly added class can become the global winner without
  changing any old score, so parameter isolation alone does not prove
  class-incremental accuracy retention;
* freezing the shared teacher is load bearing.

The results concern exact modular function updates.  They do not establish
the source's Gaussian-process approximation, empirical accuracy, or
generalization from class training data to unseen inputs.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace PredictionErrorClassification

noncomputable section

variable {Class Input Output : Type*}

section Score

variable [NormedAddCommGroup Output]

/-- Algorithm 2's class score: distance between a class-specific student and
the shared teacher at the queried input. -/
def predictionError
    (teacher : Input → Output)
    (students : Class → Input → Output)
    (label : Class)
    (input : Input) : ℝ :=
  ‖students label input - teacher input‖

/-- One class-specific function update, modeling an isolated student
training result while every other student remains fixed. -/
def updateStudent [DecidableEq Class]
    (students : Class → Input → Output)
    (target : Class)
    (replacement : Input → Output) :
    Class → Input → Output :=
  Function.update students target replacement

/-- A class outside the updated module has exactly the same score. -/
theorem predictionError_updateStudent_of_ne
    [DecidableEq Class]
    (teacher : Input → Output)
    (students : Class → Input → Output)
    {target label : Class}
    (replacement : Input → Output)
    (label_ne_target : label ≠ target)
    (input : Input) :
    predictionError teacher
        (updateStudent students target replacement) label input =
      predictionError teacher students label input := by
  simp [predictionError, updateStudent, label_ne_target]

omit [NormedAddCommGroup Output] in
/-- Updates to two distinct class modules commute exactly. -/
theorem updateStudent_comm
    [DecidableEq Class]
    (students : Class → Input → Output)
    {left right : Class}
    (distinct : left ≠ right)
    (leftReplacement rightReplacement : Input → Output) :
    updateStudent
        (updateStudent students left leftReplacement)
        right rightReplacement =
      updateStudent
        (updateStudent students right rightReplacement)
        left leftReplacement := by
  funext label input
  by_cases label_eq_left : label = left
  · subst label
    simp [updateStudent, distinct]
  · by_cases label_eq_right : label = right
    · subst label
      simp [updateStudent, distinct.symm]
    · simp [updateStudent, label_eq_left, label_eq_right]

/-- `winner` minimizes prediction error on the declared finite candidate
set.  Ties are intentionally allowed. -/
def IsPredictionErrorMinimizer
    (teacher : Input → Output)
    (students : Class → Input → Output)
    (candidates : Finset Class)
    (input : Input)
    (winner : Class) : Prop :=
  winner ∈ candidates ∧
    ∀ candidate ∈ candidates,
      predictionError teacher students winner input ≤
        predictionError teacher students candidate input

/-- Agreement of two student families on a candidate set preserves its
complete minimizer relation. -/
theorem isPredictionErrorMinimizer_congr_on
    [DecidableEq Class]
    (teacher : Input → Output)
    (students₁ students₂ : Class → Input → Output)
    (candidates : Finset Class)
    (input : Input)
    (agreement :
      ∀ label ∈ candidates, students₁ label = students₂ label) :
    ∀ winner,
      IsPredictionErrorMinimizer
          teacher students₁ candidates input winner ↔
        IsPredictionErrorMinimizer
          teacher students₂ candidates input winner := by
  intro winner
  constructor
  · rintro ⟨winner_mem, winner_minimal⟩
    refine ⟨winner_mem, ?_⟩
    intro candidate candidate_mem
    simpa [predictionError, agreement winner winner_mem,
      agreement candidate candidate_mem] using
      winner_minimal candidate candidate_mem
  · rintro ⟨winner_mem, winner_minimal⟩
    refine ⟨winner_mem, ?_⟩
    intro candidate candidate_mem
    simpa [predictionError, agreement winner winner_mem,
      agreement candidate candidate_mem] using
      winner_minimal candidate candidate_mem

/-- Updating a class outside the candidate set preserves every minimizer
within that set.  This is the exact finite no-interference theorem. -/
theorem isPredictionErrorMinimizer_update_outside_iff
    [DecidableEq Class]
    (teacher : Input → Output)
    (students : Class → Input → Output)
    {target : Class}
    (replacement : Input → Output)
    (candidates : Finset Class)
    (target_outside : target ∉ candidates)
    (input : Input)
    (winner : Class) :
    IsPredictionErrorMinimizer teacher
        (updateStudent students target replacement)
        candidates input winner ↔
      IsPredictionErrorMinimizer teacher students
        candidates input winner := by
  apply isPredictionErrorMinimizer_congr_on
  intro label label_mem
  have label_ne_target : label ≠ target := by
    intro equality
    exact target_outside (equality ▸ label_mem)
  simp [updateStudent, label_ne_target]

/-- Strict pairwise preference induced by the prediction-error score. -/
def StrictlyPreferred
    (teacher : Input → Output)
    (students : Class → Input → Output)
    (input : Input)
    (preferred other : Class) : Prop :=
  predictionError teacher students preferred input <
    predictionError teacher students other input

end Score

/-! ## Executable boundaries -/

def twoClassTeacher (_ : Unit) : ℝ := 0

def twoClassStudents : Bool → Unit → ℝ
  | false, _ => 1
  | true, _ => 3

def perfectStudent (_ : Unit) : ℝ := 0

/-- Positive fixture: replacing the `true` student leaves the old `false`
score bit-for-bit unchanged. -/
theorem twoClass_old_score_is_preserved :
    predictionError twoClassTeacher
        (updateStudent twoClassStudents true perfectStudent)
        false () =
      predictionError twoClassTeacher twoClassStudents false () := by
  norm_num [predictionError, updateStudent, twoClassTeacher,
    twoClassStudents, perfectStudent]

/-- Negative boundary: the new class can reverse the global preference even
though the old class score is unchanged.  Modular parameter isolation is
therefore weaker than retention of class-incremental predictions. -/
theorem twoClass_new_student_reverses_global_preference :
    StrictlyPreferred twoClassTeacher twoClassStudents ()
        false true ∧
      StrictlyPreferred twoClassTeacher
        (updateStudent twoClassStudents true perfectStudent) ()
        true false ∧
      predictionError twoClassTeacher
          (updateStudent twoClassStudents true perfectStudent)
          false () =
        predictionError twoClassTeacher twoClassStudents false () := by
  norm_num [StrictlyPreferred, predictionError, updateStudent,
    twoClassTeacher, twoClassStudents, perfectStudent]

def shiftedTeacher (_ : Unit) : ℝ := 1

/-- Negative boundary: changing the shared teacher changes an old score even
when every class-specific student is fixed. -/
theorem frozen_teacher_is_load_bearing :
    predictionError twoClassTeacher twoClassStudents false () = 1 ∧
      predictionError shiftedTeacher twoClassStudents false () = 0 := by
  norm_num [predictionError, twoClassTeacher, shiftedTeacher,
    twoClassStudents]

#print axioms predictionError_updateStudent_of_ne
#print axioms updateStudent_comm
#print axioms isPredictionErrorMinimizer_congr_on
#print axioms isPredictionErrorMinimizer_update_outside_iff
#print axioms twoClass_old_score_is_preserved
#print axioms twoClass_new_student_reverses_global_preference
#print axioms frozen_teacher_is_load_bearing

end

end PredictionErrorClassification

end Mettapedia.MachineLearning.ContinualLearning
