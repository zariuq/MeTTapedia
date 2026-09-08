import Mettapedia.Cybernetics.DistinctionCalculus.Finite
import Mettapedia.Cybernetics.DistinctionCalculus.Weighted

/-!
# Controls for authored distinction versus derived completion

The three-node chain has adjacent indistinguishability and distinct endpoints.
Its least metric completion merges those endpoints. A graded chain instead
derives similarity 3/5 from two similarities 4/5: merging its endpoints is
refuted for every certificate, not merely rejected for one bad proof.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus.Examples

def chain : Tolerance (Fin 3) where
  similarity x y := if (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) then 0 else 1
  nonnegative x y := by split_ifs <;> norm_num
  bounded x y := by split_ifs <;> norm_num
  reflexive x := by fin_cases x <;> decide
  symmetric x y := by fin_cases x <;> fin_cases y <;> norm_num

@[simp] theorem chain_similarity (x y : Fin 3) :
    chain.similarity x y = if (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) then 0 else 1 := rfl

def collapsed : Tolerance (Fin 3) := Tolerance.ofReport (fun _ => false)

def throughMiddle (x y : Fin 3) : Certificate (Fin 3) :=
  .triangle (.edge x 1) (.edge 1 y)

theorem chain_completion_checked : completionCheck chain collapsed throughMiddle = true := by
  simp only [completionCheck, decide_eq_true_eq]
  refine ⟨?_, Tolerance.ofReport_metric _, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [collapsed, Tolerance.ofReport, Fin.ext_iff]
  · intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [check, throughMiddle, infer, collapsed, Tolerance.ofReport,
        Tolerance.distance, Fin.ext_iff]

theorem chain_completion_is_least : LeastMetricExtension chain collapsed :=
  completionCheck_sound chain_completion_checked

theorem raw_chain_completion_checked :
    checkRawCompletion chain.similarity collapsed.similarity throughMiddle = true := by
  simpa only [checkRawCompletion, admit_tolerance] using chain_completion_checked

theorem chain_endpoints_apart : chain.Apart 0 2 := by
  norm_num [Tolerance.Apart, Tolerance.distance, Fin.ext_iff]

theorem chain_apart_not_cotransitive :
    ¬ (chain.Apart 0 1 ∨ chain.Apart 1 2) := by
  norm_num [Tolerance.Apart, Tolerance.distance, Fin.ext_iff]

theorem chain_not_metric : ¬ chain.Metric := by
  intro metric
  have bound := metric 0 1 2
  norm_num [Tolerance.distance, Fin.ext_iff] at bound

/-- Every coherent extension identifies the endpoints, but the seed does not. -/
theorem every_metric_extension_merges_endpoints (model : Tolerance (Fin 3))
    (hExt : chain.Extends model) (metric : model.Metric) : model.Indistinguishable 0 2 := by
  have bound := chain_completion_is_least.2.2 model hExt metric 0 2
  rw [model.indistinguishable_iff_similarity_one]
  exact le_antisymm (model.bounded 0 2) (by simpa [collapsed, Tolerance.ofReport] using bound)

theorem completion_does_not_establish_seed_equality :
    check chain ⟨0, 2, 0⟩ (throughMiddle 0 2) = true ∧
      ¬ chain.Indistinguishable 0 2 := by
  constructor
  · norm_num [check, infer, throughMiddle, Tolerance.distance, Fin.ext_iff]
  · norm_num [Tolerance.Indistinguishable, Tolerance.distance, Fin.ext_iff]

theorem wrong_junction_rejected :
    infer chain (.triangle (.edge 0 1) (.edge 2 0)) = none := by decide

theorem strengthened_bound_rejected :
    check chain ⟨0, 2, 0⟩ (.weaken 0 (.edge 0 2)) = false := by
  norm_num [check, infer, Tolerance.distance, Fin.ext_iff]
  intro equal
  cases equal

theorem wrong_requested_endpoints_rejected :
    check chain ⟨0, 2, 0⟩ (.refl 0) = false := by decide

theorem invalid_matrix_rejected : admit (fun (_ _ : Fin 2) => (2 : ℚ)) = none := by decide

def graded : Tolerance (Fin 3) where
  similarity x y := if x = y then 1 else if x = 1 ∨ y = 1 then 4 / 5 else 0
  nonnegative x y := by split_ifs <;> norm_num
  bounded x y := by split_ifs <;> norm_num
  reflexive x := by simp
  symmetric x y := by fin_cases x <;> fin_cases y <;> norm_num

def gradedCompletion : Tolerance (Fin 3) where
  similarity x y := if x = y then 1 else if x = 1 ∨ y = 1 then 4 / 5 else 3 / 5
  nonnegative x y := by split_ifs <;> norm_num
  bounded x y := by split_ifs <;> norm_num
  reflexive x := by simp
  symmetric x y := by fin_cases x <;> fin_cases y <;> norm_num

def gradedPaths (x y : Fin 3) : Certificate (Fin 3) :=
  if x = y then .refl x else if x = 1 ∨ y = 1 then .edge x y else throughMiddle x y

theorem graded_completion_checked :
    completionCheck graded gradedCompletion gradedPaths = true := by
  simp only [completionCheck, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;> norm_num [graded, gradedCompletion, Fin.ext_iff]
  · intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;>
      norm_num [Tolerance.distance, gradedCompletion, Fin.ext_iff]
  · intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [check, gradedPaths, throughMiddle, infer, graded, gradedCompletion,
        Tolerance.distance, Fin.ext_iff]

theorem graded_completion_is_least : LeastMetricExtension graded gradedCompletion :=
  completionCheck_sound graded_completion_checked

theorem graded_fractional_bound_checked :
    check graded ⟨0, 2, 2 / 5⟩ (throughMiddle 0 2) = true := by
  norm_num [check, infer, throughMiddle, graded, Tolerance.distance, Fin.ext_iff]

/-- Feasible all-ones completion is not automatically the least completion. -/
theorem graded_no_endpoint_collapse_certificate :
    ¬ ∃ proof, check graded ⟨0, 2, 0⟩ proof = true := by
  rintro ⟨proof, accepted⟩
  have bound := check_sound accepted gradedCompletion graded_completion_is_least.2.1
    graded_completion_is_least.1
  norm_num [Tolerance.distance, gradedCompletion, Fin.ext_iff] at bound

def uniformThree : Distribution (Fin 3) where
  weight _ := 1 / 3
  nonnegative _ := by norm_num
  normalized := by norm_num [Fin.sum_univ_succ]

theorem uniformThree_average (f : Fin 3 → Fin 3 → ℚ) :
    uniformThree.pairAverage f =
      (f 0 0 + f 0 1 + f 0 2 + f 1 0 + f 1 1 + f 1 2 + f 2 0 + f 2 1 + f 2 2) / 9 := by
  simp [Distribution.pairAverage, uniformThree, Fin.sum_univ_succ]
  ring

theorem chain_distinction_lost_by_closure :
    uniformThree.graphtropy chain = 7 / 9 ∧ uniformThree.distinction chain = 2 / 9 ∧
      uniformThree.graphtropy collapsed = 1 ∧ uniformThree.distinction collapsed = 0 := by
  rw [Distribution.distinction_eq_one_sub, Distribution.distinction_eq_one_sub]
  norm_num [Distribution.graphtropy, uniformThree_average, collapsed, Tolerance.ofReport,
    Fin.ext_iff]

/-- Zero mass can hide a real distortion; it is not a full-support theorem. -/
def pointMass : Distribution Bool where
  weight b := if b = false then 1 else 0
  nonnegative b := by split_ifs <;> norm_num
  normalized := by simp

def fineBool : Tolerance Bool := Tolerance.ofReport id
def coarseBool : Tolerance Bool := Tolerance.ofReport (fun _ => false)

theorem zero_average_without_global_preservation :
    pointMass.distortion fineBool coarseBool id = 0 ∧
      fineBool.similarity false true ≠ coarseBool.similarity false true := by
  norm_num [Distribution.distortion, Distribution.pairAverage, pointMass, fineBool, coarseBool,
    Tolerance.ofReport]

def uniformBool : Distribution Bool where
  weight _ := 1 / 2
  nonnegative _ := by norm_num
  normalized := by norm_num

/-- The same observed change can help or harm a declared goal. Distortion
alone therefore cannot serve as a certificate of beneficial self-modification. -/
theorem same_distortion_opposite_value_changes :
    uniformBool.distortion fineBool fineBool (fun _ => true) = 1 / 2 ∧
      uniformBool.distortion fineBool fineBool (fun _ => false) = 1 / 2 ∧
      uniformBool.valueChange (fun b => if b then 1 else 0) (fun _ => true) = 1 / 2 ∧
      uniformBool.valueChange (fun b => if b then 1 else 0) (fun _ => false) = -(1 / 2) := by
  norm_num [Distribution.distortion, Distribution.pairAverage, Distribution.valueChange,
    uniformBool, fineBool, Tolerance.ofReport]

end Mettapedia.Cybernetics.DistinctionCalculus.Examples
