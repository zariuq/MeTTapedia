import Mathlib.Tactic

/-!
# Linear two-task continual learning

This file formalizes the finite-dimensional linear-quadratic instances of the
causal-coding bridge.  Order interference is the commutator of task curvature
operators.  Sequential reuse is separately measured by the failure of two
successive task steps to equal one additive joint step; it can be nonzero even
when the curvatures commute.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

/-- A quadratic task is represented by its curvature matrix and optimum. -/
structure QuadraticTask (Index : Type*) where
  curvature : Matrix Index Index ℝ
  optimum : Index → ℝ

section TwoTask

variable {Index : Type*} [Fintype Index]

/-- Gradient of `1/2 (θ-μ)ᵀ A (θ-μ)`. -/
noncomputable def QuadraticTask.gradient (task : QuadraticTask Index)
    (parameter : Index → ℝ) : Index → ℝ :=
  task.curvature.mulVec (parameter - task.optimum)

/-- One gradient step on a quadratic task. -/
noncomputable def QuadraticTask.update (task : QuadraticTask Index)
    (stepSize : ℝ) (parameter : Index → ℝ) : Index → ℝ :=
  parameter - stepSize • task.gradient parameter

/-- One Euler step using the additive sum of two task gradients. -/
noncomputable def additiveTwoTaskUpdate (first second : QuadraticTask Index)
    (stepSize : ℝ) (parameter : Index → ℝ) : Index → ℝ :=
  parameter - stepSize • (first.gradient parameter + second.gradient parameter)

/-- A step on `first` followed by a step on `second`. -/
noncomputable def sequentialTwoTaskUpdate (first second : QuadraticTask Index)
    (stepSize : ℝ) (parameter : Index → ℝ) : Index → ℝ :=
  second.update stepSize (first.update stepSize parameter)

/-- Exact non-additivity of sequential learning.  The second-order term is
the second task's curvature acting on the first task's gradient. -/
theorem sequentialTwoTaskUpdate_sub_additive_exact
    (first second : QuadraticTask Index) (stepSize : ℝ)
    (parameter : Index → ℝ) :
    sequentialTwoTaskUpdate first second stepSize parameter -
        additiveTwoTaskUpdate first second stepSize parameter =
      stepSize ^ 2 • second.curvature.mulVec (first.gradient parameter) := by
  funext i
  simp only [sequentialTwoTaskUpdate, additiveTwoTaskUpdate,
    QuadraticTask.update, QuadraticTask.gradient, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec_sub, Matrix.mulVec_smul]
  ring

/-- Curvature commutator in the order induced by `second` after `first`. -/
noncomputable def curvatureCommutator (first second : QuadraticTask Index) :
    Matrix Index Index ℝ :=
  second.curvature * first.curvature - first.curvature * second.curvature

/-- Exact difference between the two sequential orders. -/
theorem sequentialTwoTaskUpdate_order_defect_exact
    (first second : QuadraticTask Index) (stepSize : ℝ)
    (parameter : Index → ℝ) :
    sequentialTwoTaskUpdate first second stepSize parameter -
        sequentialTwoTaskUpdate second first stepSize parameter =
      stepSize ^ 2 •
        (second.curvature.mulVec (first.gradient parameter) -
          first.curvature.mulVec (second.gradient parameter)) := by
  funext i
  simp only [sequentialTwoTaskUpdate, QuadraticTask.update,
    QuadraticTask.gradient, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec_sub, Matrix.mulVec_smul]
  ring

/-- For centered tasks, order interference is exactly the curvature
commutator acting on the current parameter. -/
theorem centered_sequential_order_defect_eq_commutator
    (first second : QuadraticTask Index)
    (hfirst : first.optimum = 0) (hsecond : second.optimum = 0)
    (stepSize : ℝ) (parameter : Index → ℝ) :
    sequentialTwoTaskUpdate first second stepSize parameter -
        sequentialTwoTaskUpdate second first stepSize parameter =
      stepSize ^ 2 • (curvatureCommutator first second).mulVec parameter := by
  rw [sequentialTwoTaskUpdate_order_defect_exact]
  simp only [QuadraticTask.gradient, hfirst, hsecond, sub_zero, curvatureCommutator,
    Matrix.sub_mulVec, Matrix.mulVec_mulVec]

/-- Commuting centered curvatures have no task-order interference. -/
theorem centered_sequential_updates_commute
    (first second : QuadraticTask Index)
    (hfirst : first.optimum = 0) (hsecond : second.optimum = 0)
    (hcommute : second.curvature * first.curvature =
      first.curvature * second.curvature)
    (stepSize : ℝ) (parameter : Index → ℝ) :
    sequentialTwoTaskUpdate first second stepSize parameter =
      sequentialTwoTaskUpdate second first stepSize parameter := by
  apply sub_eq_zero.mp
  rw [centered_sequential_order_defect_eq_commutator
    first second hfirst hsecond]
  simp [curvatureCommutator, hcommute]

/-! ## Exact positive and negative fixtures -/

noncomputable def scalarUnitTask : QuadraticTask (Fin 1) where
  curvature := 1
  optimum := 0

noncomputable def scalarUnitParameter : Fin 1 → ℝ := fun _ => 1

/-- Reusing the same scalar task has zero order defect but does not equal the
single additive joint step: the sequential result is `1/4`, while the joint
step is zero.  This is the linear same-cause double-counting fixture. -/
theorem sameCause_reuse_zero_commutator_nonadditive_fixture :
    sequentialTwoTaskUpdate scalarUnitTask scalarUnitTask (1 / 2)
        scalarUnitParameter = (fun _ => 1 / 4) ∧
      additiveTwoTaskUpdate scalarUnitTask scalarUnitTask (1 / 2)
        scalarUnitParameter = 0 ∧
      curvatureCommutator scalarUnitTask scalarUnitTask = 0 ∧
      sequentialTwoTaskUpdate scalarUnitTask scalarUnitTask (1 / 2)
          scalarUnitParameter ≠
        additiveTwoTaskUpdate scalarUnitTask scalarUnitTask (1 / 2)
          scalarUnitParameter := by
  constructor
  · funext i
    fin_cases i
    norm_num [sequentialTwoTaskUpdate, QuadraticTask.update,
      QuadraticTask.gradient, scalarUnitTask, scalarUnitParameter,
      Matrix.mulVec, dotProduct]
  constructor
  · funext i
    fin_cases i
    norm_num [additiveTwoTaskUpdate, QuadraticTask.gradient,
      scalarUnitTask, scalarUnitParameter, Matrix.mulVec, dotProduct]
  constructor
  · simp [curvatureCommutator]
  · intro h
    have hi := congrFun h (0 : Fin 1)
    norm_num [sequentialTwoTaskUpdate, additiveTwoTaskUpdate,
      QuadraticTask.update, QuadraticTask.gradient, scalarUnitTask,
      scalarUnitParameter, Matrix.mulVec, dotProduct] at hi

noncomputable def orthogonalFirstTask : QuadraticTask (Fin 2) where
  curvature := !![1, 0; 0, 0]
  optimum := 0

noncomputable def orthogonalSecondTask : QuadraticTask (Fin 2) where
  curvature := !![0, 0; 0, 1]
  optimum := 0

/-- Disjoint coordinate modules have neither curvature order interference nor
sequential non-additivity. -/
theorem orthogonalModules_no_interference_fixture
    (stepSize : ℝ) (parameter : Fin 2 → ℝ) :
    sequentialTwoTaskUpdate orthogonalFirstTask orthogonalSecondTask
        stepSize parameter =
      sequentialTwoTaskUpdate orthogonalSecondTask orthogonalFirstTask
        stepSize parameter ∧
    sequentialTwoTaskUpdate orthogonalFirstTask orthogonalSecondTask
        stepSize parameter =
      additiveTwoTaskUpdate orthogonalFirstTask orthogonalSecondTask
        stepSize parameter := by
  constructor
  · apply centered_sequential_updates_commute
    · rfl
    · rfl
    · apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        norm_num [orthogonalFirstTask, orthogonalSecondTask,
          Matrix.mul_apply, Fin.sum_univ_two]
  · apply sub_eq_zero.mp
    rw [sequentialTwoTaskUpdate_sub_additive_exact]
    funext i
    fin_cases i <;>
      simp [orthogonalFirstTask, orthogonalSecondTask, QuadraticTask.gradient,
        dotProduct, Fin.sum_univ_two]

noncomputable def obliqueFirstTask : QuadraticTask (Fin 2) where
  curvature := fun i j => if i.val = 0 ∧ j.val = 0 then 1 else 0
  optimum := 0

noncomputable def obliqueSecondTask : QuadraticTask (Fin 2) where
  curvature := fun _ _ => 1
  optimum := 0

noncomputable def obliqueParameter : Fin 2 → ℝ :=
  fun i => if i.val = 0 then 0 else 1

/-- Oblique task subspaces have a nonzero curvature commutator and path
dependence: the two update orders disagree. -/
theorem obliqueTasks_curvature_interference_fixture :
    curvatureCommutator obliqueFirstTask obliqueSecondTask ≠ 0 ∧
      sequentialTwoTaskUpdate obliqueFirstTask obliqueSecondTask 1
          obliqueParameter ≠
        sequentialTwoTaskUpdate obliqueSecondTask obliqueFirstTask 1
          obliqueParameter := by
  constructor
  · intro h
    have hij := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
    norm_num [curvatureCommutator, obliqueFirstTask, obliqueSecondTask,
      Matrix.mul_apply, Fin.sum_univ_two] at hij
  · intro h
    have hi := congrFun h (0 : Fin 2)
    norm_num [sequentialTwoTaskUpdate, QuadraticTask.update,
      QuadraticTask.gradient, obliqueFirstTask, obliqueSecondTask,
      obliqueParameter, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hi

/-- Crown separating the two proved linear mechanisms: oblique curvatures
produce order interference, while same-cause reuse produces non-additivity
despite a zero commutator. -/
theorem linearTwoTask_causalCoding_separation_crown :
    curvatureCommutator obliqueFirstTask obliqueSecondTask ≠ 0 ∧
      sequentialTwoTaskUpdate obliqueFirstTask obliqueSecondTask 1
          obliqueParameter ≠
        sequentialTwoTaskUpdate obliqueSecondTask obliqueFirstTask 1
          obliqueParameter ∧
      curvatureCommutator scalarUnitTask scalarUnitTask = 0 ∧
      sequentialTwoTaskUpdate scalarUnitTask scalarUnitTask (1 / 2)
          scalarUnitParameter ≠
        additiveTwoTaskUpdate scalarUnitTask scalarUnitTask (1 / 2)
          scalarUnitParameter :=
  ⟨obliqueTasks_curvature_interference_fixture.1,
    obliqueTasks_curvature_interference_fixture.2,
    sameCause_reuse_zero_commutator_nonadditive_fixture.2.2.1,
    sameCause_reuse_zero_commutator_nonadditive_fixture.2.2.2⟩

end TwoTask

end Mettapedia.MachineLearning.ContinualLearning
