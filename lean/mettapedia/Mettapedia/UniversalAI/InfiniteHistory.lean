import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Infinite-history interaction core

This file defines a minimal measure-theoretic core for infinite histories using
Ionescu-Tulcea. The goal is to make "value = integral over trajectories" the
primitive notion, and derive finite-horizon or recursive views as lemmas later.

Positive example: if `reward : Prod Action Percept -> Real` is bounded and
`w : Nat -> Real` is
absolutely summable, then `fun traj => tsum (fun n => w n * reward (traj n))`
is bounded and integrable, so `value` is well-defined.

Negative example: if `reward` is unbounded or `w n = 1` (not summable), then the
trajectory utility need not be integrable, so `value` is not defined without
extra assumptions.
-/

namespace Mettapedia.UniversalAI.InfiniteHistory

universe u v uX

variable {Action : Type u} {Percept : Type v}
  [MeasurableSpace Action] [MeasurableSpace Percept]

abbrev TrajectoryOf (X : Nat -> Type uX) : Type uX :=
  (n : Nat) -> X n
abbrev PrefixOf (X : Nat -> Type uX) (n : Nat) : Type uX :=
  (i : Finset.Iic n) -> X i

abbrev StepFamily (Action : Type u) (Percept : Type v) : Nat -> Type (max u v) :=
  fun _ => Prod Action Percept
abbrev Trajectory (Action : Type u) (Percept : Type v) : Type (max u v) :=
  TrajectoryOf (StepFamily Action Percept)
abbrev Prefix (Action : Type u) (Percept : Type v) (n : Nat) : Type (max u v) :=
  PrefixOf (StepFamily Action Percept) n

instance prefixMeasurableSpace (Action : Type u) (Percept : Type v)
    [MeasurableSpace Action] [MeasurableSpace Percept] (n : Nat) :
    MeasurableSpace (Prefix Action Percept n) := by
  dsimp [Prefix]
  infer_instance

instance trajectoryMeasurableSpace (Action : Type u) (Percept : Type v)
    [MeasurableSpace Action] [MeasurableSpace Percept] :
    MeasurableSpace (Trajectory Action Percept) := by
  dsimp [Trajectory]
  infer_instance

instance prefixOfMeasurableSpace (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)] (n : Nat) : MeasurableSpace (PrefixOf X n) := by
  dsimp [PrefixOf]
  infer_instance

instance trajectoryOfMeasurableSpace (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)] : MeasurableSpace (TrajectoryOf X) := by
  dsimp [TrajectoryOf]
  infer_instance

/-- Combine a policy kernel and environment kernel into a step kernel. -/
noncomputable def stepKernel
    (pi : (n : Nat) -> ProbabilityTheory.Kernel (Prefix Action Percept n) Action)
    (mu :
      (n : Nat) -> ProbabilityTheory.Kernel (Prod (Prefix Action Percept n) Action) Percept) :
    (n : Nat) ->
      ProbabilityTheory.Kernel (Prefix Action Percept n) (StepFamily Action Percept (n + 1)) :=
  fun n => ProbabilityTheory.Kernel.compProd (pi n) (mu n)

instance stepKernel_isMarkov
    (pi : (n : Nat) -> ProbabilityTheory.Kernel (Prefix Action Percept n) Action)
    (mu :
      (n : Nat) -> ProbabilityTheory.Kernel (Prod (Prefix Action Percept n) Action) Percept)
    [hpi : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (pi n)]
    [hmu : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (mu n)] :
    (n : Nat) -> ProbabilityTheory.IsMarkovKernel
      (stepKernel (Action:=Action) (Percept:=Percept) pi mu n) := by
  intro n
  dsimp [stepKernel]
  infer_instance

noncomputable def trajKernelOf (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)]
    (κ : (n : Nat) -> ProbabilityTheory.Kernel (PrefixOf X n) (X (n + 1)))
    [hκ : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (κ n)]
    (a : Nat) :
    ProbabilityTheory.Kernel (PrefixOf X a) (TrajectoryOf X) :=
  ProbabilityTheory.Kernel.traj (κ := κ) a

noncomputable def trajMeasureOf (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)]
    (κ : (n : Nat) -> ProbabilityTheory.Kernel (PrefixOf X n) (X (n + 1)))
    [hκ : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (κ n)]
    (a : Nat) (mu0 : MeasureTheory.Measure (PrefixOf X a)) :
    MeasureTheory.Measure (TrajectoryOf X) :=
  MeasureTheory.Measure.bind mu0 (trajKernelOf (X := X) (κ := κ) a)

@[simp] theorem trajKernelOf_eq (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)]
    (κ : (n : Nat) -> ProbabilityTheory.Kernel (PrefixOf X n) (X (n + 1)))
    [hκ : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (κ n)]
    (a : Nat) :
    trajKernelOf (X := X) (κ := κ) a = ProbabilityTheory.Kernel.traj (κ := κ) a := rfl

@[simp] theorem trajMeasureOf_eq (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)]
    (κ : (n : Nat) -> ProbabilityTheory.Kernel (PrefixOf X n) (X (n + 1)))
    [hκ : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (κ n)]
    (a : Nat) (mu0 : MeasureTheory.Measure (PrefixOf X a)) :
    trajMeasureOf (X := X) (κ := κ) a mu0 =
      MeasureTheory.Measure.bind mu0 (ProbabilityTheory.Kernel.traj (κ := κ) a) := rfl

instance trajKernelOf_isMarkov (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)]
    (κ : (n : Nat) -> ProbabilityTheory.Kernel (PrefixOf X n) (X (n + 1)))
    [hκ : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (κ n)]
    (a : Nat) : ProbabilityTheory.IsMarkovKernel (trajKernelOf (X := X) (κ := κ) a) := by
  dsimp [trajKernelOf]
  infer_instance

instance trajMeasureOf_isProbability (X : Nat -> Type uX)
    [∀ n, MeasurableSpace (X n)]
    (κ : (n : Nat) -> ProbabilityTheory.Kernel (PrefixOf X n) (X (n + 1)))
    [hκ : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (κ n)]
    (a : Nat) (mu0 : MeasureTheory.Measure (PrefixOf X a))
    [MeasureTheory.IsProbabilityMeasure mu0] :
    MeasureTheory.IsProbabilityMeasure (trajMeasureOf (X := X) (κ := κ) a mu0) := by
  dsimp [trajMeasureOf]
  infer_instance

/-- Kernel on trajectories given a policy/environment kernel family. -/
noncomputable def trajKernel
    (pi : (n : Nat) -> ProbabilityTheory.Kernel (Prefix Action Percept n) Action)
    (mu :
      (n : Nat) -> ProbabilityTheory.Kernel (Prod (Prefix Action Percept n) Action) Percept)
    [hpi : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (pi n)]
    [hmu : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (mu n)]
    (a : Nat) :
    ProbabilityTheory.Kernel (Prefix Action Percept a) (Trajectory Action Percept) :=
  trajKernelOf (X := StepFamily Action Percept)
    (κ := stepKernel (Action:=Action) (Percept:=Percept) pi mu) a

/-- Measure on trajectories obtained by binding an initial prefix measure. -/
noncomputable def trajMeasure
    (pi : (n : Nat) -> ProbabilityTheory.Kernel (Prefix Action Percept n) Action)
    (mu :
      (n : Nat) -> ProbabilityTheory.Kernel (Prod (Prefix Action Percept n) Action) Percept)
    [hpi : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (pi n)]
    [hmu : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (mu n)]
    (a : Nat) (mu0 : MeasureTheory.Measure (Prefix Action Percept a)) :
    MeasureTheory.Measure (Trajectory Action Percept) :=
  trajMeasureOf (X := StepFamily Action Percept)
    (κ := stepKernel (Action:=Action) (Percept:=Percept) pi mu) a mu0

/-- Value of a utility under a trajectory measure. -/
noncomputable def value
    (P : MeasureTheory.Measure (Trajectory Action Percept))
    (U : Trajectory Action Percept -> Real) : Real :=
  MeasureTheory.integral P U

/-- Value induced by a policy/environment and an initial prefix measure. -/
noncomputable def valueFrom
    (pi : (n : Nat) -> ProbabilityTheory.Kernel (Prefix Action Percept n) Action)
    (mu :
      (n : Nat) -> ProbabilityTheory.Kernel (Prod (Prefix Action Percept n) Action) Percept)
    [hpi : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (pi n)]
    [hmu : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (mu n)]
    (a : Nat) (mu0 : MeasureTheory.Measure (Prefix Action Percept a))
    (U : Trajectory Action Percept -> Real) : Real :=
  value (Action:=Action) (Percept:=Percept)
    (trajMeasure (Action:=Action) (Percept:=Percept) pi mu a mu0) U

/-- Value from a concrete prefix using the trajectory kernel. -/
noncomputable def valueFromPrefix
    (pi : (n : Nat) -> ProbabilityTheory.Kernel (Prefix Action Percept n) Action)
    (mu :
      (n : Nat) -> ProbabilityTheory.Kernel (Prod (Prefix Action Percept n) Action) Percept)
    [hpi : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (pi n)]
    [hmu : (n : Nat) -> ProbabilityTheory.IsMarkovKernel (mu n)]
    (a : Nat) (pref : Prefix Action Percept a)
    (U : Trajectory Action Percept -> Real) : Real :=
  MeasureTheory.integral ((trajKernel (Action:=Action) (Percept:=Percept) pi mu a) pref) U

section DiscountedUtility

variable {Action : Type u} {Percept : Type v}
  [MeasurableSpace Action] [MeasurableSpace Percept]

/-- Shift a trajectory by `k` steps. -/
def trajShift (k : ℕ) (traj : Trajectory Action Percept) : Trajectory Action Percept :=
  fun n => traj (k + n)

/-- Shift a weight sequence by `k` steps. -/
def weightShift (k : ℕ) (w : ℕ → ℝ) : ℕ → ℝ :=
  fun n => w (k + n)

/-- Infinite-horizon discounted utility on trajectories. -/
noncomputable def discountedUtility
    (reward : Action × Percept → ℝ) (w : ℕ → ℝ) :
    Trajectory Action Percept → ℝ :=
  fun traj => tsum fun n => w n * reward (traj n)

/-- Finite-horizon truncation of discounted utility. -/
noncomputable def discountedUtilityTrunc
    (reward : Action × Percept → ℝ) (w : ℕ → ℝ) (t : ℕ) :
    Trajectory Action Percept → ℝ :=
  fun traj => (Finset.range t).sum fun n => w n * reward (traj n)

/-- Discounted utility from time `k` onward. -/
noncomputable def discountedUtilityFrom
    (reward : Action × Percept → ℝ) (w : ℕ → ℝ) (k : ℕ) :
    Trajectory Action Percept → ℝ :=
  fun traj => discountedUtility reward (weightShift k w) (trajShift k traj)

theorem measurable_reward_at
    (reward : Action × Percept → ℝ) (k : ℕ) (h_reward : Measurable reward) :
    Measurable fun traj : Trajectory Action Percept => reward (traj k) := by
  have h_eval : Measurable fun traj : Trajectory Action Percept => traj k := by
    simpa using (measurable_pi_apply (a := k))
  exact h_reward.comp h_eval

theorem measurable_discountedUtilityTrunc
    (reward : Action × Percept → ℝ) (w : ℕ → ℝ) (t : ℕ)
    (h_reward : Measurable reward) :
    Measurable (discountedUtilityTrunc (Action := Action) (Percept := Percept) reward w t) := by
  classical
  refine Finset.measurable_fun_sum (Finset.range t) ?_
  intro n hn
  have h_at := measurable_reward_at (Action := Action) (Percept := Percept)
    (reward := reward) (k := n) h_reward
  simpa [discountedUtilityTrunc] using (measurable_const.mul h_at)

omit [MeasurableSpace Action] [MeasurableSpace Percept] in
theorem summable_discountedUtility_of_bound
    (reward : Action × Percept → ℝ) (w : ℕ → ℝ) (R : ℝ)
    (h_reward_bound : ∀ s, |reward s| ≤ R)
    (hw : Summable (fun n => |w n|)) :
    ∀ traj : Trajectory Action Percept,
      Summable (fun n => w n * reward (traj n)) := by
  intro traj
  have hsum : Summable fun n => |w n| * R := (Summable.mul_right R hw)
  refine Summable.of_norm_bounded hsum ?_
  intro n
  have h_bound : |reward (traj n)| ≤ R := h_reward_bound _
  have h_nonneg : 0 ≤ |w n| := abs_nonneg _
  have h_mul : |w n| * |reward (traj n)| ≤ |w n| * R :=
    mul_le_mul_of_nonneg_left h_bound h_nonneg
  simpa [Real.norm_eq_abs, abs_mul] using h_mul

theorem measurable_discountedUtility
    (reward : Action × Percept → ℝ) (w : ℕ → ℝ) (R : ℝ)
    (h_reward : Measurable reward)
    (h_reward_bound : ∀ s, |reward s| ≤ R)
    (hw : Summable (fun n => |w n|)) :
    Measurable (discountedUtility (Action := Action) (Percept := Percept) reward w) := by
  have h_meas : ∀ t,
      Measurable (discountedUtilityTrunc (Action := Action) (Percept := Percept) reward w t) :=
    fun t => measurable_discountedUtilityTrunc (Action := Action) (Percept := Percept)
      (reward := reward) (w := w) (t := t) h_reward
  refine measurable_of_tendsto_metrizable h_meas ?_
  refine tendsto_pi_nhds.2 ?_
  intro traj
  have hsum :
      Summable (fun n => w n * reward (traj n)) :=
    summable_discountedUtility_of_bound (Action := Action) (Percept := Percept)
      (reward := reward) (w := w) (R := R) h_reward_bound hw traj
  have hhas :
      HasSum (fun n => w n * reward (traj n))
        (discountedUtility (Action := Action) (Percept := Percept) reward w traj) := by
    simpa [discountedUtility] using hsum.hasSum
  simpa [discountedUtilityTrunc] using hhas.tendsto_sum_nat

omit [MeasurableSpace Action] [MeasurableSpace Percept] in
theorem tendsto_discountedUtilityTrunc
    (reward : Action × Percept → ℝ) (w : ℕ → ℝ) (R : ℝ)
    (h_reward_bound : ∀ s, |reward s| ≤ R)
    (hw : Summable (fun n => |w n|)) (traj : Trajectory Action Percept) :
    Filter.Tendsto
        (fun t =>
          discountedUtilityTrunc (Action := Action) (Percept := Percept) reward w t traj)
        Filter.atTop
        (nhds (discountedUtility (Action := Action) (Percept := Percept) reward w traj)) := by
  have hsum :
      Summable (fun n => w n * reward (traj n)) :=
    summable_discountedUtility_of_bound (Action := Action) (Percept := Percept)
      (reward := reward) (w := w) (R := R) h_reward_bound hw traj
  have hhas :
      HasSum (fun n => w n * reward (traj n))
        (discountedUtility (Action := Action) (Percept := Percept) reward w traj) := by
    simpa [discountedUtility] using hsum.hasSum
  simpa [discountedUtilityTrunc] using hhas.tendsto_sum_nat

omit [MeasurableSpace Action] [MeasurableSpace Percept] in
theorem discountedUtility_norm_le
    (reward : Action × Percept → ℝ) (w : ℕ → ℝ) (R : ℝ)
    (h_reward_bound : ∀ s, |reward s| ≤ R)
    (hw : Summable (fun n => |w n|)) (traj : Trajectory Action Percept) :
    ‖discountedUtility (Action := Action) (Percept := Percept) reward w traj‖ ≤
      tsum (fun n => |w n| * R) := by
  have hsum : Summable fun n => |w n| * R := (Summable.mul_right R hw)
  have h_has : HasSum (fun n => |w n| * R) (tsum fun n => |w n| * R) := hsum.hasSum
  have h_bound : ∀ n, ‖w n * reward (traj n)‖ ≤ |w n| * R := by
    intro n
    have h_r : |reward (traj n)| ≤ R := h_reward_bound _
    have h_nonneg : 0 ≤ |w n| := abs_nonneg _
    have h_mul : |w n| * |reward (traj n)| ≤ |w n| * R :=
      mul_le_mul_of_nonneg_left h_r h_nonneg
    simpa [Real.norm_eq_abs, abs_mul] using h_mul
  have h :=
    tsum_of_norm_bounded (f := fun n => w n * reward (traj n))
      (g := fun n => |w n| * R) (a := tsum fun n => |w n| * R) h_has h_bound
  simpa [discountedUtility] using h

theorem integrable_discountedUtility
    (reward : Action × Percept → ℝ) (w : ℕ → ℝ) (R : ℝ)
    (h_reward : Measurable reward)
    (h_reward_bound : ∀ s, |reward s| ≤ R)
    (hw : Summable (fun n => |w n|))
    (μ : MeasureTheory.Measure (Trajectory Action Percept))
    [MeasureTheory.IsFiniteMeasure μ] :
    MeasureTheory.Integrable
      (discountedUtility (Action := Action) (Percept := Percept) reward w) μ := by
  have h_meas :
      Measurable (discountedUtility (Action := Action) (Percept := Percept) reward w) :=
    measurable_discountedUtility (Action := Action) (Percept := Percept)
      (reward := reward) (w := w) (R := R) h_reward h_reward_bound hw
  have h_bound :
      ∀ᵐ traj ∂μ,
        ‖discountedUtility (Action := Action) (Percept := Percept) reward w traj‖ ≤
          tsum (fun n => |w n| * R) := by
    refine Filter.Eventually.of_forall ?_
    intro traj
    exact discountedUtility_norm_le (Action := Action) (Percept := Percept)
      (reward := reward) (w := w) (R := R) h_reward_bound hw traj
  exact MeasureTheory.Integrable.of_bound h_meas.aestronglyMeasurable _ h_bound

theorem tendsto_integral_discountedUtilityTrunc
    (reward : Action × Percept → ℝ) (w : ℕ → ℝ) (R : ℝ)
    (h_reward : Measurable reward)
    (h_reward_bound : ∀ s, |reward s| ≤ R) (h_R_nonneg : 0 ≤ R)
    (hw : Summable (fun n => |w n|))
    (μ : MeasureTheory.Measure (Trajectory Action Percept))
    [MeasureTheory.IsFiniteMeasure μ] :
    Filter.Tendsto
        (fun t =>
          ∫ traj, discountedUtilityTrunc (Action := Action) (Percept := Percept) reward w t traj ∂ μ)
        Filter.atTop
        (nhds (∫ traj, discountedUtility (Action := Action) (Percept := Percept) reward w traj ∂ μ)) := by
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := fun _ => tsum (fun n => |w n| * R)) ?_ ?_ ?_ ?_
  · intro t
    exact
      (measurable_discountedUtilityTrunc (Action := Action) (Percept := Percept)
        (reward := reward) (w := w) (t := t) h_reward).aestronglyMeasurable
  ·
    exact
      (MeasureTheory.integrable_const (tsum fun n => |w n| * R) :
        MeasureTheory.Integrable
          (fun _ : Trajectory Action Percept => tsum (fun n => |w n| * R)) μ)
  ·
    intro t
    refine Filter.Eventually.of_forall ?_
    intro traj
    have hsum : Summable fun n => |w n| * R := (Summable.mul_right R hw)
    have h_bound : ∀ n, ‖w n * reward (traj n)‖ ≤ |w n| * R := by
      intro n
      have h_r : |reward (traj n)| ≤ R := h_reward_bound _
      have h_nonneg : 0 ≤ |w n| := abs_nonneg _
      have h_mul : |w n| * |reward (traj n)| ≤ |w n| * R :=
        mul_le_mul_of_nonneg_left h_r h_nonneg
      simpa [Real.norm_eq_abs, abs_mul] using h_mul
    have hsum_trunc :
        ‖(Finset.range t).sum (fun n => w n * reward (traj n))‖ ≤
          (Finset.range t).sum (fun n => |w n| * R) :=
      norm_sum_le_of_le _ fun n _ => h_bound n
    have hsum_trunc' :
        (Finset.range t).sum (fun n => |w n| * R) ≤
          tsum (fun n => |w n| * R) :=
      hsum.sum_le_tsum (Finset.range t) fun n _ =>
        mul_nonneg (abs_nonneg _) h_R_nonneg
    have hsum_trunc'' :
        ‖(Finset.range t).sum (fun n => w n * reward (traj n))‖ ≤
          tsum (fun n => |w n| * R) :=
      le_trans hsum_trunc hsum_trunc'
    simpa [discountedUtilityTrunc] using hsum_trunc''
  ·
    refine Filter.Eventually.of_forall ?_
    intro traj
    exact
      tendsto_discountedUtilityTrunc (Action := Action) (Percept := Percept)
        (reward := reward) (w := w) (R := R) h_reward_bound hw traj

omit [MeasurableSpace Action] [MeasurableSpace Percept] in
theorem discountedUtilityTrunc_zero
    (reward : Action × Percept → ℝ) (w : ℕ → ℝ) (traj : Trajectory Action Percept) :
    discountedUtilityTrunc reward w 0 traj = 0 := by
  simp [discountedUtilityTrunc]

omit [MeasurableSpace Action] [MeasurableSpace Percept] in
theorem discountedUtilityTrunc_succ
    (reward : Action × Percept → ℝ) (w : ℕ → ℝ) (t : ℕ) (traj : Trajectory Action Percept) :
    discountedUtilityTrunc reward w (t + 1) traj =
      discountedUtilityTrunc reward w t traj + w t * reward (traj t) := by
  simp [discountedUtilityTrunc, Finset.sum_range_succ]

end DiscountedUtility

end Mettapedia.UniversalAI.InfiniteHistory
