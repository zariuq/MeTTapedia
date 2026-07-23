import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromSimultaneousBlocks
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromBalancedScalarShiftStability
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Routed CAROM: Hermitian word-energy stability

Simultaneous generalized eigenspaces of real commuting command families are
most naturally analyzed after complexification.  Their block eigenvalues are
therefore complex, so a real scalar-shift certificate is not sufficient.

This file constructs the corresponding positive Hermitian energy directly on
a complex inner-product space.  The energy is a weighted finite sum of squared
norms along all residual command words.  It is positive definite, homogeneous
under complex scalars, obeys the parallelogram identity, and contracts every
jointly nilpotent residual family.  A tunable balance parameter then absorbs
the cross term between a complex scalar contraction and the residual.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function

namespace RoutedCarom

universe uCommand uState

section HermitianWordEnergy

variable {Command : Type uCommand} [Fintype Command] [DecidableEq Command]
variable {V : Type uState} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Weighted energy of all residual command words up to the declared depth. -/
noncomputable def endWordEnergy
    (weight : ℝ) (residual : Command → Module.End ℂ V) : ℕ → V → ℝ
  | 0, state => ‖state‖ ^ 2
  | depth + 1, state =>
      ‖state‖ ^ 2 + weight * ∑ command : Command,
        endWordEnergy weight residual depth (residual command state)

/-- A scalar two-term Young bound, factored out for reuse by norm and word
energies. -/
theorem real_add_sq_le_balanced
    (balance : ℝ) (balance_pos : 0 < balance) (first second : ℝ) :
    (first + second) ^ 2 ≤
      (1 + balance) * first ^ 2 + (1 + 1 / balance) * second ^ 2 := by
  have difference_nonneg : 0 ≤ (balance * first - second) ^ 2 := sq_nonneg _
  have multipliedBound :
      balance * (first + second) ^ 2 ≤
        (balance ^ 2 + balance) * first ^ 2 +
          (1 + balance) * second ^ 2 := by
    nlinarith
  have weightedIdentity :
      balance *
          ((1 + balance) * first ^ 2 +
            (1 + 1 / balance) * second ^ 2) =
        (balance ^ 2 + balance) * first ^ 2 +
          (1 + balance) * second ^ 2 := by
    field_simp [ne_of_gt balance_pos]
    ring
  have multipliedGoal :
      (first + second) ^ 2 * balance ≤
        ((1 + balance) * first ^ 2 +
          (1 + 1 / balance) * second ^ 2) * balance := by
    calc
      (first + second) ^ 2 * balance =
          balance * (first + second) ^ 2 := mul_comm _ _
      _ ≤ (balance ^ 2 + balance) * first ^ 2 +
          (1 + balance) * second ^ 2 := multipliedBound
      _ = balance *
          ((1 + balance) * first ^ 2 +
            (1 + 1 / balance) * second ^ 2) := weightedIdentity.symm
      _ = ((1 + balance) * first ^ 2 +
          (1 + 1 / balance) * second ^ 2) * balance := mul_comm _ _
  exact (mul_le_mul_iff_left₀ balance_pos).mp multipliedGoal

omit [InnerProductSpace ℂ V] in
/-- Young's inequality for squared norms in a complex normed space. -/
theorem norm_add_sq_le_balanced
    (balance : ℝ) (balance_pos : 0 < balance) (first second : V) :
    ‖first + second‖ ^ 2 ≤
      (1 + balance) * ‖first‖ ^ 2 +
        (1 + 1 / balance) * ‖second‖ ^ 2 := by
  calc
    ‖first + second‖ ^ 2 ≤ (‖first‖ + ‖second‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (norm_add_le first second)
    _ ≤ (1 + balance) * ‖first‖ ^ 2 +
        (1 + 1 / balance) * ‖second‖ ^ 2 :=
      real_add_sq_le_balanced balance balance_pos _ _

omit [DecidableEq Command] in
/-- Word energy is nonnegative at every depth. -/
theorem endWordEnergy_nonneg
    (weight : ℝ) (weight_nonneg : 0 ≤ weight)
    (residual : Command → Module.End ℂ V) (depth : ℕ) (state : V) :
    0 ≤ endWordEnergy weight residual depth state := by
  induction depth generalizing state with
  | zero => simp [endWordEnergy]
  | succ depth ih =>
      rw [endWordEnergy]
      have sum_nonneg : 0 ≤ ∑ command : Command,
          endWordEnergy weight residual depth (residual command state) :=
        Finset.sum_nonneg fun command _ => ih (residual command state)
      positivity

omit [DecidableEq Command] in
/-- The current-state norm term makes every word energy strictly positive on
nonzero states. -/
theorem endWordEnergy_pos
    (weight : ℝ) (weight_nonneg : 0 ≤ weight)
    (residual : Command → Module.End ℂ V) (depth : ℕ)
    {state : V} (state_ne_zero : state ≠ 0) :
    0 < endWordEnergy weight residual depth state := by
  cases depth with
  | zero => simp [endWordEnergy, norm_pos_iff.mpr state_ne_zero]
  | succ depth =>
      rw [endWordEnergy]
      have norm_sq_pos : 0 < ‖state‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr state_ne_zero)
      have sum_nonneg : 0 ≤ ∑ command : Command,
          endWordEnergy weight residual depth (residual command state) :=
        Finset.sum_nonneg fun command _ =>
          endWordEnergy_nonneg weight weight_nonneg residual depth _
      positivity

omit [DecidableEq Command] in
/-- Word energy is homogeneous under arbitrary complex scalars. -/
theorem endWordEnergy_smul
    (weight : ℝ) (residual : Command → Module.End ℂ V)
    (depth : ℕ) (scalar : ℂ) (state : V) :
    endWordEnergy weight residual depth (scalar • state) =
      ‖scalar‖ ^ 2 * endWordEnergy weight residual depth state := by
  induction depth generalizing state with
  | zero =>
      simp only [endWordEnergy, norm_smul]
      ring
  | succ depth ih =>
      simp only [endWordEnergy, norm_smul, map_smul, ih]
      rw [← Finset.mul_sum]
      ring

omit [DecidableEq Command] in
/-- The word energy satisfies the parallelogram identity, making its
Hermitian quadratic character explicit rather than inferred from positivity
alone. -/
theorem endWordEnergy_parallelogram
    (weight : ℝ) (residual : Command → Module.End ℂ V)
    (depth : ℕ) (first second : V) :
    endWordEnergy weight residual depth (first + second) +
        endWordEnergy weight residual depth (first - second) =
      2 * (endWordEnergy weight residual depth first +
        endWordEnergy weight residual depth second) := by
  induction depth generalizing first second with
  | zero => exact parallelogram_law_with_norm ℂ first second
  | succ depth ih =>
      have baseIdentity := parallelogram_law_with_norm ℂ first second
      have sumIdentity :
          (∑ command : Command,
              endWordEnergy weight residual depth
                (residual command (first + second))) +
              ∑ command : Command,
                endWordEnergy weight residual depth
                  (residual command (first - second)) =
            2 * ((∑ command : Command,
                endWordEnergy weight residual depth (residual command first)) +
              ∑ command : Command,
                endWordEnergy weight residual depth (residual command second)) := by
        calc
          _ = ∑ command : Command,
              (endWordEnergy weight residual depth
                  (residual command (first + second)) +
                endWordEnergy weight residual depth
                  (residual command (first - second))) :=
            Finset.sum_add_distrib.symm
          _ = ∑ command : Command,
              2 * (endWordEnergy weight residual depth (residual command first) +
                endWordEnergy weight residual depth (residual command second)) := by
            apply Finset.sum_congr rfl
            intro command _
            rw [map_add, map_sub]
            exact ih (residual command first) (residual command second)
          _ = 2 * ∑ command : Command,
              (endWordEnergy weight residual depth (residual command first) +
                endWordEnergy weight residual depth (residual command second)) := by
            rw [Finset.mul_sum]
          _ = _ := by rw [Finset.sum_add_distrib]
      simp only [endWordEnergy]
      linear_combination baseIdentity + weight * sumIdentity

omit [DecidableEq Command] in
/-- The balanced two-term inequality lifts from the ambient squared norm to
every finite word energy. -/
theorem endWordEnergy_add_le_balanced
    (weight : ℝ) (weight_nonneg : 0 ≤ weight)
    (residual : Command → Module.End ℂ V)
    (depth : ℕ) (balance : ℝ) (balance_pos : 0 < balance)
    (first second : V) :
    endWordEnergy weight residual depth (first + second) ≤
      (1 + balance) * endWordEnergy weight residual depth first +
        (1 + 1 / balance) * endWordEnergy weight residual depth second := by
  induction depth generalizing first second with
  | zero => exact norm_add_sq_le_balanced balance balance_pos first second
  | succ depth ih =>
      rw [endWordEnergy, endWordEnergy, endWordEnergy]
      have base_bound := norm_add_sq_le_balanced balance balance_pos first second
      have sum_bound :
          ∑ command : Command,
              endWordEnergy weight residual depth
                (residual command (first + second)) ≤
            ∑ command : Command,
              ((1 + balance) *
                  endWordEnergy weight residual depth (residual command first) +
                (1 + 1 / balance) *
                  endWordEnergy weight residual depth (residual command second)) := by
        apply Finset.sum_le_sum
        intro command _
        rw [map_add]
        exact ih (residual command first) (residual command second)
      have weighted_sum_bound :=
        mul_le_mul_of_nonneg_left sum_bound weight_nonneg
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at weighted_sum_bound
      nlinarith

/-- State-level extinction under every residual command word of one length. -/
def EndStateVanishesAfter
    (residual : Command → Module.End ℂ V) (depth : ℕ) (state : V) : Prop :=
  ∀ schedule : List Command, schedule.length = depth →
    (schedule.map residual).prod state = 0

omit [Fintype Command] [DecidableEq Command] in
/-- One residual command consumes one level of a state-extinction
certificate. -/
theorem EndStateVanishesAfter.after_step
    {residual : Command → Module.End ℂ V} {depth : ℕ} {state : V}
    (vanishes : EndStateVanishesAfter residual (depth + 1) state)
    (command : Command) :
    EndStateVanishesAfter residual depth (residual command state) := by
  intro schedule schedule_length
  have extended := vanishes (schedule ++ [command]) (by simp [schedule_length])
  simpa [List.map_append, List.prod_append, Module.End.mul_apply] using extended

omit [Fintype Command] [DecidableEq Command] in
/-- Algebraic joint nilpotence implies state-level extinction. -/
theorem EndJointlyNilpotentAt.stateVanishesAfter
    {residual : Command → Module.End ℂ V} {depth : ℕ}
    (jointlyNilpotent : EndJointlyNilpotentAt residual depth)
    (state : V) : EndStateVanishesAfter residual depth state := by
  intro schedule schedule_length
  rw [jointlyNilpotent schedule schedule_length]
  rfl

omit [Fintype Command] [DecidableEq Command] in
/-- Joint nilpotence persists when one more residual command is appended to
the required word length. -/
theorem EndJointlyNilpotentAt.succ
    {residual : Command → Module.End ℂ V} {depth : ℕ}
    (jointlyNilpotent : EndJointlyNilpotentAt residual depth) :
    EndJointlyNilpotentAt residual (depth + 1) := by
  intro schedule schedule_length
  cases schedule with
  | nil => simp at schedule_length
  | cons command tail =>
      have tail_length : tail.length = depth := by simpa using schedule_length
      simp [jointlyNilpotent tail tail_length]

omit [DecidableEq Command] in
/-- Once all newly added command words vanish, word energy has reached a
plateau at that state. -/
theorem endWordEnergy_succ_eq_of_vanishesAfter
    (weight : ℝ) (residual : Command → Module.End ℂ V)
    (depth : ℕ) (state : V)
    (vanishes : EndStateVanishesAfter residual (depth + 1) state) :
    endWordEnergy weight residual (depth + 1) state =
      endWordEnergy weight residual depth state := by
  induction depth generalizing state with
  | zero =>
      rw [endWordEnergy]
      have step_zero (command : Command) : residual command state = 0 := by
        simpa [EndStateVanishesAfter] using vanishes [command] (by simp)
      have energy_zero (command : Command) :
          endWordEnergy weight residual 0 (residual command state) = 0 := by
        rw [step_zero]
        change ‖(0 : V)‖ ^ 2 = 0
        simp
      rw [endWordEnergy]
      simp_rw [energy_zero]
      simp
  | succ depth ih =>
      rw [endWordEnergy, endWordEnergy]
      congr 1
      apply congrArg (fun value : ℝ => weight * value)
      apply Finset.sum_congr rfl
      intro command _
      exact ih (residual command state) (vanishes.after_step command)

/-- A positive word weight turns joint residual extinction into uniform
one-step contraction by the inverse weight. -/
theorem endWordEnergy_residual_contracts
    (weight : ℝ) (weight_pos : 0 < weight)
    (residual : Command → Module.End ℂ V)
    (depth : ℕ)
    (jointlyNilpotent : EndJointlyNilpotentAt residual (depth + 2))
    (command : Command) (state : V) :
    endWordEnergy weight residual (depth + 1) (residual command state) ≤
      (1 / weight) * endWordEnergy weight residual (depth + 1) state := by
  rw [endWordEnergy_succ_eq_of_vanishesAfter weight residual depth
      (residual command state)
      ((jointlyNilpotent.stateVanishesAfter state).after_step command),
    endWordEnergy]
  have term_nonneg : ∀ other ∈ (Finset.univ : Finset Command),
      0 ≤ endWordEnergy weight residual depth (residual other state) :=
    fun other _ => endWordEnergy_nonneg weight weight_pos.le residual depth _
  have term_le_sum :
      endWordEnergy weight residual depth (residual command state) ≤
        ∑ other : Command,
          endWordEnergy weight residual depth (residual other state) :=
    Finset.single_le_sum term_nonneg (Finset.mem_univ command)
  have norm_sq_nonneg : 0 ≤ ‖state‖ ^ 2 := sq_nonneg _
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ weight_pos).2
  nlinarith

/-! ## Complex scalar shifts -/

/-- A common positive Hermitian energy certificate for a family of complex
linear transitions.  The parallelogram and scalar-homogeneity fields record
that the energy is genuinely quadratic over `ℂ`, rather than merely a
positive real-valued ranking function. -/
structure CommonHermitianEnergyLyapunov
    {Command : Type uCommand} {V : Type uState}
    [AddCommGroup V] [Module ℂ V]
    (transition : Command → Module.End ℂ V) where
  energy : V → ℝ
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  rate_lt_one : rate < 1
  energy_nonneg : ∀ state : V, 0 ≤ energy state
  energy_pos : ∀ {state : V}, state ≠ 0 → 0 < energy state
  energy_smul : ∀ (scalar : ℂ) (state : V),
    energy (scalar • state) = ‖scalar‖ ^ 2 * energy state
  parallelogram : ∀ (first second : V),
    energy (first + second) + energy (first - second) =
      2 * (energy first + energy second)
  contracts : ∀ (command : Command) (state : V),
    energy (transition command state) ≤ rate * energy state

/-- Add a command-dependent complex scalar part to a residual endomorphism. -/
noncomputable def endScalarShiftedTransition
    (coefficient : Command → ℂ)
    (residual : Command → Module.End ℂ V) :
    Command → Module.End ℂ V :=
  fun command => coefficient command • LinearMap.id + residual command

omit [Fintype Command] [DecidableEq Command] in
@[simp] theorem endScalarShiftedTransition_apply
    (coefficient : Command → ℂ)
    (residual : Command → Module.End ℂ V)
    (command : Command) (state : V) :
    endScalarShiftedTransition coefficient residual command state =
      coefficient command • state + residual command state := by
  simp [endScalarShiftedTransition]

/-- A complex scalar contraction plus a jointly nilpotent residual family has
a common Hermitian word-energy certificate whenever the displayed balanced
rate is strictly below one. -/
noncomputable def balancedEndScalarShiftedJointNilpotentCommonLyapunov
    (coefficient : Command → ℂ)
    (residual : Command → Module.End ℂ V)
    (depth : ℕ)
    (jointlyNilpotent : EndJointlyNilpotentAt residual (depth + 2))
    (weight radius balance : ℝ)
    (weight_pos : 0 < weight)
    (radius_nonneg : 0 ≤ radius)
    (balance_pos : 0 < balance)
    (coefficient_bound : ∀ command, ‖coefficient command‖ ≤ radius)
    (strict_rate :
      (1 + balance) * radius ^ 2 +
          (1 + 1 / balance) * (1 / weight) < 1) :
    CommonHermitianEnergyLyapunov
      (endScalarShiftedTransition coefficient residual) where
  energy := endWordEnergy weight residual (depth + 1)
  rate :=
    (1 + balance) * radius ^ 2 +
      (1 + 1 / balance) * (1 / weight)
  rate_nonneg := by positivity
  rate_lt_one := strict_rate
  energy_nonneg := endWordEnergy_nonneg weight weight_pos.le residual (depth + 1)
  energy_pos := endWordEnergy_pos weight weight_pos.le residual (depth + 1)
  energy_smul := endWordEnergy_smul weight residual (depth + 1)
  parallelogram := endWordEnergy_parallelogram weight residual (depth + 1)
  contracts := by
    intro command state
    have split_bound := endWordEnergy_add_le_balanced
      weight weight_pos.le residual (depth + 1) balance balance_pos
      (coefficient command • state) (residual command state)
    have coefficient_energy :=
      endWordEnergy_smul weight residual (depth + 1) (coefficient command) state
    have residual_energy := endWordEnergy_residual_contracts
      weight weight_pos residual depth jointlyNilpotent command state
    have radius_sq_bound : ‖coefficient command‖ ^ 2 ≤ radius ^ 2 := by
      nlinarith [norm_nonneg (coefficient command), coefficient_bound command]
    have state_energy_nonneg :
        0 ≤ endWordEnergy weight residual (depth + 1) state :=
      endWordEnergy_nonneg weight weight_pos.le residual (depth + 1) state
    have coefficient_term_le :
        (1 + balance) *
            (‖coefficient command‖ ^ 2 *
              endWordEnergy weight residual (depth + 1) state) ≤
          (1 + balance) *
            (radius ^ 2 * endWordEnergy weight residual (depth + 1) state) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right radius_sq_bound state_energy_nonneg)
        (by positivity)
    have residual_term_le :
        (1 + 1 / balance) *
            endWordEnergy weight residual (depth + 1) (residual command state) ≤
          (1 + 1 / balance) *
            ((1 / weight) * endWordEnergy weight residual (depth + 1) state) := by
      exact mul_le_mul_of_nonneg_left residual_energy (by positivity)
    rw [endScalarShiftedTransition_apply]
    rw [coefficient_energy] at split_bound
    calc
      endWordEnergy weight residual (depth + 1)
          (coefficient command • state + residual command state) ≤
          (1 + balance) *
              (‖coefficient command‖ ^ 2 *
                endWordEnergy weight residual (depth + 1) state) +
            (1 + 1 / balance) *
              endWordEnergy weight residual (depth + 1)
                (residual command state) := split_bound
      _ ≤ (1 + balance) *
              (radius ^ 2 * endWordEnergy weight residual (depth + 1) state) +
            (1 + 1 / balance) *
              ((1 / weight) *
                endWordEnergy weight residual (depth + 1) state) :=
        add_le_add coefficient_term_le residual_term_le
      _ = ((1 + balance) * radius ^ 2 +
              (1 + 1 / balance) * (1 / weight)) *
            endWordEnergy weight residual (depth + 1) state := by ring

/-- Every complex scalar radius strictly inside the unit disk admits a word
weight and balance producing a common Hermitian certificate. -/
theorem exists_balancedEndScalarShiftedJointNilpotentCommonLyapunov
    (coefficient : Command → ℂ)
    (residual : Command → Module.End ℂ V)
    (depth : ℕ)
    (jointlyNilpotent : EndJointlyNilpotentAt residual (depth + 2))
    (radius : ℝ) (radius_nonneg : 0 ≤ radius) (radius_lt_one : radius < 1)
    (coefficient_bound : ∀ command, ‖coefficient command‖ ≤ radius) :
    Nonempty
      (CommonHermitianEnergyLyapunov
        (endScalarShiftedTransition coefficient residual)) := by
  obtain ⟨balance, scale, balance_pos, scale_pos, strict_rate⟩ :=
    exists_balance_scale_strict_rate radius radius_nonneg radius_lt_one
  let weight : ℝ := 2 * scale ^ 2
  have weight_pos : 0 < weight := by
    dsimp [weight]
    positivity
  have converted_rate :
      (1 + balance) * radius ^ 2 +
          (1 + 1 / balance) * (1 / weight) < 1 := by
    dsimp [weight]
    simpa [div_eq_mul_inv] using strict_rate
  exact ⟨balancedEndScalarShiftedJointNilpotentCommonLyapunov
    coefficient residual depth jointlyNilpotent weight radius balance
    weight_pos radius_nonneg balance_pos coefficient_bound converted_rate⟩

/-! ## Simultaneous generalized blocks -/

omit [Fintype Command] [DecidableEq Command] in
/-- The transition restricted to a simultaneous generalized block is exactly
the complex scalar-shift family consumed by the Hermitian certificate. -/
theorem simultaneousBlockTransition_eq_endScalarShiftedTransition
    [FiniteDimensional ℂ V]
    (transition : Command → Module.End ℂ V)
    (commutes : ∀ first second,
      Commute (transition first) (transition second))
    (character : Command → ℂ) :
    simultaneousBlockTransition transition commutes character =
      endScalarShiftedTransition character
        (simultaneousBlockResidual transition commutes character) := by
  funext command
  rw [simultaneousBlockTransition_eq_scalar_add_residual]
  ext state
  simp [endScalarShiftedTransition]

/-- Every simultaneous generalized block whose character lies strictly
inside one common radius has a common Hermitian contraction metric for all
commands. -/
theorem exists_simultaneousBlockCommonHermitianEnergy
    [FiniteDimensional ℂ V]
    (transition : Command → Module.End ℂ V)
    (commutes : ∀ first second,
      Commute (transition first) (transition second))
    (character : Command → ℂ)
    (radius : ℝ) (radius_nonneg : 0 ≤ radius) (radius_lt_one : radius < 1)
    (character_bound : ∀ command, ‖character command‖ ≤ radius) :
    Nonempty
      (CommonHermitianEnergyLyapunov
        (simultaneousBlockTransition transition commutes character)) := by
  let residual := simultaneousBlockResidual transition commutes character
  let nilpotent : ∀ command, IsNilpotent (residual command) :=
    simultaneousBlockResidual_isNilpotent transition commutes character
  let depth := jointNilpotenceBudget
    (positiveNilpotenceDepth residual nilpotent)
  have jointlyNilpotent : EndJointlyNilpotentAt residual depth :=
    simultaneousBlockResidual_endJointlyNilpotentAt
      transition commutes character
  have certificate :=
    exists_balancedEndScalarShiftedJointNilpotentCommonLyapunov
      character residual depth jointlyNilpotent.succ.succ
      radius radius_nonneg radius_lt_one character_bound
  rw [simultaneousBlockTransition_eq_endScalarShiftedTransition]
  exact certificate

/-! ## Positive and negative fixtures -/

/-- Zero residual dynamics on one complex state coordinate. -/
noncomputable def zeroComplexResidual (_ : Unit) : Module.End ℂ ℂ := 0

/-- The zero residual family is jointly nilpotent after one command. -/
theorem zeroComplexResidual_jointlyNilpotent :
    EndJointlyNilpotentAt zeroComplexResidual 1 := by
  intro schedule schedule_length
  cases schedule with
  | nil => simp at schedule_length
  | cons command tail => simp [zeroComplexResidual]

/-- A strict complex scalar contraction close to the unit circle receives a
Hermitian certificate. -/
noncomputable def nineTenthsComplexCoefficient (_ : Unit) : ℂ := 9 / 10

noncomputable def nineTenthsComplexCommonHermitianEnergy :
    CommonHermitianEnergyLyapunov
      (endScalarShiftedTransition nineTenthsComplexCoefficient
        zeroComplexResidual) :=
  Classical.choice
    (exists_balancedEndScalarShiftedJointNilpotentCommonLyapunov
      nineTenthsComplexCoefficient zeroComplexResidual 1
      zeroComplexResidual_jointlyNilpotent.succ.succ
      (9 / 10) (by norm_num) (by norm_num)
      (fun command => by cases command; norm_num [nineTenthsComplexCoefficient]))

/-- Unit scalar radius cannot satisfy the strict balanced-rate gate, even if
the residual contribution is made arbitrarily small. -/
theorem unitComplexRadius_balanced_rate_fails
    (weight balance : ℝ) (weight_pos : 0 < weight) (balance_pos : 0 < balance) :
    ¬ ((1 + balance) * (1 : ℝ) ^ 2 +
        (1 + 1 / balance) * (1 / weight) < 1) := by
  have residual_nonneg :
      0 ≤ (1 + 1 / balance) * (1 / weight) := by positivity
  nlinarith

/-- The unit complex identity transition is a genuine semantic boundary: no
positive Hermitian energy can contract it at a rate strictly below one. -/
noncomputable def unitComplexIdentityTransition (_ : Unit) : Module.End ℂ ℂ :=
  LinearMap.id

theorem unitComplexIdentityTransition_noCommonHermitianEnergy :
    ¬ Nonempty (CommonHermitianEnergyLyapunov unitComplexIdentityTransition) := by
  rintro ⟨certificate⟩
  have positive : 0 < certificate.energy (1 : ℂ) :=
    certificate.energy_pos one_ne_zero
  have contraction := certificate.contracts () (1 : ℂ)
  have identity_step : unitComplexIdentityTransition () (1 : ℂ) = 1 := rfl
  rw [identity_step] at contraction
  nlinarith [certificate.rate_lt_one]

#print axioms real_add_sq_le_balanced
#print axioms norm_add_sq_le_balanced
#print axioms endWordEnergy_nonneg
#print axioms endWordEnergy_pos
#print axioms endWordEnergy_smul
#print axioms endWordEnergy_parallelogram
#print axioms endWordEnergy_add_le_balanced
#print axioms EndStateVanishesAfter.after_step
#print axioms EndJointlyNilpotentAt.stateVanishesAfter
#print axioms EndJointlyNilpotentAt.succ
#print axioms endWordEnergy_succ_eq_of_vanishesAfter
#print axioms endWordEnergy_residual_contracts
#print axioms CommonHermitianEnergyLyapunov
#print axioms endScalarShiftedTransition_apply
#print axioms balancedEndScalarShiftedJointNilpotentCommonLyapunov
#print axioms exists_balancedEndScalarShiftedJointNilpotentCommonLyapunov
#print axioms simultaneousBlockTransition_eq_endScalarShiftedTransition
#print axioms exists_simultaneousBlockCommonHermitianEnergy
#print axioms zeroComplexResidual_jointlyNilpotent
#print axioms nineTenthsComplexCommonHermitianEnergy
#print axioms unitComplexRadius_balanced_rate_fails
#print axioms unitComplexIdentityTransition_noCommonHermitianEnergy

end HermitianWordEnergy

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
