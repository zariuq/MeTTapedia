import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromCommutingNilpotentStability
import Mathlib.Data.List.Perm.Subperm

/-!
# Routed CAROM: common metrics for finite jointly nilpotent command families

This file separates two statements that should not be conflated:

1. a finite command semigroup is jointly nilpotent;
2. joint nilpotence yields a common positive-definite quadratic metric.

The metric construction itself does not require pairwise commutation.  It is a
geometrically weighted sum of all command continuations up to a finite depth,
defined recursively.  If every sufficiently long continuation vanishes, one
application of any command shifts the energy down one level and contracts it
by `1/2`.

Pairwise commutation becomes relevant in the next theorem layer, where it can
turn individual nilpotence bounds into joint nilpotence.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function
open scoped Matrix BigOperators

namespace RoutedCarom

universe uCommand uIndex

section FiniteFamily

variable {Command : Type uCommand} [Fintype Command] [DecidableEq Command]
variable {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- Recursively weighted word metric.  Depth zero observes only the current
state.  Every further depth includes all one-command continuations with twice
the previous weight. -/
noncomputable def jointNilpotentMetric
    (transition : Command → Matrix Index Index ℝ) : ℕ → Matrix Index Index ℝ
  | 0 => 1
  | depth + 1 =>
      1 + (2 : ℝ) • ∑ command : Command,
        (transition command).transpose *
          jointNilpotentMetric transition depth * transition command

omit [DecidableEq Index] in
/-- Quadratic energy of a matrix sandwich is the inner energy after applying
the command. -/
theorem quadraticEnergy_transpose_mul_mul_same
    (metric transition : Matrix Index Index ℝ) (state : Index → ℝ) :
    quadraticEnergy (transition.transpose * metric * transition) state =
      quadraticEnergy metric (transition *ᵥ state) := by
  simp only [quadraticEnergy]
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

omit [DecidableEq Index] in
theorem quadraticEnergy_add
    (first second : Matrix Index Index ℝ) (state : Index → ℝ) :
    quadraticEnergy (first + second) state =
      quadraticEnergy first state + quadraticEnergy second state := by
  simp [quadraticEnergy, Matrix.add_mulVec, dotProduct_add]

omit [DecidableEq Index] in
theorem quadraticEnergy_smul
    (scalar : ℝ) (metric : Matrix Index Index ℝ) (state : Index → ℝ) :
    quadraticEnergy (scalar • metric) state =
      scalar * quadraticEnergy metric state := by
  simp [quadraticEnergy, Matrix.smul_mulVec, dotProduct_smul]

theorem quadraticEnergy_one (state : Index → ℝ) :
    quadraticEnergy (1 : Matrix Index Index ℝ) state =
      dotProduct state state := by
  simp [quadraticEnergy]

omit [DecidableEq Command] [DecidableEq Index] in
theorem quadraticEnergy_sum
    (metric : Command → Matrix Index Index ℝ) (state : Index → ℝ) :
    quadraticEnergy (∑ command : Command, metric command) state =
      ∑ command : Command, quadraticEnergy (metric command) state := by
  simp [quadraticEnergy, Matrix.sum_mulVec, dotProduct_sum]

omit [DecidableEq Command] in
/-- Energy recursion corresponding to `jointNilpotentMetric`. -/
theorem jointNilpotentMetric_energy_succ
    (transition : Command → Matrix Index Index ℝ)
    (depth : ℕ) (state : Index → ℝ) :
    quadraticEnergy (jointNilpotentMetric transition (depth + 1)) state =
      dotProduct state state +
        2 * ∑ command : Command,
          quadraticEnergy (jointNilpotentMetric transition depth)
            (transition command *ᵥ state) := by
  rw [jointNilpotentMetric, quadraticEnergy_add, quadraticEnergy_one,
    quadraticEnergy_smul, quadraticEnergy_sum]
  simp_rw [quadraticEnergy_transpose_mul_mul_same]

omit [DecidableEq Command] in
/-- Every recursively constructed word energy is nonnegative. -/
theorem jointNilpotentMetric_energy_nonneg
    (transition : Command → Matrix Index Index ℝ)
    (depth : ℕ) (state : Index → ℝ) :
    0 ≤ quadraticEnergy (jointNilpotentMetric transition depth) state := by
  induction depth generalizing state with
  | zero =>
      simp [jointNilpotentMetric, quadraticEnergy,
        real_dotProduct_self_nonneg state]
  | succ depth ih =>
      rw [jointNilpotentMetric_energy_succ]
      have hState := real_dotProduct_self_nonneg state
      have hTerms : 0 ≤ ∑ command : Command,
          quadraticEnergy (jointNilpotentMetric transition depth)
            (transition command *ᵥ state) :=
        Finset.sum_nonneg fun command _ => ih (transition command *ᵥ state)
      positivity

omit [DecidableEq Command] in
/-- The identity term at every depth makes the word metric strictly positive
on nonzero states. -/
theorem jointNilpotentMetric_energy_pos
    (transition : Command → Matrix Index Index ℝ)
    (depth : ℕ) {state : Index → ℝ} (state_ne_zero : state ≠ 0) :
    0 < quadraticEnergy (jointNilpotentMetric transition depth) state := by
  cases depth with
  | zero =>
      simp only [jointNilpotentMetric, quadraticEnergy, Matrix.one_mulVec]
      have hNonneg := real_dotProduct_self_nonneg state
      have hNe : dotProduct state state ≠ 0 := by simpa using state_ne_zero
      exact lt_of_le_of_ne hNonneg (Ne.symm hNe)
  | succ depth =>
      rw [jointNilpotentMetric_energy_succ]
      have hStateNonneg := real_dotProduct_self_nonneg state
      have hStateNe : dotProduct state state ≠ 0 := by simpa using state_ne_zero
      have hStatePos : 0 < dotProduct state state :=
        lt_of_le_of_ne hStateNonneg (Ne.symm hStateNe)
      have hTerms : 0 ≤ ∑ command : Command,
          quadraticEnergy (jointNilpotentMetric transition depth)
            (transition command *ᵥ state) :=
        Finset.sum_nonneg fun command _ =>
          jointNilpotentMetric_energy_nonneg transition depth
            (transition command *ᵥ state)
      positivity

omit [DecidableEq Command] in
/-- Every recursively constructed word metric is symmetric. -/
theorem jointNilpotentMetric_isSymm
    (transition : Command → Matrix Index Index ℝ) (depth : ℕ) :
    (jointNilpotentMetric transition depth).IsSymm := by
  induction depth with
  | zero => simp [jointNilpotentMetric]
  | succ depth ih =>
      have termSymm (command : Command) :
          ((transition command).transpose *
              jointNilpotentMetric transition depth *
              transition command).IsSymm := by
        rw [Matrix.IsSymm]
        simp [Matrix.transpose_mul, ih.eq, Matrix.mul_assoc]
      have sumSymm :
          (∑ command : Command, (transition command).transpose *
            jointNilpotentMetric transition depth *
              transition command).IsSymm := by
        rw [Matrix.IsSymm, Matrix.transpose_sum]
        exact Finset.sum_congr rfl fun command _ => (termSymm command).eq
      exact Matrix.isSymm_one.add (sumSymm.smul (2 : ℝ))

omit [DecidableEq Command] in
/-- Matrix-level strict positivity of the recursive word metric. -/
theorem jointNilpotentMetric_posDef
    (transition : Command → Matrix Index Index ℝ) (depth : ℕ) :
    (jointNilpotentMetric transition depth).PosDef := by
  exact Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_iff_isSymm.mpr
      (jointNilpotentMetric_isSymm transition depth)) fun state state_ne_zero => by
        simpa [quadraticEnergy] using
          jointNilpotentMetric_energy_pos transition depth state_ne_zero

/-- A state vanishes after exactly `depth` further commands, regardless of
which command sequence is chosen. -/
def StateVanishesAfter
    (transition : Command → Matrix Index Index ℝ)
    (depth : ℕ) (state : Index → ℝ) : Prop :=
  ∀ schedule : List Command, schedule.length = depth →
    runLinearSchedule transition schedule state = 0

omit [Fintype Command] [DecidableEq Command] [DecidableEq Index] in
/-- One command consumes one level of a state-vanishing certificate. -/
theorem StateVanishesAfter.after_step
    {transition : Command → Matrix Index Index ℝ}
    {depth : ℕ} {state : Index → ℝ}
    (vanishes : StateVanishesAfter transition (depth + 1) state)
    (command : Command) :
    StateVanishesAfter transition depth (transition command *ᵥ state) := by
  intro schedule schedule_length
  exact vanishes (command :: schedule) (by simp [schedule_length])

omit [DecidableEq Command] in
/-- Once all words at the newly added depth vanish, the recursive energy has
already reached a plateau at that state. -/
theorem jointNilpotentMetric_energy_succ_eq_of_vanishesAfter
    (transition : Command → Matrix Index Index ℝ)
    (depth : ℕ) (state : Index → ℝ)
    (vanishes : StateVanishesAfter transition (depth + 1) state) :
    quadraticEnergy (jointNilpotentMetric transition (depth + 1)) state =
      quadraticEnergy (jointNilpotentMetric transition depth) state := by
  induction depth generalizing state with
  | zero =>
      rw [jointNilpotentMetric_energy_succ]
      have step_zero (command : Command) : transition command *ᵥ state = 0 := by
        simpa [StateVanishesAfter, runLinearSchedule] using
          vanishes [command] (by simp)
      simp_rw [step_zero]
      simp [jointNilpotentMetric, quadraticEnergy]
  | succ depth ih =>
      rw [jointNilpotentMetric_energy_succ,
        jointNilpotentMetric_energy_succ]
      congr 1
      apply congrArg (fun value : ℝ => 2 * value)
      apply Finset.sum_congr rfl
      intro command _
      exact ih (transition command *ᵥ state) (vanishes.after_step command)

/-- A command family is jointly nilpotent at `depth` when every state
vanishes under every command sequence of that length. -/
def JointlyNilpotentAt
    (transition : Command → Matrix Index Index ℝ) (depth : ℕ) : Prop :=
  ∀ state, StateVanishesAfter transition depth state

omit [Fintype Command] [DecidableEq Command] [DecidableEq Index] in
/-- Joint extinction persists for every longer schedule. -/
theorem JointlyNilpotentAt.succ
    {transition : Command → Matrix Index Index ℝ} {depth : ℕ}
    (jointlyNilpotent : JointlyNilpotentAt transition depth) :
    JointlyNilpotentAt transition (depth + 1) := by
  intro state schedule schedule_length
  cases schedule with
  | nil => simp at schedule_length
  | cons command schedule =>
      exact jointlyNilpotent (transition command *ᵥ state) schedule <| by
        simpa using Nat.succ.inj schedule_length

omit [DecidableEq Command] in
/-- Joint nilpotence supplies the missing top-level plateau after applying
one command. -/
theorem jointNilpotentMetric_after_command_plateau
    (transition : Command → Matrix Index Index ℝ)
    (depth : ℕ)
    (jointlyNilpotent : JointlyNilpotentAt transition (depth + 2))
    (command : Command) (state : Index → ℝ) :
    quadraticEnergy (jointNilpotentMetric transition (depth + 1))
        (transition command *ᵥ state) =
      quadraticEnergy (jointNilpotentMetric transition depth)
        (transition command *ᵥ state) := by
  exact jointNilpotentMetric_energy_succ_eq_of_vanishesAfter
    transition depth (transition command *ᵥ state)
      ((jointlyNilpotent state).after_step command)

/-- Any one command contracts the shared recursive metric by `1/2`. -/
theorem jointlyNilpotentMetric_contracts
    (transition : Command → Matrix Index Index ℝ)
    (depth : ℕ)
    (jointlyNilpotent : JointlyNilpotentAt transition (depth + 2))
    (command : Command) (state : Index → ℝ) :
    quadraticEnergy (jointNilpotentMetric transition (depth + 1))
        (transition command *ᵥ state) ≤
      (1 / 2 : ℝ) *
        quadraticEnergy (jointNilpotentMetric transition (depth + 1)) state := by
  rw [jointNilpotentMetric_after_command_plateau transition depth
      jointlyNilpotent command state,
    jointNilpotentMetric_energy_succ]
  have termNonneg : ∀ other ∈ (Finset.univ : Finset Command),
      0 ≤ quadraticEnergy (jointNilpotentMetric transition depth)
        (transition other *ᵥ state) := fun other _ =>
    jointNilpotentMetric_energy_nonneg transition depth
      (transition other *ᵥ state)
  have term_le_sum :
      quadraticEnergy (jointNilpotentMetric transition depth)
          (transition command *ᵥ state) ≤
        ∑ other : Command,
          quadraticEnergy (jointNilpotentMetric transition depth)
            (transition other *ᵥ state) := by
    exact Finset.single_le_sum termNonneg (Finset.mem_univ command)
  have stateNonneg := real_dotProduct_self_nonneg state
  linarith

/-- Constructed common quadratic Lyapunov certificate for any finite jointly
nilpotent command family. -/
noncomputable def jointlyNilpotentCommonLyapunov
    (transition : Command → Matrix Index Index ℝ)
    (depth : ℕ)
    (jointlyNilpotent : JointlyNilpotentAt transition (depth + 2)) :
    CommonQuadraticLyapunov transition where
  metric := jointNilpotentMetric transition (depth + 1)
  rate := 1 / 2
  rate_nonneg := by norm_num
  rate_lt_one := by norm_num
  energy_nonneg := jointNilpotentMetric_energy_nonneg transition (depth + 1)
  contracts := jointlyNilpotentMetric_contracts transition depth jointlyNilpotent

/-- Schedule-level crown for finite jointly nilpotent families. -/
theorem jointlyNilpotent_allSchedules_energy_le
    (transition : Command → Matrix Index Index ℝ)
    (depth : ℕ)
    (jointlyNilpotent : JointlyNilpotentAt transition (depth + 2))
    (schedule : List Command) (initial : Index → ℝ) :
    quadraticEnergy (jointNilpotentMetric transition (depth + 1))
        (runLinearSchedule transition schedule initial) ≤
      (1 / 2 : ℝ) ^ schedule.length *
        quadraticEnergy (jointNilpotentMetric transition (depth + 1)) initial := by
  exact (jointlyNilpotentCommonLyapunov transition depth jointlyNilpotent)
    |>.runLinearSchedule_energy_le schedule initial

/-! ## From commuting individual nilpotence to joint nilpotence -/

/-- The sharp counting budget obtained by allowing each command to occur one
fewer time than its individual nilpotence depth. -/
def jointNilpotenceBudget (nilpotenceDepth : Command → ℕ) : ℕ :=
  (∑ command : Command, (nilpotenceDepth command - 1)) + 1

/-- A schedule at the joint budget contains some command at least as many
times as that command's individual nilpotence depth. -/
theorem exists_nilpotenceDepth_le_count
    (nilpotenceDepth : Command → ℕ)
    (depth_pos : ∀ command, 0 < nilpotenceDepth command)
    (schedule : List Command)
    (schedule_length : schedule.length = jointNilpotenceBudget nilpotenceDepth) :
    ∃ command, nilpotenceDepth command ≤ schedule.count command := by
  classical
  by_contra no_command
  have count_lt_depth (command : Command) :
      schedule.count command < nilpotenceDepth command := by
    exact Nat.lt_of_not_ge fun count_ge =>
      no_command ⟨command, count_ge⟩
  have count_le_pred (command : Command) :
      schedule.count command ≤ nilpotenceDepth command - 1 := by
    have := count_lt_depth command
    have := depth_pos command
    omega
  have sum_le :
      (∑ command : Command, schedule.count command) ≤
        ∑ command : Command, (nilpotenceDepth command - 1) :=
    Finset.sum_le_sum fun command _ => count_le_pred command
  have sum_count_eq_length :
      (∑ command : Command, schedule.count command) = schedule.length := by
    rw [← List.sum_toFinset_count_eq_length schedule]
    symm
    apply Finset.sum_subset (by simp)
    intro command _ command_not_mem
    have : command ∉ schedule := by simpa using command_not_mem
    exact List.count_eq_zero.mpr this
  rw [sum_count_eq_length, schedule_length, jointNilpotenceBudget] at sum_le
  omega

omit [Fintype Command] [DecidableEq Command] in
/-- Under pairwise commutation, schedule execution equals multiplication by
the list product in the schedule's original order. -/
theorem runLinearSchedule_eq_prod_mulVec_of_pairwiseCommute
    (transition : Command → Matrix Index Index ℝ)
    (pairwiseCommute : ∀ first second,
      Commute (transition first) (transition second))
    (schedule : List Command) (state : Index → ℝ) :
    runLinearSchedule transition schedule state =
      (schedule.map transition).prod *ᵥ state := by
  induction schedule generalizing state with
  | nil => simp [runLinearSchedule]
  | cons command schedule ih =>
      have commutesWithTail :
          Commute (transition command) (schedule.map transition).prod :=
        Commute.list_prod_right (schedule.map transition) (transition command) <| by
          intro matrix matrix_mem
          obtain ⟨other, _, rfl⟩ := List.mem_map.mp matrix_mem
          exact pairwiseCommute command other
      rw [runLinearSchedule, ih, Matrix.mulVec_mulVec,
        ← commutesWithTail.eq]
      rfl

omit [Fintype Command] [DecidableEq Command] [DecidableEq Index] in
/-- Mapping a globally commuting command family over any schedule produces a
pairwise commuting matrix list. -/
theorem mappedTransitions_pairwiseCommute
    (transition : Command → Matrix Index Index ℝ)
    (pairwiseCommute : ∀ first second,
      Commute (transition first) (transition second))
    (schedule : List Command) :
    (schedule.map transition).Pairwise Commute := by
  induction schedule with
  | nil => simp
  | cons command schedule ih =>
      simp only [List.map_cons, List.pairwise_cons]
      constructor
      · intro matrix matrix_mem
        obtain ⟨other, _, rfl⟩ := List.mem_map.mp matrix_mem
        exact pairwiseCommute command other
      · exact ih

/-- Pairwise commuting commands that are individually nilpotent are jointly
nilpotent at the finite counting budget. -/
theorem pairwiseCommuting_individuallyNilpotent_jointlyNilpotentAt
    (transition : Command → Matrix Index Index ℝ)
    (nilpotenceDepth : Command → ℕ)
    (depth_pos : ∀ command, 0 < nilpotenceDepth command)
    (individuallyNilpotent : ∀ command,
      transition command ^ nilpotenceDepth command = 0)
    (pairwiseCommute : ∀ first second,
      Commute (transition first) (transition second)) :
    JointlyNilpotentAt transition (jointNilpotenceBudget nilpotenceDepth) := by
  classical
  intro state schedule schedule_length
  obtain ⟨command, depth_le_count⟩ :=
    exists_nilpotenceDepth_le_count nilpotenceDepth depth_pos schedule schedule_length
  let repeated := List.replicate (nilpotenceDepth command) command
  have repeated_subperm : List.Subperm repeated schedule := by
    apply List.subperm_iff_count.mpr
    intro other
    by_cases other_eq : other = command
    · subst other
      simpa [repeated] using depth_le_count
    · have other_not_mem : other ∉ repeated := by
        simp [repeated, other_eq]
      rw [List.count_eq_zero.mpr other_not_mem]
      exact Nat.zero_le _
  have grouped_perm :
      List.Perm (repeated ++ schedule.diff repeated) schedule :=
    List.subperm_append_diff_self_of_count_le
      (List.subperm_ext_iff.mp repeated_subperm)
  have mapped_prod_eq :
      ((repeated ++ schedule.diff repeated).map transition).prod =
        (schedule.map transition).prod :=
    (grouped_perm.map transition).prod_eq'
      (mappedTransitions_pairwiseCommute transition pairwiseCommute _)
  rw [runLinearSchedule_eq_prod_mulVec_of_pairwiseCommute transition
      pairwiseCommute schedule state,
    ← mapped_prod_eq, List.map_append, List.prod_append]
  have repeated_prod_zero : (repeated.map transition).prod = 0 := by
    simp [repeated, individuallyNilpotent command]
  rw [repeated_prod_zero, zero_mul, Matrix.zero_mulVec]

/-- The resulting finite-family common metric, now discharged from local
nilpotence and commutation hypotheses rather than assumed joint extinction. -/
noncomputable def commutingIndividuallyNilpotentCommonLyapunov
    (transition : Command → Matrix Index Index ℝ)
    (nilpotenceDepth : Command → ℕ)
    (depth_pos : ∀ command, 0 < nilpotenceDepth command)
    (individuallyNilpotent : ∀ command,
      transition command ^ nilpotenceDepth command = 0)
    (pairwiseCommute : ∀ first second,
      Commute (transition first) (transition second)) :
    CommonQuadraticLyapunov transition := by
  have joint := pairwiseCommuting_individuallyNilpotent_jointlyNilpotentAt
    transition nilpotenceDepth depth_pos individuallyNilpotent pairwiseCommute
  exact jointlyNilpotentCommonLyapunov transition
    (jointNilpotenceBudget nilpotenceDepth) joint.succ.succ

/-! ## Positive and negative fixtures -/

/-- The two distinct commuting square-zero fixtures are jointly nilpotent
after three commands. -/
theorem commutingNilpotentAB_jointlyNilpotentAt_three :
    JointlyNilpotentAt
      (twoCommandTransition commutingNilpotentA commutingNilpotentB) 3 := by
  intro state schedule schedule_length
  obtain ⟨first, second, third, rfl⟩ := List.length_eq_three.mp schedule_length
  cases first <;> cases second <;> cases third <;>
    funext index <;> fin_cases index <;>
      simp [runLinearSchedule, twoCommandTransition,
        commutingNilpotentA, commutingNilpotentB,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The divergent pair is not jointly nilpotent even at length two. -/
theorem divergentSwitches_not_jointlyNilpotentAt_two :
    ¬ JointlyNilpotentAt
      (twoCommandTransition divergentSwitchA divergentSwitchB) 2 := by
  intro jointlyNilpotent
  have vanishes := jointlyNilpotent ![0, 1] [false, true] (by simp)
  have coordinate := congr_fun vanishes 1
  norm_num [runLinearSchedule, twoCommandTransition,
    divergentSwitchA, divergentSwitchB, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at coordinate

/-- Both commands in the positive fixture have individual nilpotence depth
two. -/
def commutingNilpotentABDepth (_ : Bool) : ℕ := 2

theorem commutingNilpotentAB_individuallyNilpotent
    (command : Bool) :
    twoCommandTransition commutingNilpotentA commutingNilpotentB command ^
        commutingNilpotentABDepth command = 0 := by
  cases command <;>
    simp [commutingNilpotentABDepth, twoCommandTransition, pow_two,
      commutingNilpotentA_square_zero, commutingNilpotentB_square_zero]

theorem commutingNilpotentAB_pairwiseCommute
    (first second : Bool) :
    Commute
      (twoCommandTransition commutingNilpotentA commutingNilpotentB first)
      (twoCommandTransition commutingNilpotentA commutingNilpotentB second) := by
  cases first <;> cases second
  · exact Commute.refl _
  · exact commutingNilpotentAB_commute
  · exact commutingNilpotentAB_commute.symm
  · exact Commute.refl _

/-- Positive fixture routed through the finite-family construction rather
than the specialized two-command formula. -/
noncomputable def commutingNilpotentABFamilyCommonLyapunov :
    CommonQuadraticLyapunov
      (twoCommandTransition commutingNilpotentA commutingNilpotentB) :=
  commutingIndividuallyNilpotentCommonLyapunov
    (twoCommandTransition commutingNilpotentA commutingNilpotentB)
    commutingNilpotentABDepth
    (fun command => by cases command <;> norm_num [commutingNilpotentABDepth])
    commutingNilpotentAB_individuallyNilpotent
    commutingNilpotentAB_pairwiseCommute

#print axioms quadraticEnergy_transpose_mul_mul_same
#print axioms jointNilpotentMetric_energy_succ
#print axioms jointNilpotentMetric_posDef
#print axioms jointNilpotentMetric_energy_succ_eq_of_vanishesAfter
#print axioms jointlyNilpotentMetric_contracts
#print axioms jointlyNilpotentCommonLyapunov
#print axioms jointlyNilpotent_allSchedules_energy_le
#print axioms exists_nilpotenceDepth_le_count
#print axioms runLinearSchedule_eq_prod_mulVec_of_pairwiseCommute
#print axioms pairwiseCommuting_individuallyNilpotent_jointlyNilpotentAt
#print axioms commutingIndividuallyNilpotentCommonLyapunov
#print axioms commutingNilpotentAB_jointlyNilpotentAt_three
#print axioms divergentSwitches_not_jointlyNilpotentAt_two
#print axioms commutingNilpotentABFamilyCommonLyapunov

end FiniteFamily

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
