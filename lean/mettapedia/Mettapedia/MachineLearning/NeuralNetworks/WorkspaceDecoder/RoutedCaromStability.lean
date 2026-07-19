import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromCommutation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Routed CAROM: switched stability boundary

Individual discrete-time stability is not closed under arbitrary switching.
The explicit two-dimensional fixture below uses two nilpotent matrices: each
command kills every state in two repetitions, yet alternating the commands
produces an exponentially growing coordinate.

This does not contradict contraction theory.  Two strict contractions in one
common norm cannot exhibit the fixture.  The positive theorem therefore uses
the correct switched-systems hypothesis: one common quadratic Lyapunov
function whose contraction inequality holds for every command.  It yields a
uniform geometric energy bound for every finite schedule.  Pairwise
commutation is kept separate: it controls command order, while the common
Lyapunov certificate controls schedule stability.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function Filter
open scoped BigOperators Matrix Topology

namespace RoutedCarom

universe uCommand uIndex

/-! ## Individually nilpotent commands with divergent alternation -/

/-- First individually nilpotent switch. -/
noncomputable def divergentSwitchA : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 2; 0, 0]

/-- Second individually nilpotent switch. -/
noncomputable def divergentSwitchB : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; 2, 0]

theorem divergentSwitchA_square_zero :
    divergentSwitchA * divergentSwitchA = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [divergentSwitchA, Matrix.mul_apply, Fin.sum_univ_two]

theorem divergentSwitchB_square_zero :
    divergentSwitchB * divergentSwitchB = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [divergentSwitchB, Matrix.mul_apply, Fin.sum_univ_two]

/-- Each command is stronger than merely Schur-stable: two repetitions send
every state exactly to zero. -/
theorem divergentSwitches_individually_extinguish
    (state : Fin 2 → ℝ) :
    divergentSwitchA *ᵥ (divergentSwitchA *ᵥ state) = 0 ∧
      divergentSwitchB *ᵥ (divergentSwitchB *ᵥ state) = 0 := by
  constructor
  · rw [Matrix.mulVec_mulVec, divergentSwitchA_square_zero]
    simp
  · rw [Matrix.mulVec_mulVec, divergentSwitchB_square_zero]
    simp

/-- One alternating `A`-then-`B` cycle. -/
noncomputable def divergentCycleStep (state : Fin 2 → ℝ) : Fin 2 → ℝ :=
  divergentSwitchB *ᵥ (divergentSwitchA *ᵥ state)

theorem divergentCycleStep_exact (x y : ℝ) :
    divergentCycleStep ![x, y] = ![0, 4 * y] := by
  funext i
  fin_cases i
  · norm_num [divergentCycleStep, divergentSwitchA, divergentSwitchB,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · norm_num [divergentCycleStep, divergentSwitchA, divergentSwitchB,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- State after `cycles` alternating command pairs from the second basis
vector. -/
noncomputable def divergentAlternatingState (cycles : ℕ) : Fin 2 → ℝ :=
  (divergentCycleStep^[cycles]) ![0, 1]

/-- Exact exponential growth under alternation. -/
theorem divergentAlternatingState_exact (cycles : ℕ) :
    divergentAlternatingState cycles = ![0, (4 : ℝ) ^ cycles] := by
  induction cycles with
  | zero => simp [divergentAlternatingState]
  | succ cycles ih =>
      rw [divergentAlternatingState, Function.iterate_succ_apply']
      change divergentCycleStep (divergentAlternatingState cycles) = _
      rw [ih, divergentCycleStep_exact, pow_succ]
      simp [mul_comm]

/-- T4 negative crown: the alternating trajectory is unbounded in its second
coordinate even though both constituent commands are nilpotent. -/
theorem individuallyStable_switchingDiverges
    (bound : ℝ) :
    ∃ cycles : ℕ, bound < divergentAlternatingState cycles 1 := by
  obtain ⟨cycles, hcycles⟩ :=
    pow_unbounded_of_one_lt bound (by norm_num : (1 : ℝ) < 4)
  refine ⟨cycles, ?_⟩
  rw [divergentAlternatingState_exact]
  simpa using hcycles

/-! ## Common quadratic Lyapunov stability -/

/-- Quadratic energy induced by a matrix.  Positivity is supplied explicitly
by the Lyapunov certificate below. -/
noncomputable def quadraticEnergy
    {Index : Type uIndex} [Fintype Index]
    (metric : Matrix Index Index ℝ) (state : Index → ℝ) : ℝ :=
  dotProduct state (metric *ᵥ state)

/-- A single quadratic Lyapunov certificate shared by every command. -/
structure CommonQuadraticLyapunov
    {Command : Type uCommand} {Index : Type uIndex} [Fintype Index]
    (transition : Command → Matrix Index Index ℝ) where
  metric : Matrix Index Index ℝ
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  rate_lt_one : rate < 1
  energy_nonneg : ∀ state, 0 ≤ quadraticEnergy metric state
  contracts : ∀ command state,
    quadraticEnergy metric (transition command *ᵥ state) ≤
      rate * quadraticEnergy metric state

/-- Execute a finite command schedule, in list order. -/
noncomputable def runLinearSchedule
    {Command : Type uCommand} {Index : Type uIndex} [Fintype Index]
    (transition : Command → Matrix Index Index ℝ) :
    List Command → (Index → ℝ) → (Index → ℝ)
  | [], state => state
  | command :: schedule, state =>
      runLinearSchedule transition schedule (transition command *ᵥ state)

/-- T4 positive crown: a common quadratic Lyapunov function gives one
geometric bound that holds for every command sequence and every depth. -/
theorem CommonQuadraticLyapunov.runLinearSchedule_energy_le
    {Command : Type uCommand} {Index : Type uIndex} [Fintype Index]
    {transition : Command → Matrix Index Index ℝ}
    (certificate : CommonQuadraticLyapunov transition)
    (schedule : List Command) (initial : Index → ℝ) :
    quadraticEnergy certificate.metric
        (runLinearSchedule transition schedule initial) ≤
      certificate.rate ^ schedule.length *
        quadraticEnergy certificate.metric initial := by
  induction schedule generalizing initial with
  | nil => simp [runLinearSchedule]
  | cons command schedule ih =>
      calc
        quadraticEnergy certificate.metric
            (runLinearSchedule transition (command :: schedule) initial) =
            quadraticEnergy certificate.metric
              (runLinearSchedule transition schedule
                (transition command *ᵥ initial)) := rfl
        _ ≤ certificate.rate ^ schedule.length *
              quadraticEnergy certificate.metric
                (transition command *ᵥ initial) := ih _
        _ ≤ certificate.rate ^ schedule.length *
              (certificate.rate *
                quadraticEnergy certificate.metric initial) :=
          mul_le_mul_of_nonneg_left (certificate.contracts command initial)
            (pow_nonneg certificate.rate_nonneg _)
        _ = certificate.rate ^ (command :: schedule).length *
              quadraticEnergy certificate.metric initial := by
          simp [pow_succ, mul_assoc]

/-- The geometric envelope supplied by every common certificate tends to
zero. -/
theorem CommonQuadraticLyapunov.geometricEnvelope_tendsto_zero
    {Command : Type uCommand} {Index : Type uIndex} [Fintype Index]
    {transition : Command → Matrix Index Index ℝ}
    (certificate : CommonQuadraticLyapunov transition)
    (initial : Index → ℝ) :
    Tendsto
      (fun depth : ℕ => certificate.rate ^ depth *
        quadraticEnergy certificate.metric initial)
      atTop (𝓝 0) := by
  simpa using
    (tendsto_pow_atTop_nhds_zero_of_lt_one certificate.rate_nonneg
      certificate.rate_lt_one).mul_const
        (quadraticEnergy certificate.metric initial)

/-! ## Stability and order are independent obligations -/

/-- Pairwise commutation makes every adjacent two-command exchange
order-independent at the state level. -/
theorem pairwiseLinearCommutation_iff_orderIndependence
    {Command : Type uCommand} {Index : Type uIndex} [Fintype Index]
    (transition : Command → Matrix Index Index ℝ) :
    (∀ first second, Commute (transition first) (transition second)) ↔
      ∀ first second state,
        transition second *ᵥ (transition first *ᵥ state) =
          transition first *ᵥ (transition second *ᵥ state) := by
  constructor
  · intro h first second
    simpa using (linearPhases_orderIndependent_iff_commute
      (transition first) (transition second)).2 (h first second)
  · intro h first second
    apply (linearPhases_orderIndependent_iff_commute
      (transition first) (transition second)).1
    simpa using h first second

/-- Combined switched-systems crown: commutation supplies order invariance;
the common Lyapunov certificate independently supplies uniform stability. -/
theorem commutingCommonQuadraticLyapunov_crown
    {Command : Type uCommand} {Index : Type uIndex} [Fintype Index]
    {transition : Command → Matrix Index Index ℝ}
    (certificate : CommonQuadraticLyapunov transition)
    (hcommute : ∀ first second,
      Commute (transition first) (transition second)) :
    (∀ first second state,
      transition second *ᵥ (transition first *ᵥ state) =
        transition first *ᵥ (transition second *ᵥ state)) ∧
      (∀ schedule initial,
        quadraticEnergy certificate.metric
            (runLinearSchedule transition schedule initial) ≤
          certificate.rate ^ schedule.length *
            quadraticEnergy certificate.metric initial) := by
  constructor
  · exact (pairwiseLinearCommutation_iff_orderIndependence transition).1 hcommute
  · exact fun schedule initial =>
      certificate.runLinearSchedule_energy_le schedule initial

/-! ## Positive fixture for a common certificate -/

/-- A one-dimensional half-contraction. -/
noncomputable def halfScalarTransition (_ : Unit) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => 1 / 2

/-- The identity quadratic form certifies every schedule of half-contractions
with energy rate `1/4`. -/
noncomputable def halfScalarCommonLyapunov :
    CommonQuadraticLyapunov halfScalarTransition where
  metric := fun _ _ => 1
  rate := 1 / 4
  rate_nonneg := by norm_num
  rate_lt_one := by norm_num
  energy_nonneg := by
    intro state
    simp [quadraticEnergy, Matrix.mulVec, dotProduct]
    nlinarith [sq_nonneg (state 0)]
  contracts := by
    intro command state
    simp [quadraticEnergy, halfScalarTransition, Matrix.mulVec, dotProduct]
    ring_nf
    exact le_rfl

theorem halfScalar_allSchedules_positiveExample
    (schedule : List Unit) (initial : Fin 1 → ℝ) :
    quadraticEnergy halfScalarCommonLyapunov.metric
        (runLinearSchedule halfScalarTransition schedule initial) ≤
      (1 / 4 : ℝ) ^ schedule.length *
        quadraticEnergy halfScalarCommonLyapunov.metric initial := by
  exact halfScalarCommonLyapunov.runLinearSchedule_energy_le schedule initial

#print axioms divergentSwitches_individually_extinguish
#print axioms individuallyStable_switchingDiverges
#print axioms CommonQuadraticLyapunov.runLinearSchedule_energy_le
#print axioms CommonQuadraticLyapunov.geometricEnvelope_tendsto_zero
#print axioms commutingCommonQuadraticLyapunov_crown

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
