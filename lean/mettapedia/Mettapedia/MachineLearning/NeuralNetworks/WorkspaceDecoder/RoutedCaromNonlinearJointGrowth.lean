import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromNonlinearStability

/-!
# Routed CAROM: finite-word nonlinear growth certificates

Deidda, Guglielmi, and Tudisco define the nonlinear joint spectral radius by
taking the worst growth over every switching word of a fixed length and then
passing to an asymptotic limsup (arXiv:2507.11314, Equation (2)).  This file
isolates the finite, executable layer of that construction.

A `FiniteWordEnergyBound` covers every command word of one declared length.
Such bounds compose multiplicatively, so a certified block can be repeated
over every schedule whose length is a multiple of the block length.  This is
strictly more expressive than a one-command contraction certificate: a
nilpotent command may expand energy on its first step and extinguish it on its
second.

The results here do not define the cone norm or nonlinear joint spectral
radius, and they do not prove the paper's equivalence between asymptotic
stability and joint spectral radius below one.  Those conclusions additionally
require the paper's cone, subhomogeneity, boundedness, and Thompson-metric
hypotheses.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function Filter
open scoped Matrix Topology

namespace RoutedCarom

universe uCommand uState

variable {Command : Type uCommand} {State : Type uState}

/-- A uniform finite-horizon bound over every switching word of exactly
`depth` commands.  The energy need not arise from a norm, allowing the same
composition theorem to cover quadratic, regional, and learned certificates. -/
def FiniteWordEnergyBound
    (transition : Command → State → State) (energy : State → ℝ)
    (depth : ℕ) (factor : ℝ) : Prop :=
  ∀ schedule initial, schedule.length = depth →
    energy (runNonlinearSchedule transition schedule initial) ≤
      factor * energy initial

/-- Executing concatenated command words agrees with feeding the endpoint of
the first word into the second word. -/
theorem runNonlinearSchedule_append
    (transition : Command → State → State)
    (first second : List Command) (initial : State) :
    runNonlinearSchedule transition (first ++ second) initial =
      runNonlinearSchedule transition second
        (runNonlinearSchedule transition first initial) := by
  induction first generalizing initial with
  | nil => rfl
  | cons command first inductionHypothesis =>
      exact inductionHypothesis (transition command initial)

/-- The empty command word has multiplicative factor one. -/
theorem finiteWordEnergyBound_zero
  (transition : Command → State → State) (energy : State → ℝ) :
    FiniteWordEnergyBound transition energy 0 1 := by
  intro schedule initial scheduleLength
  have schedule_eq_nil : schedule = [] :=
    List.length_eq_zero_iff.mp scheduleLength
  subst schedule
  simp [runNonlinearSchedule]

/-- Finite-word growth factors are submultiplicative under concatenation.
This is the checkable finite-horizon law underlying the supremum over
composition words in the nonlinear-JSR construction. -/
theorem FiniteWordEnergyBound.add
    {transition : Command → State → State} {energy : State → ℝ}
    {firstDepth secondDepth : ℕ} {firstFactor secondFactor : ℝ}
    (firstBound :
      FiniteWordEnergyBound transition energy firstDepth firstFactor)
    (secondBound :
      FiniteWordEnergyBound transition energy secondDepth secondFactor)
    (secondFactor_nonneg : 0 ≤ secondFactor) :
    FiniteWordEnergyBound transition energy
      (firstDepth + secondDepth) (secondFactor * firstFactor) := by
  intro schedule initial scheduleLength
  let first := schedule.take firstDepth
  let second := schedule.drop firstDepth
  have firstDepth_le : firstDepth ≤ schedule.length := by
    omega
  have firstLength : first.length = firstDepth := by
    simp [first, List.length_take, firstDepth_le]
  have secondLength : second.length = secondDepth := by
    simp [second, List.length_drop, scheduleLength]
  have split : first ++ second = schedule := by
    exact List.take_append_drop firstDepth schedule
  rw [← split, runNonlinearSchedule_append]
  calc
    energy
        (runNonlinearSchedule transition second
          (runNonlinearSchedule transition first initial)) ≤
        secondFactor *
          energy (runNonlinearSchedule transition first initial) :=
      secondBound second (runNonlinearSchedule transition first initial)
        secondLength
    _ ≤ secondFactor * (firstFactor * energy initial) :=
      mul_le_mul_of_nonneg_left
        (firstBound first initial firstLength) secondFactor_nonneg
    _ = (secondFactor * firstFactor) * energy initial := by ring

/-- A bound for every word of one block length repeats over every word made of
that many complete blocks.  The schedule itself remains arbitrary; it is not
assumed to repeat one selected command pattern. -/
theorem FiniteWordEnergyBound.repeat
    {transition : Command → State → State} {energy : State → ℝ}
    {blockDepth : ℕ} {blockFactor : ℝ}
    (blockBound :
      FiniteWordEnergyBound transition energy blockDepth blockFactor)
    (blockFactor_nonneg : 0 ≤ blockFactor)
    (blocks : ℕ) :
    FiniteWordEnergyBound transition energy
      (blockDepth * blocks) (blockFactor ^ blocks) := by
  induction blocks with
  | zero =>
      simpa using finiteWordEnergyBound_zero transition energy
  | succ blocks inductionHypothesis =>
      have combined :=
        blockBound.add inductionHypothesis
          (pow_nonneg blockFactor_nonneg blocks)
      simpa [Nat.mul_succ, pow_succ, Nat.add_comm] using combined

/-- A strict block factor gives the geometric envelope used by every
multiple-of-block-depth schedule. -/
theorem FiniteWordEnergyBound.geometricEnvelope_tendsto_zero
    {transition : Command → State → State} {energy : State → ℝ}
    {blockDepth : ℕ} {blockFactor : ℝ}
    (blockBound :
      FiniteWordEnergyBound transition energy blockDepth blockFactor)
    (blockFactor_nonneg : 0 ≤ blockFactor)
    (blockFactor_lt_one : blockFactor < 1)
    (initial : State) :
    (∀ blocks, FiniteWordEnergyBound transition energy
      (blockDepth * blocks) (blockFactor ^ blocks)) ∧
      Tendsto (fun blocks : ℕ => blockFactor ^ blocks * energy initial)
        atTop (𝓝 0) := by
  constructor
  · exact fun blocks => blockBound.repeat blockFactor_nonneg blocks
  · simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        blockFactor_nonneg blockFactor_lt_one).mul_const (energy initial)

/-! ## Positive boundary: block contraction without one-step contraction -/

/-- One nilpotent command, inherited from the switched-stability fixture. -/
noncomputable def expandingThenExtinguishingTransition
    (_ : Unit) (state : Fin 2 → ℝ) : Fin 2 → ℝ :=
  divergentSwitchA *ᵥ state

/-- Standard squared Euclidean energy, expressed through the existing
quadratic-energy interface. -/
noncomputable def standardSquaredEnergy (state : Fin 2 → ℝ) : ℝ :=
  quadraticEnergy (1 : Matrix (Fin 2) (Fin 2) ℝ) state

/-- Every two-command word extinguishes the state, so its block factor is
zero even though the first command can expand energy. -/
theorem expandingThenExtinguishing_twoStepBound :
    FiniteWordEnergyBound expandingThenExtinguishingTransition
      standardSquaredEnergy 2 0 := by
  intro schedule initial scheduleLength
  cases schedule with
  | nil => simp at scheduleLength
  | cons first rest =>
      cases rest with
      | nil => simp at scheduleLength
      | cons second rest =>
          cases rest with
          | nil =>
              cases first
              cases second
              simp only [runNonlinearSchedule,
                expandingThenExtinguishingTransition]
              rw [Matrix.mulVec_mulVec, divergentSwitchA_square_zero]
              simp [standardSquaredEnergy, quadraticEnergy]
          | cons third rest =>
              simp at scheduleLength

/-- The same command has no strict one-step energy contraction factor: on the
second basis vector it expands squared energy from one to four. -/
theorem expandingThenExtinguishing_no_strictOneStepBound :
    ¬ ∃ factor : ℝ, factor < 1 ∧
      FiniteWordEnergyBound expandingThenExtinguishingTransition
        standardSquaredEnergy 1 factor := by
  rintro ⟨factor, factor_lt_one, bound⟩
  have expanded :=
    bound [()] ![0, 1] (by simp)
  norm_num [runNonlinearSchedule, expandingThenExtinguishingTransition,
    standardSquaredEnergy, quadraticEnergy, divergentSwitchA,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two] at expanded
  linarith

/-- Consequently, every even-length schedule has the repeated zero-factor
certificate. -/
theorem expandingThenExtinguishing_allEvenWords
    (blocks : ℕ) :
    FiniteWordEnergyBound expandingThenExtinguishingTransition
      standardSquaredEnergy (2 * blocks) (0 ^ blocks) :=
  expandingThenExtinguishing_twoStepBound.repeat (by norm_num) blocks

/-! ## Negative boundary: individual repetitions do not control switching -/

/-- Each constituent command of the divergent switched family extinguishes
under self-repetition. -/
theorem divergentBoolTransition_repetitions_extinguish
    (state : Fin 2 → ℝ) :
    divergentBoolTransition false
        (divergentBoolTransition false state) = 0 ∧
      divergentBoolTransition true
        (divergentBoolTransition true state) = 0 := by
  simpa [divergentBoolTransition] using
    divergentSwitches_individually_extinguish state

/-- Despite individual two-step extinction, no strict factor covers every
two-command word: the alternating word expands squared energy by sixteen. -/
theorem divergentBoolTransition_no_strictTwoStepBound :
    ¬ ∃ factor : ℝ, factor < 1 ∧
      FiniteWordEnergyBound divergentBoolTransition
        standardSquaredEnergy 2 factor := by
  rintro ⟨factor, factor_lt_one, bound⟩
  have alternating :=
    bound (divergentAlternatingSchedule 1) ![0, 1] (by
      simp [divergentAlternatingSchedule])
  rw [runDivergentAlternatingSchedule_exact] at alternating
  norm_num [divergentCycleStep, standardSquaredEnergy, quadraticEnergy,
    divergentSwitchA, divergentSwitchB, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at alternating
  linarith

#print axioms runNonlinearSchedule_append
#print axioms FiniteWordEnergyBound.add
#print axioms FiniteWordEnergyBound.repeat
#print axioms FiniteWordEnergyBound.geometricEnvelope_tendsto_zero
#print axioms expandingThenExtinguishing_twoStepBound
#print axioms expandingThenExtinguishing_no_strictOneStepBound
#print axioms divergentBoolTransition_no_strictTwoStepBound

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
