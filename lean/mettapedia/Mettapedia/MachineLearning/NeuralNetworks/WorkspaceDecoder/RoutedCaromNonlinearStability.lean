import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromStability

/-!
# Routed CAROM: uniform nonlinear switched stability

Individual nonlinear phases may each have attractive behavior without sharing
one schedule-uniform stability certificate.  This file records the sufficient
data explicitly: one invariant region, one nonnegative Lyapunov energy, one
strict contraction rate valid for every command, and one coercivity constant
relating energy to distance from a common center.

The resulting bounds hold for every finite command schedule.  They do not
infer the invariant region or the Lyapunov function from a sampled trajectory,
and they do not assert that a trained router satisfies the certificate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Function Set
open scoped Matrix

namespace RoutedCarom

universe uCommand uState uObservation

variable {Command : Type uCommand} {State : Type uState}
  [NormedAddCommGroup State]

/-- A common regional Lyapunov certificate for a nonlinear switched family.
The energy controls squared norm distance from one common center throughout
the declared invariant region. -/
structure CommonRegionalLyapunov
    (transition : Command → State → State)
    (center : State) (region : Set State) where
  energy : State → ℝ
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  rate_lt_one : rate < 1
  coercivity : ℝ
  coercivity_pos : 0 < coercivity
  center_mem : center ∈ region
  energy_nonneg : ∀ state ∈ region, 0 ≤ energy state
  energy_controls_distance : ∀ state ∈ region,
    coercivity * ‖state - center‖ ^ 2 ≤ energy state
  maps_region : ∀ command state, state ∈ region →
    transition command state ∈ region
  contracts : ∀ command state, state ∈ region →
    energy (transition command state) ≤ rate * energy state

/-- Execute nonlinear command phases in list order. -/
def runNonlinearSchedule (transition : Command → State → State) :
    List Command → State → State
  | [], state => state
  | command :: schedule, state =>
      runNonlinearSchedule transition schedule (transition command state)

/-- Every prefix endpoint stays in the common invariant region. -/
theorem CommonRegionalLyapunov.runNonlinearSchedule_mem
    {transition : Command → State → State} {center : State}
    {region : Set State}
    (certificate : CommonRegionalLyapunov transition center region)
    (schedule : List Command) (initial : State)
    (hinitial : initial ∈ region) :
    runNonlinearSchedule transition schedule initial ∈ region := by
  induction schedule generalizing initial with
  | nil => simpa [runNonlinearSchedule] using hinitial
  | cons command schedule ih =>
      exact ih (transition command initial)
        (certificate.maps_region command initial hinitial)

/-- One geometric energy envelope holds for every finite switching word. -/
theorem CommonRegionalLyapunov.runNonlinearSchedule_energy_le
    {transition : Command → State → State} {center : State}
    {region : Set State}
    (certificate : CommonRegionalLyapunov transition center region)
    (schedule : List Command) (initial : State)
    (hinitial : initial ∈ region) :
    certificate.energy (runNonlinearSchedule transition schedule initial) ≤
      certificate.rate ^ schedule.length * certificate.energy initial := by
  induction schedule generalizing initial with
  | nil => simp [runNonlinearSchedule]
  | cons command schedule ih =>
      have hnext : transition command initial ∈ region :=
        certificate.maps_region command initial hinitial
      calc
        certificate.energy
            (runNonlinearSchedule transition (command :: schedule) initial) =
            certificate.energy
              (runNonlinearSchedule transition schedule
                (transition command initial)) := rfl
        _ ≤ certificate.rate ^ schedule.length *
              certificate.energy (transition command initial) :=
          ih (transition command initial) hnext
        _ ≤ certificate.rate ^ schedule.length *
              (certificate.rate * certificate.energy initial) :=
          mul_le_mul_of_nonneg_left
            (certificate.contracts command initial hinitial)
            (pow_nonneg certificate.rate_nonneg _)
        _ = certificate.rate ^ (command :: schedule).length *
              certificate.energy initial := by
          simp [pow_succ, mul_assoc]

/-- Coercivity converts the common energy envelope into a uniform squared
distance bound from the common center. -/
theorem CommonRegionalLyapunov.runNonlinearSchedule_distance_sq_le
    {transition : Command → State → State} {center : State}
    {region : Set State}
    (certificate : CommonRegionalLyapunov transition center region)
    (schedule : List Command) (initial : State)
    (hinitial : initial ∈ region) :
    certificate.coercivity *
        ‖runNonlinearSchedule transition schedule initial - center‖ ^ 2 ≤
      certificate.rate ^ schedule.length * certificate.energy initial := by
  exact le_trans
    (certificate.energy_controls_distance _
      (certificate.runNonlinearSchedule_mem schedule initial hinitial))
    (certificate.runNonlinearSchedule_energy_le schedule initial hinitial)

/-- A discrete observation is stable inside a strict norm margin around the
common center. -/
def ObservationStableOnOpenBall {Observation : Type uObservation}
    (observe : State → Observation)
    (center : State) (margin : ℝ) : Prop :=
  ∀ state, ‖state - center‖ < margin → observe state = observe center

/-- A strict Lyapunov budget below the observation margin preserves the
center's discrete observation after any finite command schedule. -/
theorem CommonRegionalLyapunov.observation_eq_center_of_energy_lt
    {Observation : Type uObservation}
    {transition : Command → State → State} {center : State}
    {region : Set State}
    (certificate : CommonRegionalLyapunov transition center region)
    (observe : State → Observation) (margin : ℝ)
    (hmargin : 0 ≤ margin)
    (hstable : ObservationStableOnOpenBall observe center margin)
    (schedule : List Command) (initial : State)
    (hinitial : initial ∈ region)
    (hbudget :
      certificate.rate ^ schedule.length * certificate.energy initial <
        certificate.coercivity * margin ^ 2) :
    observe (runNonlinearSchedule transition schedule initial) =
      observe center := by
  have hdistanceSq :=
    certificate.runNonlinearSchedule_distance_sq_le schedule initial hinitial
  have hstrict :
      certificate.coercivity *
          ‖runNonlinearSchedule transition schedule initial - center‖ ^ 2 <
        certificate.coercivity * margin ^ 2 :=
    lt_of_le_of_lt hdistanceSq hbudget
  have hsquares :
      ‖runNonlinearSchedule transition schedule initial - center‖ ^ 2 <
        margin ^ 2 := by
    nlinarith [certificate.coercivity_pos]
  apply hstable
  nlinarith [norm_nonneg
    (runNonlinearSchedule transition schedule initial - center)]

/-! ## A genuinely nonlinear common-certificate fixture -/

/-- One linear and one quadratic command on the unit interval. -/
noncomputable def scalarNonlinearTransition : Bool → ℝ → ℝ
  | false, state => state / 2
  | true, state => state ^ 2 / 4

noncomputable def scalarUnitRegion : Set ℝ := Set.Icc (-1) 1

/-- Squared distance is a common energy for both commands. -/
noncomputable def scalarNonlinearCommonLyapunov :
    CommonRegionalLyapunov scalarNonlinearTransition 0 scalarUnitRegion where
  energy := fun state => state ^ 2
  rate := 1 / 4
  rate_nonneg := by norm_num
  rate_lt_one := by norm_num
  coercivity := 1
  coercivity_pos := by norm_num
  center_mem := by norm_num [scalarUnitRegion]
  energy_nonneg := by
    intro state _
    positivity
  energy_controls_distance := by
    intro state _
    rw [Real.norm_eq_abs, sq_abs]
    norm_num
  maps_region := by
    intro command state hstate
    rcases hstate with ⟨hlower, hupper⟩
    cases command with
    | false =>
        simp only [scalarNonlinearTransition]
        constructor <;> linarith
    | true =>
        simp only [scalarNonlinearTransition]
        constructor
        · nlinarith [sq_nonneg state]
        · have hproduct : 0 ≤ (1 - state) * (1 + state) :=
            mul_nonneg (by linarith) (by linarith)
          nlinarith
  contracts := by
    intro command state hstate
    rcases hstate with ⟨hlower, hupper⟩
    cases command with
    | false =>
        simp only [scalarNonlinearTransition]
        ring_nf
        exact le_rfl
    | true =>
        simp only [scalarNonlinearTransition]
        have hproduct : 0 ≤ (1 - state) * (1 + state) :=
          mul_nonneg (by linarith) (by linarith)
        have hsquare : state ^ 2 ≤ 1 := by nlinarith
        have hquartic : state ^ 4 ≤ state ^ 2 := by
          nlinarith [sq_nonneg state,
            mul_nonneg (sq_nonneg state) (sub_nonneg.mpr hsquare)]
        nlinarith

theorem scalarNonlinear_allSchedules_energy_le
    (schedule : List Bool) (initial : ℝ)
    (hinitial : initial ∈ scalarUnitRegion) :
    (runNonlinearSchedule scalarNonlinearTransition schedule initial) ^ 2 ≤
      (1 / 4 : ℝ) ^ schedule.length * initial ^ 2 := by
  exact scalarNonlinearCommonLyapunov.runNonlinearSchedule_energy_le
    schedule initial hinitial

/-! ## Negative boundary: individual attraction is insufficient -/

/-- The two individually nilpotent linear fixtures, viewed as a nonlinear
switched family. -/
noncomputable def divergentBoolTransition :
    Bool → (Fin 2 → ℝ) → (Fin 2 → ℝ)
  | false, state => divergentSwitchA *ᵥ state
  | true, state => divergentSwitchB *ᵥ state

/-- Repeat the command word `A; B` a declared number of times. -/
def divergentAlternatingSchedule : ℕ → List Bool
  | 0 => []
  | cycles + 1 => false :: true :: divergentAlternatingSchedule cycles

theorem divergentAlternatingSchedule_length (cycles : ℕ) :
    (divergentAlternatingSchedule cycles).length = 2 * cycles := by
  induction cycles with
  | zero => rfl
  | succ cycles ih =>
      simp [divergentAlternatingSchedule, ih]
      omega

/-- The generic nonlinear scheduler reproduces the earlier alternating
matrix trajectory exactly. -/
theorem runDivergentAlternatingSchedule_exact
    (cycles : ℕ) (state : Fin 2 → ℝ) :
    runNonlinearSchedule divergentBoolTransition
        (divergentAlternatingSchedule cycles) state =
      (divergentCycleStep^[cycles]) state := by
  induction cycles generalizing state with
  | zero => simp [divergentAlternatingSchedule, runNonlinearSchedule]
  | succ cycles ih =>
      simp only [divergentAlternatingSchedule, runNonlinearSchedule,
        divergentBoolTransition]
      rw [ih]
      rw [Function.iterate_succ_apply]
      rfl

/-- No globally coercive common strict Lyapunov certificate can cover the
two individually nilpotent switches.  Their alternating word diverges, so
the missing common certificate is a substantive boundary rather than a
technical inconvenience. -/
theorem divergentBoolTransition_no_globalCommonRegionalLyapunov :
    ¬ Nonempty
      (CommonRegionalLyapunov divergentBoolTransition 0 Set.univ) := by
  rintro ⟨certificate⟩
  let initial : Fin 2 → ℝ := ![0, 1]
  let initialEnergy := certificate.energy initial
  let bound := max 1 (initialEnergy / certificate.coercivity + 1)
  obtain ⟨cycles, hcycles⟩ :=
    individuallyStable_switchingDiverges bound
  let schedule := divergentAlternatingSchedule cycles
  let finalState := divergentAlternatingState cycles
  have hrun :
      runNonlinearSchedule divergentBoolTransition schedule initial =
        finalState := by
    dsimp only [schedule, finalState, initial, divergentAlternatingState]
    exact runDivergentAlternatingSchedule_exact cycles ![0, 1]
  have hinitial : initial ∈ (Set.univ : Set (Fin 2 → ℝ)) := Set.mem_univ _
  have hdistance :=
    certificate.runNonlinearSchedule_distance_sq_le schedule initial hinitial
  rw [hrun, sub_zero] at hdistance
  have hratePow : certificate.rate ^ schedule.length ≤ 1 :=
    pow_le_one₀ certificate.rate_nonneg certificate.rate_lt_one.le
  have hinitialEnergy : 0 ≤ initialEnergy :=
    certificate.energy_nonneg initial hinitial
  have hscaledEnergy :
      certificate.rate ^ schedule.length * initialEnergy ≤ initialEnergy :=
    mul_le_of_le_one_left hinitialEnergy hratePow
  have hupper :
      certificate.coercivity * ‖finalState‖ ^ 2 ≤ initialEnergy :=
    le_trans hdistance hscaledEnergy
  have hboundOne : (1 : ℝ) ≤ bound := le_max_left _ _
  have hboundEnergy :
      initialEnergy / certificate.coercivity + 1 ≤ bound :=
    le_max_right _ _
  have hcoordinatePositive : 0 < finalState 1 := by
    exact lt_trans (lt_of_lt_of_le (by norm_num) hboundOne) hcycles
  have hcoordinateNorm : finalState 1 ≤ ‖finalState‖ := by
    calc
      finalState 1 = ‖finalState 1‖ := by
        rw [Real.norm_eq_abs, abs_of_pos hcoordinatePositive]
      _ ≤ ‖finalState‖ := norm_le_pi_norm finalState 1
  have hnormOne : 1 < ‖finalState‖ :=
    lt_of_le_of_lt hboundOne (lt_of_lt_of_le hcycles hcoordinateNorm)
  have henergyDiv :
      initialEnergy / certificate.coercivity < ‖finalState‖ := by
    linarith [hboundEnergy, hcycles, hcoordinateNorm]
  have hcancel :
      certificate.coercivity *
          (initialEnergy / certificate.coercivity) = initialEnergy := by
    field_simp [certificate.coercivity_pos.ne']
  have henergyLtNorm :
      initialEnergy < certificate.coercivity * ‖finalState‖ := by
    rw [← hcancel]
    exact mul_lt_mul_of_pos_left henergyDiv certificate.coercivity_pos
  have hnormLtSq : ‖finalState‖ < ‖finalState‖ ^ 2 := by
    nlinarith [norm_nonneg finalState]
  have hstrict :
      initialEnergy < certificate.coercivity * ‖finalState‖ ^ 2 :=
    lt_trans henergyLtNorm
      (mul_lt_mul_of_pos_left hnormLtSq certificate.coercivity_pos)
  exact (not_lt_of_ge hupper) hstrict

#print axioms CommonRegionalLyapunov.runNonlinearSchedule_mem
#print axioms CommonRegionalLyapunov.runNonlinearSchedule_energy_le
#print axioms CommonRegionalLyapunov.runNonlinearSchedule_distance_sq_le
#print axioms CommonRegionalLyapunov.observation_eq_center_of_energy_lt
#print axioms scalarNonlinear_allSchedules_energy_le
#print axioms runDivergentAlternatingSchedule_exact
#print axioms divergentBoolTransition_no_globalCommonRegionalLyapunov

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
