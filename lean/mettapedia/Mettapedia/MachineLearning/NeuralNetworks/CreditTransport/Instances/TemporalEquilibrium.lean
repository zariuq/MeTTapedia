import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.BroadcastProxy
import Mathlib.Tactic

/-!
# Temporal, equilibrium, and reversible-echo credit

This module places three further credit mechanisms on the common transport
substrate.  Forward eligibility records temporal parameter sensitivity but does
not manufacture the downstream learning signal.  Equilibrium propagation reads
finite differences between declared equilibria.  Reversible echo credit has a
separate dynamical premise: the reverse phase must undo the forward map.

The positive and negative examples are deliberately paired.  Exact eligibility
with the exact terminal signal recovers the independently unrolled derivative;
a stale signal reverses it.  Finite equilibrium nudges are biased even when the
zero-nudge limit is exact.  Orthogonal echo dynamics recover the initial state,
whereas replaying the transpose of a dissipative map does not.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances

/-! ## Forward eligibility and temporal learning signals -/

/-- A two-transition scalar recurrent problem.

`transition` is the recurrent Jacobian, `weight` is the shared parameter, and
the two inputs are the two occurrences of that shared parameter. -/
structure TemporalCreditProblem where
  transition : ℝ
  weight : ℝ
  firstInput : ℝ
  secondInput : ℝ
  target : ℝ

inductive TemporalCreditPhase where
  | initial
  | firstObserved
  | secondObserved
  | signalInjected
  | updateReady
  deriving DecidableEq, Repr

inductive TemporalCreditEvent where
  | observeFirst
  | observeSecond
  | injectTerminalSignal
  | readUpdate
  deriving DecidableEq, Repr

structure TemporalCreditState where
  phase : TemporalCreditPhase
  recurrentState : ℝ
  eligibility : ℝ
  learningSignal : ℝ
  update : ℝ

/-- Independently expanded final recurrent state. -/
def twoStepRecurrentState (problem : TemporalCreditProblem) : ℝ :=
  problem.transition * (problem.weight * problem.firstInput) +
    problem.weight * problem.secondInput

/-- Forward sensitivity of the final state to the tied recurrent weight. -/
def twoStepEligibility (problem : TemporalCreditProblem) : ℝ :=
  problem.transition * problem.firstInput + problem.secondInput

/-- Analytic terminal-loss gradient obtained from the unrolled computation. -/
def twoStepBPTTGradient (problem : TemporalCreditProblem) : ℝ :=
  (twoStepRecurrentState problem - problem.target) * twoStepEligibility problem

def initialTemporalCreditState : TemporalCreditState where
  phase := .initial
  recurrentState := 0
  eligibility := 0
  learningSignal := 0
  update := 0

def temporalCreditEnabled
    (_problem : TemporalCreditProblem) (_weight : ℝ)
    (state : TemporalCreditState) (event : TemporalCreditEvent) : Prop :=
  match state.phase, event with
  | .initial, .observeFirst => True
  | .firstObserved, .observeSecond => True
  | .secondObserved, .injectTerminalSignal => True
  | .signalInjected, .readUpdate => True
  | _, _ => False

def temporalCreditTransition
    (problem : TemporalCreditProblem) (_weight : ℝ)
    (event : TemporalCreditEvent) (state : TemporalCreditState) : TemporalCreditState :=
  match event with
  | .observeFirst =>
      { state with
        phase := .firstObserved
        recurrentState := problem.weight * problem.firstInput
        eligibility := problem.firstInput }
  | .observeSecond =>
      { state with
        phase := .secondObserved
        recurrentState := problem.transition * state.recurrentState +
          problem.weight * problem.secondInput
        eligibility := problem.transition * state.eligibility + problem.secondInput }
  | .injectTerminalSignal =>
      { state with
        phase := .signalInjected
        learningSignal := state.recurrentState - problem.target }
  | .readUpdate =>
      { state with
        phase := .updateReady
        update := state.learningSignal * state.eligibility }

def temporalCreditCost
    (_problem : TemporalCreditProblem) (_weight : ℝ)
    (_state : TemporalCreditState) (event : TemporalCreditEvent) : ResourceVector :=
  match event with
  | .observeFirst | .observeSecond =>
      { scalarWork := 2, criticalPathSpan := 1, localDerivativeCalls := 1 }
  | .injectTerminalSignal => { scalarWork := 1, criticalPathSpan := 1 }
  | .readUpdate => { scalarWork := 1, criticalPathSpan := 1 }

noncomputable def temporalCreditSystem : CreditTransportSystem
    TemporalCreditProblem ℝ TemporalCreditState TemporalCreditEvent ℝ ℝ where
  objective problem _ := (twoStepRecurrentState problem - problem.target) ^ 2 / 2
  initialState _ _ := initialTemporalCreditState
  enabled := temporalCreditEnabled
  transition := temporalCreditTransition
  signal _ _ state := state.learningSignal
  readUpdate _ _ state := state.update
  eventCost := temporalCreditCost
  oracleAudit := { accesses := [.forwardEligibilityTrace] }
  localityAudit := {
    scope := .moduleLocal
    dependsOn := fun earlier later =>
      match earlier, later with
      | .observeFirst, .observeSecond => True
      | .observeFirst, .injectTerminalSignal => True
      | .observeFirst, .readUpdate => True
      | .observeSecond, .injectTerminalSignal => True
      | .observeSecond, .readUpdate => True
      | .injectTerminalSignal, .readUpdate => True
      | _, _ => False }

def temporalCreditSchedule : List TemporalCreditEvent :=
  [.observeFirst, .observeSecond, .injectTerminalSignal, .readUpdate]

theorem temporalCreditSchedule_enabled (problem : TemporalCreditProblem) (parameter : ℝ) :
    temporalCreditSystem.ScheduleEnabled problem parameter temporalCreditSchedule := by
  simp [CreditTransportSystem.ScheduleEnabled,
    CreditTransportSystem.ScheduleEnabledFrom,
    temporalCreditSystem, temporalCreditSchedule, temporalCreditEnabled,
    temporalCreditTransition, initialTemporalCreditState]

/-- The forward eligibility recurrence equals the independently unrolled
parameter sensitivity. -/
theorem temporalCredit_finalEligibility
    (problem : TemporalCreditProblem) (parameter : ℝ) :
    (temporalCreditSystem.run problem parameter temporalCreditSchedule).eligibility =
      twoStepEligibility problem := by
  simp [CreditTransportSystem.run, CreditTransportSystem.runFrom,
    temporalCreditSystem, temporalCreditSchedule, temporalCreditTransition,
    initialTemporalCreditState, twoStepEligibility]

/-- Exact e-prop factorization with the exact terminal learning signal recovers
the independently expanded BPTT gradient. -/
theorem exactTemporalSignal_recovers_BPTT
    (problem : TemporalCreditProblem) (parameter : ℝ) :
    temporalCreditSystem.finalUpdate problem parameter temporalCreditSchedule =
      twoStepBPTTGradient problem := by
  simp [CreditTransportSystem.finalUpdate, CreditTransportSystem.run,
    CreditTransportSystem.runFrom, temporalCreditSystem, temporalCreditSchedule,
    temporalCreditTransition, initialTemporalCreditState, twoStepRecurrentState,
    twoStepEligibility, twoStepBPTTGradient]

/-- A forward eligibility trace does not make a stale or sign-reversed learning
signal correct. -/
theorem staleTemporalSignal_can_reverse_BPTT :
    let problem : TemporalCreditProblem :=
      { transition := 1 / 2, weight := 1, firstInput := 1,
        secondInput := 2, target := 0 }
    0 < twoStepBPTTGradient problem ∧
      (-1) * twoStepEligibility problem < 0 := by
  norm_num [twoStepBPTTGradient, twoStepRecurrentState, twoStepEligibility]

/-! ## Finite-nudge equilibrium credit -/

/-- Equilibrium of the scalar energy
`(state-theta)^2/2 + beta*(state-target)^2/2`. -/
noncomputable def scalarNudgedEquilibrium (theta target beta : ℝ) : ℝ :=
  (theta + beta * target) / (1 + beta)

/-- Parameter partial of the internal energy at a held state. -/
def scalarEnergyParameterPartial (theta state : ℝ) : ℝ := theta - state

/-- One-sided equilibrium-propagation estimator. -/
noncomputable def scalarOneSidedEP (theta target beta : ℝ) : ℝ :=
  (scalarEnergyParameterPartial theta (scalarNudgedEquilibrium theta target beta) -
    scalarEnergyParameterPartial theta (scalarNudgedEquilibrium theta target 0)) / beta

/-- Symmetric positive/negative-nudge estimator. -/
noncomputable def scalarSymmetricEP (theta target beta : ℝ) : ℝ :=
  (scalarEnergyParameterPartial theta (scalarNudgedEquilibrium theta target beta) -
    scalarEnergyParameterPartial theta (scalarNudgedEquilibrium theta target (-beta))) /
      (2 * beta)

/-- The task gradient at the free equilibrium. -/
def scalarEPTaskGradient (theta target : ℝ) : ℝ := theta - target

theorem scalarOneSidedEP_formula
    (theta target beta : ℝ) (beta_ne : beta ≠ 0) (denom_ne : 1 + beta ≠ 0) :
    scalarOneSidedEP theta target beta = (theta - target) / (1 + beta) := by
  unfold scalarOneSidedEP scalarEnergyParameterPartial scalarNudgedEquilibrium
  field_simp [beta_ne, denom_ne]
  ring

theorem scalarSymmetricEP_formula
    (theta target beta : ℝ)
    (beta_ne : beta ≠ 0) (positive_denom_ne : 1 + beta ≠ 0)
    (negative_denom_ne : 1 - beta ≠ 0) :
    scalarSymmetricEP theta target beta = (theta - target) / (1 - beta ^ 2) := by
  have square_denom_ne : 1 - beta ^ 2 ≠ 0 := by
    rw [show 1 - beta ^ 2 = (1 - beta) * (1 + beta) by ring]
    exact mul_ne_zero negative_denom_ne positive_denom_ne
  have negative_nudge_denom_ne : 1 + -beta ≠ 0 := by
    simpa [sub_eq_add_neg] using negative_denom_ne
  unfold scalarSymmetricEP scalarEnergyParameterPartial scalarNudgedEquilibrium
  field_simp [beta_ne, positive_denom_ne, negative_denom_ne,
    negative_nudge_denom_ne, square_denom_ne]
  ring_nf

/-- Finite one-sided nudging is not the task gradient in general. -/
theorem scalarOneSidedEP_finite_bias :
    scalarOneSidedEP 2 0 (1 / 10) = 20 / 11 ∧
      scalarEPTaskGradient 2 0 = 2 ∧
      scalarOneSidedEP 2 0 (1 / 10) ≠ scalarEPTaskGradient 2 0 := by
  norm_num [scalarOneSidedEP, scalarEnergyParameterPartial,
    scalarNudgedEquilibrium, scalarEPTaskGradient]

/-- Symmetric nudging cancels the first-order term but remains biased at a
finite radius on this exact quadratic fixture. -/
theorem scalarSymmetricEP_smaller_nonzero_finite_bias :
    scalarSymmetricEP 2 0 (1 / 10) = 200 / 99 ∧
      |scalarSymmetricEP 2 0 (1 / 10) - scalarEPTaskGradient 2 0| <
        |scalarOneSidedEP 2 0 (1 / 10) - scalarEPTaskGradient 2 0| ∧
      scalarSymmetricEP 2 0 (1 / 10) ≠ scalarEPTaskGradient 2 0 := by
  norm_num [scalarSymmetricEP, scalarOneSidedEP, scalarEnergyParameterPartial,
    scalarNudgedEquilibrium, scalarEPTaskGradient, abs_of_nonneg, abs_of_neg]

def equilibriumResponseOracle : OracleAudit where
  accesses := [.equilibriumResponse, .equilibriumResponse]

theorem equilibriumResponse_requires_two_declared_phases :
    equilibriumResponseOracle.accesses.length = 2 := rfl

/-! ## Finite phase alias classes

Sampling a polynomial response at finitely many equally spaced phases groups
coefficient degrees by their residue modulo the phase count.  The definition
below isolates that algebraic alias class without claiming a complex Fourier
reconstruction theorem.  The no-alias theorem states the exact degree budget;
the paired quartic example shows what fails beyond it. -/

/-- Sum of response coefficients whose degrees are indistinguishable modulo a
finite phase count. -/
noncomputable def phaseAliasCoefficient
    {R : Type*} [Semiring R]
    (sampleCount residue : ℕ) (response : Polynomial R) : R :=
  ∑ degree ∈ response.support.filter (fun degree => degree % sampleCount = residue),
    response.coeff degree

/-- Below the finite phase count, every residue class contains at most its
matching coefficient, so the alias-class readout is exact. -/
theorem phaseAliasCoefficient_eq_coeff_of_natDegree_lt
    {R : Type*} [Semiring R]
    (response : Polynomial R) (sampleCount residue : ℕ)
    (degree_lt : response.natDegree < sampleCount)
    (residue_lt : residue < sampleCount) :
    phaseAliasCoefficient sampleCount residue response = response.coeff residue := by
  have filtered_subset :
      response.support.filter (fun degree => degree % sampleCount = residue) ⊆ {residue} := by
    intro degree degree_mem
    have support_mem := (Finset.mem_filter.mp degree_mem).1
    have residue_eq := (Finset.mem_filter.mp degree_mem).2
    have degree_le : degree ≤ response.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp support_mem)
    have degree_lt_count : degree < sampleCount := lt_of_le_of_lt degree_le degree_lt
    have degree_mod : degree % sampleCount = degree := Nat.mod_eq_of_lt degree_lt_count
    exact Finset.mem_singleton.mpr (by simpa [degree_mod] using residue_eq)
  by_cases residue_mem : residue ∈ response.support
  · have residue_filtered :
        residue ∈ response.support.filter (fun degree => degree % sampleCount = residue) :=
      Finset.mem_filter.mpr ⟨residue_mem, Nat.mod_eq_of_lt residue_lt⟩
    have filtered_eq :
        response.support.filter (fun degree => degree % sampleCount = residue) = {residue} := by
      apply Finset.Subset.antisymm filtered_subset
      simpa using residue_filtered
    simp [phaseAliasCoefficient, filtered_eq]
  · have filtered_eq :
        response.support.filter (fun degree => degree % sampleCount = residue) = ∅ := by
      ext degree
      constructor
      · intro degree_mem
        have degree_support := (Finset.mem_filter.mp degree_mem).1
        have degree_mod := (Finset.mem_filter.mp degree_mem).2
        have degree_filtered :
            degree ∈ response.support.filter (fun index => index % sampleCount = residue) :=
          Finset.mem_filter.mpr ⟨degree_support, degree_mod⟩
        have degree_eq : degree = residue :=
          Finset.mem_singleton.mp (filtered_subset degree_filtered)
        exact (residue_mem (degree_eq ▸ degree_support)).elim
      · intro degree_empty
        simp at degree_empty
    have coefficient_zero : response.coeff residue = 0 := by
      by_contra coefficient_ne
      exact residue_mem (Polynomial.mem_support_iff.mpr coefficient_ne)
    simp [phaseAliasCoefficient, filtered_eq, coefficient_zero]

noncomputable def quadraticPhaseResponse : Polynomial ℝ :=
  Polynomial.C 7 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5 * Polynomial.X ^ 2

noncomputable def aliasedQuarticPhaseResponse : Polynomial ℝ :=
  Polynomial.C 3 * Polynomial.X + Polynomial.C 11 * Polynomial.X ^ 4

/-- Three phase classes recover the linear coefficient of a quadratic
response exactly. -/
theorem three_phase_quadratic_recovers_linear_coefficient :
    phaseAliasCoefficient 3 1 quadraticPhaseResponse = 3 := by
  rw [phaseAliasCoefficient_eq_coeff_of_natDegree_lt quadraticPhaseResponse 3 1]
  · norm_num [quadraticPhaseResponse]
  · unfold quadraticPhaseResponse
    compute_degree
    all_goals norm_num
  · norm_num

/-- At three phases, degrees one and four occupy the same alias class while
carrying distinct nonzero coefficients.  This executable witness makes the
strict degree budget in the recovery theorem substantive. -/
theorem three_phase_quartic_aliases_degrees_one_and_four :
    1 ∈ aliasedQuarticPhaseResponse.support.filter (fun degree => degree % 3 = 1) ∧
      4 ∈ aliasedQuarticPhaseResponse.support.filter (fun degree => degree % 3 = 1) ∧
      aliasedQuarticPhaseResponse.coeff 1 = 3 ∧
      aliasedQuarticPhaseResponse.coeff 4 = 11 := by
  norm_num [aliasedQuarticPhaseResponse, Polynomial.mem_support_iff]

/-! ## Reversible and dissipative echo dynamics -/

namespace FeedbackMap2

def transpose (matrix : FeedbackMap2) : FeedbackMap2 :=
  { row00 := matrix.row00, row01 := matrix.row10,
    row10 := matrix.row01, row11 := matrix.row11 }

def compose (left right : FeedbackMap2) : FeedbackMap2 :=
  { row00 := left.row00 * right.row00 + left.row01 * right.row10
    row01 := left.row00 * right.row01 + left.row01 * right.row11
    row10 := left.row10 * right.row00 + left.row11 * right.row10
    row11 := left.row10 * right.row01 + left.row11 * right.row11 }

theorem compose_apply (left right : FeedbackMap2) (state : CreditVec2) :
    (left.compose right).apply state = left.apply (right.apply state) := by
  ext <;> simp [compose, apply] <;> ring

noncomputable def rationalRotation : FeedbackMap2 :=
  { row00 := 3 / 5, row01 := -4 / 5, row10 := 4 / 5, row11 := 3 / 5 }

noncomputable def dissipativeHalf : FeedbackMap2 :=
  { row00 := 1 / 2, row01 := 0, row10 := 0, row11 := 1 / 2 }

/-- The transpose is the exact inverse for the rational orthogonal rotation. -/
theorem rationalRotation_transpose_echo (state : CreditVec2) :
    rationalRotation.transpose.apply (rationalRotation.apply state) = state := by
  ext <;> norm_num [transpose, rationalRotation, apply] <;> ring

/-- Replaying the transpose of a dissipative map compounds contraction rather
than reversing time. -/
theorem dissipative_transpose_echo_is_quarter :
    let state : CreditVec2 := ⟨2, -1⟩
    dissipativeHalf.transpose.apply (dissipativeHalf.apply state) =
      (⟨1 / 2, -1 / 4⟩ : CreditVec2) ∧
    dissipativeHalf.transpose.apply (dissipativeHalf.apply state) ≠ state := by
  norm_num [transpose, dissipativeHalf, apply]

end FeedbackMap2

def reversibleEchoOracle : OracleAudit where
  accesses := [.reversibleTrajectoryEcho]

#print axioms temporalCredit_finalEligibility
#print axioms exactTemporalSignal_recovers_BPTT
#print axioms staleTemporalSignal_can_reverse_BPTT
#print axioms scalarOneSidedEP_formula
#print axioms scalarSymmetricEP_formula
#print axioms scalarOneSidedEP_finite_bias
#print axioms scalarSymmetricEP_smaller_nonzero_finite_bias
#print axioms phaseAliasCoefficient_eq_coeff_of_natDegree_lt
#print axioms three_phase_quadratic_recovers_linear_coefficient
#print axioms three_phase_quartic_aliases_degrees_one_and_four
#print axioms FeedbackMap2.rationalRotation_transpose_echo
#print axioms FeedbackMap2.dissipative_transpose_echo_is_quarter

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances
