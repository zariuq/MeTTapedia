import Mathlib.Tactic

/-!
# Agnostic equilibrium propagation: finite Lyapunov structure

Scellier, *Agnostic Physics-Driven Deep Learning* (2022,
arXiv:2205.15021), studies a two-phase physical learning procedure.  A state
first minimizes an energy with nudging `β₁`; after changing the nudging to
`β₂`, it minimizes again.  The paper's Theorems 2--3 show that the secant
Lyapunov function between `β₁` and `β₂` cannot increase, even for finite
nudging and control strength.

This file extracts the order-theoretic core of that result.  It requires no
differentiability:

* selected minimizers of `E + β C` have cost antitone in `β`;
* positive and negative nudging give lower and upper secant bounds on the
  unnudged cost;
* the two equilibrium inequalities make the secant Lyapunov function
  decrease exactly, because the shared control energy cancels.

The first-phase equilibrium is load-bearing.  A finite two-parameter fixture
shows that minimizing only after the nudging change can increase the secant
Lyapunov value.  Positivity of `β₂ - β₁` is also explicit.

These finite inequalities do not formalize the source's differentiable
envelope theorem, Taylor expansions, implicit-function hypotheses, or
Riemannian-gradient asymptotics.

Source artifact SHA-256:
`b47d6791f5ba63ae17b56830a9261ef2fbe66cd7c99951fa4aa2638873eb0e85`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace AgnosticEquilibriumLyapunov

noncomputable section

variable {State Parameter : Type*}

/-- State energy after adding a scalar nudging coefficient times the cost. -/
def nudgedEnergy
    (energy cost : State → ℝ) (beta : ℝ) (state : State) : ℝ :=
  energy state + beta * cost state

/-- The selected state globally minimizes the nudged energy. -/
def IsNudgedMinimizer
    (energy cost : State → ℝ) (beta : ℝ) (selected : State) : Prop :=
  ∀ candidate,
    nudgedEnergy energy cost beta selected ≤
      nudgedEnergy energy cost beta candidate

/-- At two distinct nudging values, their respective minimizers order the
selected costs in the opposite direction.  This is the finite inequality at
the heart of the source's Lemma 10. -/
theorem cost_le_of_nudgedMinimizers
    (energy cost : State → ℝ)
    (firstBeta secondBeta : ℝ)
    (firstState secondState : State)
    (hbeta : firstBeta < secondBeta)
    (hfirst :
      IsNudgedMinimizer energy cost firstBeta firstState)
    (hsecond :
      IsNudgedMinimizer energy cost secondBeta secondState) :
    cost secondState ≤ cost firstState := by
  have hfirstAtSecond := hfirst secondState
  have hsecondAtFirst := hsecond firstState
  simp only [nudgedEnergy] at hfirstAtSecond hsecondAtFirst
  nlinarith

/-- A consistently selected nudged minimizer has antitone cost. -/
theorem selectedCost_antitone
    (energy cost : State → ℝ)
    (selected : ℝ → State)
    (hselected :
      ∀ beta, IsNudgedMinimizer energy cost beta (selected beta)) :
    Antitone (fun beta => cost (selected beta)) := by
  intro firstBeta secondBeta hbeta
  rcases hbeta.eq_or_lt with hEq | hlt
  · subst secondBeta
    exact le_rfl
  · exact
      cost_le_of_nudgedMinimizers
        energy cost firstBeta secondBeta
        (selected firstBeta) (selected secondBeta)
        hlt (hselected firstBeta) (hselected secondBeta)

/-- The selected minimum-energy value at a nudging coefficient. -/
def selectedEnergy
    (energy cost : State → ℝ)
    (selected : ℝ → State)
    (beta : ℝ) : ℝ :=
  nudgedEnergy energy cost beta (selected beta)

/-- Secant slope of the selected minimum-energy curve. -/
def selectedSecant
    (energy cost : State → ℝ)
    (selected : ℝ → State)
    (firstBeta secondBeta : ℝ) : ℝ :=
  (selectedEnergy energy cost selected secondBeta -
      selectedEnergy energy cost selected firstBeta) /
    (secondBeta - firstBeta)

/-- The optimistic, positive-nudging secant lies below the unnudged loss. -/
theorem positiveSecant_le_unnudgedCost
    (energy cost : State → ℝ)
    (selected : ℝ → State)
    (beta : ℝ) (hbeta : 0 < beta)
    (hselected :
      ∀ b, IsNudgedMinimizer energy cost b (selected b)) :
    selectedSecant energy cost selected 0 beta ≤
      cost (selected 0) := by
  have hmin := hselected beta (selected 0)
  simp only [nudgedEnergy] at hmin
  simp only [selectedSecant, selectedEnergy, nudgedEnergy]
  simp only [sub_zero, zero_mul, add_zero]
  apply (div_le_iff₀ hbeta).2
  nlinarith

/-- The pessimistic, negative-nudging secant lies above the unnudged loss. -/
theorem unnudgedCost_le_negativeSecant
    (energy cost : State → ℝ)
    (selected : ℝ → State)
    (beta : ℝ) (hbeta : beta < 0)
    (hselected :
      ∀ b, IsNudgedMinimizer energy cost b (selected b)) :
    cost (selected 0) ≤
      selectedSecant energy cost selected beta 0 := by
  have hmin := hselected beta (selected 0)
  simp only [nudgedEnergy] at hmin
  have hden : 0 < 0 - beta := by linarith
  simp only [selectedSecant, selectedEnergy, nudgedEnergy]
  apply (le_div_iff₀ hden).2
  simp only [zero_mul, add_zero]
  nlinarith

/-! ## The two-phase Lyapunov theorem -/

/-- Secant Lyapunov function of a parameter-dependent free energy. -/
def secantLyapunov
    (freeEnergy : ℝ → Parameter → ℝ)
    (firstBeta secondBeta : ℝ)
    (parameter : Parameter) : ℝ :=
  (freeEnergy secondBeta parameter -
      freeEnergy firstBeta parameter) /
    (secondBeta - firstBeta)

/-- Exact finite two-phase Lyapunov theorem.  The parameter before the update
minimizes the controlled energy at `β₁`, and the parameter after the update
minimizes it at `β₂`.  Adding the two optimality inequalities cancels the
control energy and orders the secant Lyapunov values. -/
theorem secantLyapunov_decreases_of_twoPhaseOptimality
    (control : Parameter → ℝ)
    (freeEnergy : ℝ → Parameter → ℝ)
    (firstBeta secondBeta : ℝ)
    (before after : Parameter)
    (hbeta : firstBeta < secondBeta)
    (hbefore :
      control before + freeEnergy firstBeta before ≤
        control after + freeEnergy firstBeta after)
    (hafter :
      control after + freeEnergy secondBeta after ≤
        control before + freeEnergy secondBeta before) :
    secantLyapunov freeEnergy firstBeta secondBeta after ≤
      secantLyapunov freeEnergy firstBeta secondBeta before := by
  have hden : 0 < secondBeta - firstBeta := sub_pos.mpr hbeta
  apply (div_le_div_iff_of_pos_right hden).2
  nlinarith

/-- The control energy may be scaled arbitrarily, including by the reciprocal
of a finite coupling strength: only its equality across the two phases is
used. -/
theorem scaledControl_secantLyapunov_decreases
    (control : Parameter → ℝ)
    (freeEnergy : ℝ → Parameter → ℝ)
    (controlScale firstBeta secondBeta : ℝ)
    (before after : Parameter)
    (hbeta : firstBeta < secondBeta)
    (hbefore :
      controlScale * control before + freeEnergy firstBeta before ≤
        controlScale * control after + freeEnergy firstBeta after)
    (hafter :
      controlScale * control after + freeEnergy secondBeta after ≤
        controlScale * control before + freeEnergy secondBeta before) :
    secantLyapunov freeEnergy firstBeta secondBeta after ≤
      secantLyapunov freeEnergy firstBeta secondBeta before := by
  exact
    secantLyapunov_decreases_of_twoPhaseOptimality
      (fun parameter => controlScale * control parameter)
      freeEnergy firstBeta secondBeta before after
      hbeta hbefore hafter

/-! ## Executable positive and negative fixtures -/

inductive TwoParameter
  | before
  | after
  deriving DecidableEq

/-- A two-point free energy whose secant is two before the update and one
after it. -/
def improvingFreeEnergy (beta : ℝ) : TwoParameter → ℝ
  | .before => 2 * beta
  | .after => beta

/-- Both phase-optimality premises hold in the improving fixture. -/
theorem improvingFixture_twoPhaseOptimality :
    (0 + improvingFreeEnergy 0 TwoParameter.before ≤
      0 + improvingFreeEnergy 0 TwoParameter.after) ∧
    (0 + improvingFreeEnergy 1 TwoParameter.after ≤
      0 + improvingFreeEnergy 1 TwoParameter.before) := by
  norm_num [improvingFreeEnergy]

/-- The resulting secant Lyapunov value strictly decreases. -/
theorem improvingFixture_secant_strict :
    secantLyapunov improvingFreeEnergy 0 1 TwoParameter.after <
      secantLyapunov improvingFreeEnergy 0 1 TwoParameter.before := by
  norm_num [secantLyapunov, improvingFreeEnergy]

/-- Control energy for the one-phase-only counterexample. -/
def postOnlyControl : TwoParameter → ℝ
  | .before => 2
  | .after => 0

/-- Free energy in the one-phase-only counterexample. -/
def postOnlyFreeEnergy (beta : ℝ) : TwoParameter → ℝ
  | .before => 0
  | .after => beta

/-- The post-update parameter minimizes the second-phase controlled energy. -/
theorem postOnlyFixture_secondPhaseOptimal :
    postOnlyControl TwoParameter.after +
        postOnlyFreeEnergy 1 TwoParameter.after ≤
      postOnlyControl TwoParameter.before +
        postOnlyFreeEnergy 1 TwoParameter.before := by
  norm_num [postOnlyControl, postOnlyFreeEnergy]

/-- The pre-update parameter does not minimize the first-phase controlled
energy, so homeostatic calibration is absent. -/
theorem postOnlyFixture_firstPhase_not_optimal :
    ¬ (postOnlyControl TwoParameter.before +
          postOnlyFreeEnergy 0 TwoParameter.before ≤
        postOnlyControl TwoParameter.after +
          postOnlyFreeEnergy 0 TwoParameter.after) := by
  norm_num [postOnlyControl, postOnlyFreeEnergy]

/-- Despite exact second-phase minimization, the secant Lyapunov value
increases when the first-phase equilibrium premise is dropped. -/
theorem postOnlyFixture_secant_increases :
    secantLyapunov postOnlyFreeEnergy 0 1 TwoParameter.before <
      secantLyapunov postOnlyFreeEnergy 0 1 TwoParameter.after := by
  norm_num [secantLyapunov, postOnlyFreeEnergy]

/-- A negative denominator reverses an otherwise ordered numerator.  The
strict `β₁ < β₂` premise is therefore structural, not cosmetic. -/
theorem reversedBetaOrder_reverses_secantComparison :
    (1 : ℝ) ≤ 2 ∧
      2 / (-1 : ℝ) < 1 / (-1 : ℝ) := by
  norm_num

end

end AgnosticEquilibriumLyapunov

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
