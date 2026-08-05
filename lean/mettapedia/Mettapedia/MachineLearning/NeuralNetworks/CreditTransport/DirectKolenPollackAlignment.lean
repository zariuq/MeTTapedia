import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Core
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Direct Kolen--Pollack forward/feedback alignment

Casnici et al., *Accelerated Predictive Coding Networks via Direct
Kolen--Pollack Feedback Alignment* (2026), Appendix A.1, Equations
(25)--(30), observe that the last forward matrix and the transpose of its
feedback matrix receive the same innovation and the same decay.  Their
difference therefore contracts by `1 - learningRate` at every update.

This file proves that mechanism for an arbitrary time-varying innovation
sequence in any real normed vector space.  It also identifies the sharp
scalar stability interval `0 < learningRate < 2` and records an asymmetric-
innovation counterexample.  The abstraction treats the feedback object after
transposition, so both objects inhabit the same space.

No theorem below extends the source's last-layer identity through
dimension-mismatched hidden layers, certifies a Moore--Penrose
pseudoinverse approximation, or establishes the empirical performance of
DKP-PC.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

open Filter Topology

variable {Weight : Type*} [NormedAddCommGroup Weight] [NormedSpace ℝ Weight]

/-- Forward weights paired with a shape-matched, transposed feedback object. -/
structure ForwardFeedbackPair (Weight : Type*) where
  forward : Weight
  feedbackTranspose : Weight

namespace ForwardFeedbackPair

/-- Difference whose convergence expresses forward/feedback alignment. -/
def gap (pair : ForwardFeedbackPair Weight) : Weight :=
  pair.forward - pair.feedbackTranspose

/-- One shared-innovation, shared-decay update.  Algebraically this is
`weight - learningRate * (innovation + weight)` on each side. -/
def sharedDecayStep
    (learningRate : ℝ) (innovation : Weight)
    (pair : ForwardFeedbackPair Weight) : ForwardFeedbackPair Weight where
  forward :=
    (1 - learningRate) • pair.forward - learningRate • innovation
  feedbackTranspose :=
    (1 - learningRate) • pair.feedbackTranspose - learningRate • innovation

/-- Time-varying training trajectory under shared innovations. -/
def sharedDecayTrajectory
    (learningRate : ℝ) (innovation : ℕ → Weight)
    (initial : ForwardFeedbackPair Weight) : ℕ → ForwardFeedbackPair Weight
  | 0 => initial
  | step + 1 =>
      sharedDecayStep learningRate (innovation step)
        (sharedDecayTrajectory learningRate innovation initial step)

/-- Source recurrence: the common innovation cancels exactly from the
forward/feedback discrepancy. -/
theorem gap_sharedDecayStep
    (learningRate : ℝ) (innovation : Weight)
    (pair : ForwardFeedbackPair Weight) :
    gap (sharedDecayStep learningRate innovation pair) =
      (1 - learningRate) • gap pair := by
  simp only [gap, sharedDecayStep, smul_sub]
  abel

/-- Exact finite-time formula for every innovation schedule. -/
theorem gap_sharedDecayTrajectory
    (learningRate : ℝ) (innovation : ℕ → Weight)
    (initial : ForwardFeedbackPair Weight) :
    ∀ steps : ℕ,
      gap (sharedDecayTrajectory learningRate innovation initial steps) =
        (1 - learningRate) ^ steps • gap initial := by
  intro steps
  induction steps with
  | zero =>
      simp [sharedDecayTrajectory]
  | succ steps inductionHypothesis =>
      rw [sharedDecayTrajectory, gap_sharedDecayStep, inductionHypothesis,
        pow_succ]
      simp [smul_smul, mul_comm]

/-- The sharp scalar stability condition follows from
`0 < learningRate < 2`. -/
theorem abs_one_sub_learningRate_lt_one
    {learningRate : ℝ}
    (positive : 0 < learningRate) (belowTwo : learningRate < 2) :
    |1 - learningRate| < 1 := by
  rw [abs_lt]
  constructor <;> linarith

/-- Under the stability interval, the exact forward/feedback gap converges to
zero for every time-varying innovation sequence. -/
theorem gap_sharedDecayTrajectory_tendsto_zero
    {learningRate : ℝ}
    (positive : 0 < learningRate) (belowTwo : learningRate < 2)
    (innovation : ℕ → Weight) (initial : ForwardFeedbackPair Weight) :
    Tendsto
      (fun steps =>
        gap (sharedDecayTrajectory learningRate innovation initial steps))
      atTop (𝓝 0) := by
  have powerConverges :
      Tendsto (fun steps : ℕ => (1 - learningRate) ^ steps)
        atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      (abs_one_sub_learningRate_lt_one positive belowTwo)
  have scaledConverges :
      Tendsto
        (fun steps : ℕ =>
          (1 - learningRate) ^ steps • gap initial)
        atTop (𝓝 0) := by
    simpa using powerConverges.smul_const (gap initial)
  simpa only [gap_sharedDecayTrajectory] using scaledConverges

/-- If the forward and feedback objects begin equal, shared updates preserve
their equality at every finite time, without a limiting argument. -/
theorem sharedDecayTrajectory_preserves_exact_alignment
    (learningRate : ℝ) (innovation : ℕ → Weight)
    (initial : ForwardFeedbackPair Weight)
    (aligned : initial.forward = initial.feedbackTranspose) :
    ∀ steps,
      (sharedDecayTrajectory learningRate innovation initial steps).forward =
        (sharedDecayTrajectory learningRate innovation initial steps).feedbackTranspose := by
  intro steps
  have hgap := gap_sharedDecayTrajectory
    learningRate innovation initial steps
  have initialGap : gap initial = 0 := by
    simp [gap, aligned]
  rw [initialGap, smul_zero] at hgap
  exact sub_eq_zero.mp hgap

/-! ## Asymmetric boundary -/

/-- A step with different innovations on the two sides. -/
def asymmetricDecayStep
    (learningRate : ℝ) (forwardInnovation feedbackInnovation : Weight)
    (pair : ForwardFeedbackPair Weight) : ForwardFeedbackPair Weight where
  forward :=
    (1 - learningRate) • pair.forward -
      learningRate • forwardInnovation
  feedbackTranspose :=
    (1 - learningRate) • pair.feedbackTranspose -
      learningRate • feedbackInnovation

/-- Unequal innovations inject an additive forcing term into the alignment
gap; common decay alone is insufficient. -/
theorem gap_asymmetricDecayStep
    (learningRate : ℝ) (forwardInnovation feedbackInnovation : Weight)
    (pair : ForwardFeedbackPair Weight) :
    gap
        (asymmetricDecayStep learningRate forwardInnovation
          feedbackInnovation pair) =
      (1 - learningRate) • gap pair -
        learningRate • (forwardInnovation - feedbackInnovation) := by
  simp only [gap, asymmetricDecayStep, smul_sub]
  abel

/-- Positive finite fixture: at rate one half, an initial scalar gap of eight
shrinks to one after three updates, independently of the innovations. -/
theorem scalar_halfRate_threeSteps_gap_eq_one
    (innovation : ℕ → ℝ) :
    gap
        (sharedDecayTrajectory (1 / 2 : ℝ) innovation
          ⟨8, 0⟩ 3) = 1 := by
  rw [gap_sharedDecayTrajectory]
  norm_num [gap]

/-- Negative fixture: unequal innovations immediately break an initially
exact alignment. -/
theorem scalar_asymmetricInnovation_breaks_alignment :
    gap
        (asymmetricDecayStep (1 / 2 : ℝ) (1 : ℝ) (-1 : ℝ)
          ⟨0, 0⟩) = -1 := by
  norm_num [gap, asymmetricDecayStep]

/-- A rate outside the stability interval can expand the discrepancy in one
step. -/
theorem scalar_rateThree_expands_gap :
    |gap (sharedDecayStep (3 : ℝ) 0 ⟨1, 0⟩)| >
      |gap (⟨1, 0⟩ : ForwardFeedbackPair ℝ)| := by
  norm_num [gap, sharedDecayStep]

#print axioms gap_sharedDecayTrajectory
#print axioms gap_sharedDecayTrajectory_tendsto_zero
#print axioms sharedDecayTrajectory_preserves_exact_alignment
#print axioms gap_asymmetricDecayStep
#print axioms scalar_asymmetricInnovation_breaks_alignment
#print axioms scalar_rateThree_expands_gap

end ForwardFeedbackPair

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
