import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.DepthPathology
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.MuPCDepthCredit
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LocalityCeiling

/-!
# Predictive-coding regime index

Predictive-coding claims depend on several independent design choices.  This
file makes those choices explicit and assigns four already-proved frontier
results to their exact regimes.  The assignments contain the Lean proof term,
not merely the name of a paper or theorem.

The index is deliberately descriptive: it does not assert that a result
extends from one regime to another.  Later frontier files use it to keep
one-step, finite-settling, equilibrium, plain-chain, residual, and Depth-μP
claims separate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

open Filter Topology
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-- Network topology covered by a predictive-coding statement. -/
inductive TopologyKind
  | chain
  | residual
  | dag
  | graph
  deriving DecidableEq, Repr

/-- Coordinates in which latent inference is performed. -/
inductive StateCoordinates
  | activity
  | predictionError
  deriving DecidableEq, Repr

/-- How far the inference dynamics are run. -/
inductive InferenceSchedule
  | oneStep
  | finiteSteps
  | equilibrium
  deriving DecidableEq, Repr

/-- Relationship between latent inference and parameter plasticity. -/
inductive PlasticitySchedule
  | simultaneous
  | afterEquilibrium
  | fixedPrediction
  deriving DecidableEq, Repr

/-- Scaling convention for the trainable network. -/
inductive Parameterization
  | standard
  | residual
  | depthMuP
  deriving DecidableEq, Repr

/-- Objective assumptions used by a theorem. -/
inductive ObjectiveAssumption
  | squaredError
  | predictiveCodingEnergy
  | smoothObjective
  deriving DecidableEq, Repr

/-- Precision assumptions used by a theorem. -/
inductive PrecisionAssumption
  | unit
  | positive
  | boundedBandwidth
  deriving DecidableEq, Repr

/-- Activation assumptions used by a theorem. -/
inductive ActivationAssumption
  | linear
  | differentiable
  | unrestricted
  deriving DecidableEq, Repr

/-- Complete scope record for a predictive-coding result. -/
structure PCRegime where
  topology : TopologyKind
  coordinates : StateCoordinates
  inference : InferenceSchedule
  plasticity : PlasticitySchedule
  parameterization : Parameterization
  objective : ObjectiveAssumption
  precision : PrecisionAssumption
  activation : ActivationAssumption
  deriving DecidableEq, Repr

/-- A scope record paired with the actual checked proof of its statement. -/
structure ScopedResult (statement : Prop) where
  regime : PCRegime
  proof : statement

/-! ## Canonical regimes -/

/-- Unit-rate ePC's exact one-step scalar backpropagation regime. -/
def epcOneStepBackpropRegime : PCRegime where
  topology := .chain
  coordinates := .predictionError
  inference := .oneStep
  plasticity := .fixedPrediction
  parameterization := .standard
  objective := .squaredError
  precision := .unit
  activation := .differentiable

/-- Plain-chain Jacobi settling in which the slow mode approaches unit rate. -/
def plainChainSlowModeRegime : PCRegime where
  topology := .chain
  coordinates := .activity
  inference := .finiteSteps
  plasticity := .fixedPrediction
  parameterization := .standard
  objective := .predictiveCodingEnergy
  precision := .unit
  activation := .linear

/-- Depth-μP's exact scalar cancellation, separated from inference depth credit. -/
def depthMuPCancellationRegime : PCRegime where
  topology := .chain
  coordinates := .predictionError
  inference := .oneStep
  plasticity := .fixedPrediction
  parameterization := .depthMuP
  objective := .squaredError
  precision := .unit
  activation := .linear

/-- Nonlinear bounded-bandwidth rules seeking the exact chain posterior. -/
def boundedBandwidthPosteriorRegime : PCRegime where
  topology := .chain
  coordinates := .activity
  inference := .finiteSteps
  plasticity := .fixedPrediction
  parameterization := .standard
  objective := .predictiveCodingEnergy
  precision := .boundedBandwidth
  activation := .unrestricted

/-! ## Checked theorem-to-regime assignments -/

/-- The assignment contains the existing exact one-step theorem itself. -/
def epcOneStepBackpropScoped
    (predictionJacobian lossGradient : ℝ) :
    ScopedResult
      (pcLocalParameterUpdate predictionJacobian
          (epcOneStepError 1 lossGradient) =
        predictionJacobian * lossGradient) where
  regime := epcOneStepBackpropRegime
  proof := epcOneStepParameterUpdate_unitRate_eq_backprop _ _

/-- The assignment contains the existing asymptotic slow-mode theorem. -/
noncomputable def plainChainSlowModeScoped :
    ScopedResult
      (Tendsto (fun n : ℕ => pathRelaxationRate (n + 1)) atTop (nhds 1)) where
  regime := plainChainSlowModeRegime
  proof := pathRelaxationRate_tendsto_one

/-- The assignment contains the exact Depth-μP multiplier cancellation. -/
noncomputable def depthMuPCancellationScoped
    (width depth : ℕ) (hwidth : 0 < width) (hdepth : 0 < depth) :
    ScopedResult
      (depthMuPAdamLearningRateScale width depth *
          depthMuPHiddenMultiplier width depth = 1) where
  regime := depthMuPCancellationRegime
  proof := depthMuPAdamScale_mul_hiddenMultiplier width depth hwidth hdepth

/-- The assignment contains the nonlinear bounded-bandwidth lower bound. -/
noncomputable def boundedBandwidthPosteriorScoped
    (distance w sweeps : ℕ)
    (step : PCState (distance + 1) → PCState (distance + 1))
    (hbandwidth : HasChainBandwidth step w)
    (hsettle₀ :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 0) =
        pcStateOfInterior distance 0 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 0 0))
    (hsettle₁ :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 1) =
        pcStateOfInterior distance 1 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 1 0)) :
    ScopedResult (distance ≤ sweeps * w) where
  regime := boundedBandwidthPosteriorRegime
  proof := bandwidth_rule_exact_unitChainPosterior_requires_reach
    distance w sweeps step hbandwidth hsettle₀ hsettle₁

/-- Stable names used by the machine-readable regime table. -/
inductive FrontierResultTag
  | epcOneStepBackprop
  | plainChainSlowMode
  | depthMuPCancellation
  | boundedBandwidthLowerBound
  deriving DecidableEq, Repr

/-- Kernel-reducible theorem-to-regime table. -/
def frontierRegimeTable : List (FrontierResultTag × PCRegime) :=
  [ (.epcOneStepBackprop, epcOneStepBackpropRegime)
  , (.plainChainSlowMode, plainChainSlowModeRegime)
  , (.depthMuPCancellation, depthMuPCancellationRegime)
  , (.boundedBandwidthLowerBound, boundedBandwidthPosteriorRegime)
  ]

/-- Every indexed theorem occurs exactly once, in the declared order. -/
theorem frontierRegimeTable_tags_exact :
    frontierRegimeTable.map Prod.fst =
      [ .epcOneStepBackprop
      , .plainChainSlowMode
      , .depthMuPCancellation
      , .boundedBandwidthLowerBound
      ] := by
  decide

/-- Positive fixture: the ePC theorem is explicitly one-step. -/
theorem epcOneStepBackpropScoped_is_oneStep
    (predictionJacobian lossGradient : ℝ) :
    (epcOneStepBackpropScoped predictionJacobian lossGradient).regime.inference =
      .oneStep := by
  rfl

/-- Negative boundary: the one-step ePC assignment is not an equilibrium claim. -/
theorem epcOneStepBackpropScoped_not_equilibrium
    (predictionJacobian lossGradient : ℝ) :
    (epcOneStepBackpropScoped predictionJacobian lossGradient).regime.inference ≠
      .equilibrium := by
  simp [epcOneStepBackpropScoped, epcOneStepBackpropRegime]

/-- Negative boundary: the plain-chain slow-mode theorem is not residual. -/
theorem plainChainSlowModeScoped_not_residual :
    plainChainSlowModeScoped.regime.topology ≠ .residual := by
  simp [plainChainSlowModeScoped, plainChainSlowModeRegime]

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
