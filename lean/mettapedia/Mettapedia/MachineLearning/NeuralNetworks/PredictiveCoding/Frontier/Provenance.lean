import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.HybridRefinement
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.ResidualMomentBound
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.PCBPCompute

/-!
# Predictive-coding frontier provenance

This file records which frontier contributions are direct lifts, new checked
content, scope boundaries, or reproduction targets.  Counts are computed from
the records and checked by the kernel.  A contribution is assigned one primary
kind even when it composes several imported facts.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

inductive FrontierRung
  | regimeIndex
  | coordinateRescue
  | trustRegion
  | deepLineRestriction
  | smoothChartTransport
  | residualBoundary
  | residualMomentBound
  | prospectiveInterference
  | hybridRefinement
  | depthScalingRepair
  deriving DecidableEq, Repr

inductive ContributionKind
  | directLift
  | newContent
  | exactRestatement
  | scopeBoundary
  | reproductionTarget
  deriving DecidableEq, Repr

structure FrontierContribution where
  kind : ContributionKind
  description : String
  source : String
  deriving DecidableEq, Repr

/-- Primary contribution manifest for each rung. -/
def frontierContributions : FrontierRung → List FrontierContribution
  | .regimeIndex =>
      [ ⟨.newContent, "complete PCRegime product", "Frontier.Regime"⟩
      , ⟨.newContent, "kernel-checked theorem-to-regime table", "Frontier.Regime"⟩
      , ⟨.directLift, "unit-rate ePC one-step exactness", "ErrorStateReparameterization"⟩
      , ⟨.directLift, "plain-chain slow-mode limit", "DepthPathology"⟩
      , ⟨.directLift, "Depth-muP scalar cancellation", "MuPCDepthCredit"⟩
      , ⟨.directLift, "bounded-bandwidth posterior lower bound", "LocalityCeiling"⟩
      , ⟨.scopeBoundary, "one-step is not equilibrium", "Frontier.Regime"⟩
      , ⟨.scopeBoundary, "plain chain is not residual", "Frontier.Regime"⟩ ]
  | .coordinateRescue =>
      [ ⟨.directLift, "error-after-state inverse", "ErrorStateReparameterization"⟩
      , ⟨.directLift, "state-after-error inverse", "ErrorStateReparameterization"⟩
      , ⟨.directLift, "energy transport", "ErrorStateReparameterization"⟩
      , ⟨.directLift, "local weight-update transport", "ErrorStateReparameterization"⟩
      , ⟨.directLift, "critical-differential equivalence", "ErrorStateReparameterization"⟩
      , ⟨.directLift, "stable-rate wavefront decay", "ErrorStateReparameterization"⟩
      , ⟨.newContent, "shear inverse and energy transport", "Frontier.CoordinateRescue"⟩
      , ⟨.newContent, "shear equilibrium correspondence", "Frontier.CoordinateRescue"⟩
      , ⟨.newContent, "Euclidean-flow non-conjugacy counterexample", "Frontier.CoordinateRescue"⟩
      , ⟨.newContent, "exact JJT-preconditioned flow transport", "Frontier.CoordinateRescue"⟩
      , ⟨.newContent, "state attenuation and error depth invariance", "Frontier.CoordinateRescue"⟩
      , ⟨.scopeBoundary, "coordinate equivalence does not imply Euclidean-flow conjugacy",
          "ePC Appendix C"⟩
      , ⟨.reproductionTarget, "floating-point underflow and implementation speed",
          "ePC experiments"⟩ ]
  | .trustRegion =>
      [ ⟨.directLift, "strict-origin certificate", "EquilibratedEnergySaddles"⟩
      , ⟨.directLift, "unrestricted universal-strictness counterexample",
          "EquilibratedEnergySaddles"⟩
      , ⟨.newContent, "exact one-MLP equilibrium and rescaled loss", "Frontier.TrustRegion"⟩
      , ⟨.newContent, "Equation-7 inverse-Fisher identity in the quadratic model",
          "Frontier.TrustRegion"⟩
      , ⟨.newContent, "exact A.3 two-eigendirection curvature comparison",
          "Frontier.TrustRegion"⟩
      , ⟨.newContent, "exact A.4 positive-eigenvalue flattening", "Frontier.TrustRegion"⟩
      , ⟨.scopeBoundary, "Equation 7 outside the local Taylor model",
          "trust-region paper Equation 5"⟩
      , ⟨.scopeBoundary, "all saddles strict requires additional hypotheses",
          "strict-saddles conjecture"⟩
      , ⟨.scopeBoundary, "two-layer full Hessian and arbitrary-depth line certificates differ",
          "Frontier.DeepLineRestriction"⟩ ]
  | .deepLineRestriction =>
      [ ⟨.newContent, "arbitrary matrix-ray homogeneity and BP degree counting",
          "Frontier.DeepLineRestriction"⟩
      , ⟨.newContent, "exact rank-one latent minimization at arbitrary depth",
          "Frontier.DeepLineRestriction"⟩
      , ⟨.newContent, "strict PC versus second-order-flat BP origin crown",
          "Frontier.DeepLineRestriction"⟩
      , ⟨.newContent, "proof-bearing discharge of the deep-origin boundary",
          "Frontier.DeepLineRestriction"⟩ ]
  | .smoothChartTransport =>
      [ ⟨.directLift, "non-orthogonal shear non-conjugacy witness",
          "Frontier.CoordinateRescue"⟩
      , ⟨.newContent, "general adjoint-Jacobian gradient transport",
          "Frontier.PreconditionedFlowTransport"⟩
      , ⟨.newContent, "raw-flow conjugacy iff JJT is identity",
          "Frontier.PreconditionedFlowTransport"⟩
      , ⟨.newContent, "critical-point correspondence under invertible charts",
          "Frontier.PreconditionedFlowTransport"⟩
      , ⟨.newContent, "Hessian negative-index invariance",
          "Frontier.PreconditionedFlowTransport"⟩ ]
  | .residualBoundary =>
      [ ⟨.directLift, "plain Depth-muP block cancellation", "MuPCDepthCredit"⟩
      , ⟨.directLift, "inverse-depth exponential bound", "Mathlib real exponential"⟩
      , ⟨.newContent, "plain versus residual recurrence", "Frontier.ResidualBoundary"⟩
      , ⟨.newContent, "residual cancellation failure", "Frontier.ResidualBoundary"⟩
      , ⟨.newContent, "unbounded aligned residual stack", "Frontier.ResidualBoundary"⟩
      , ⟨.scopeBoundary, "scalar products do not imply noncommutative matrix bounds",
          "Frontier.ResidualMomentBound"⟩
      , ⟨.reproductionTarget, "matrix infinite-width residual cancellation",
          "muPC residual experiments"⟩ ]
  | .residualMomentBound =>
      [ ⟨.directLift, "aligned square-root residual blowup",
          "Frontier.ResidualBoundary"⟩
      , ⟨.directLift, "inverse-depth exponential upper bound",
          "Frontier.ResidualBoundary"⟩
      , ⟨.newContent, "centered factor first and second moments",
          "Frontier.ResidualMomentBound"⟩
      , ⟨.newContent, "independent finite-product integral factorization",
          "Frontier.ResidualMomentBound"⟩
      , ⟨.newContent, "uniform exp-sigma-squared second-moment crown",
          "Frontier.ResidualMomentBound"⟩
      , ⟨.reproductionTarget, "matrix-valued random residual products",
          "Frontier.ResidualMomentBound"⟩ ]
  | .prospectiveInterference =>
      [ ⟨.directLift, "zero interference energy iff commutation", "InterferenceGram"⟩
      , ⟨.directLift, "metric plus connection decomposition", "MetricDictionary"⟩
      , ⟨.newContent, "strict ordinary-repair loss and advantage iff",
          "Frontier.ProspectiveInterference"⟩
      , ⟨.newContent, "prospective fix-and-preserve repair", "Frontier.ProspectiveInterference"⟩
      , ⟨.newContent, "half-target positive fixture", "Frontier.ProspectiveInterference"⟩
      , ⟨.newContent, "metric-not-connection classification crown",
          "Frontier.ProspectiveInterference"⟩
      , ⟨.scopeBoundary, "scalar shared-hidden model only", "Frontier.ProspectiveInterference"⟩
      , ⟨.reproductionTarget, "broader benchmark and biological claims", "Nature Figure 1"⟩ ]
  | .hybridRefinement =>
      [ ⟨.directLift, "exact depth-two PC energy expansion", "BacktrackingDescent"⟩
      , ⟨.directLift, "ranked acceptance equals checker acceptance", "TypedRegisters"⟩
      , ⟨.newContent, "safe fractional refinement", "Frontier.HybridRefinement"⟩
      , ⟨.newContent, "finite iterates never worsen energy", "Frontier.HybridRefinement"⟩
      , ⟨.newContent, "exact geometric error contraction", "Frontier.HybridRefinement"⟩
      , ⟨.newContent, "checker-derived constraint and authority crown",
          "Frontier.HybridRefinement"⟩
      , ⟨.scopeBoundary, "safe fraction two need not contract strictly",
          "Frontier.HybridRefinement"⟩ ]
  | .depthScalingRepair =>
      [ ⟨.directLift, "state-coordinate first-arrival wavefront",
          "ErrorStateReparameterization"⟩
      , ⟨.directLift, "arbitrary nonlinear finite-speed lower bound",
          "LocalityCeiling"⟩
      , ⟨.directLift, "plain versus residual depth recurrence",
          "Frontier.ResidualBoundary"⟩
      , ⟨.directLift, "full-matrix Gaussian precision substrate",
          "MatrixGaussianChain"⟩
      , ⟨.newContent, "arbitrary-depth scalar Gaussian chain energy",
          "Frontier.DepthScalingRepair"⟩
      , ⟨.newContent, "finite-increment activity and weight gradients",
          "Frontier.DepthScalingRepair"⟩
      , ⟨.newContent, "geometric first-arrival energy imbalance",
          "Frontier.DepthScalingRepair"⟩
      , ⟨.newContent, "spiking-covariance equalization and passive fixtures",
          "Frontier.DepthScalingRepair"⟩
      , ⟨.newContent, "forward-reference accumulated-drift partition",
          "Frontier.DepthScalingRepair"⟩
      , ⟨.newContent, "residual timing and auxiliary-buffer synchronization",
          "Frontier.DepthScalingRepair"⟩
      , ⟨.newContent, "frozen versus live batch-statistic fixed points",
          "Frontier.DepthScalingRepair"⟩
      , ⟨.newContent, "integrated depth-repair certificate",
          "Frontier.DepthScalingRepair"⟩
      , ⟨.newContent, "executable precision/covariance equality and mechanism fixtures",
          "Frontier.DepthScalingImplementation"⟩
      , ⟨.newContent, "implementation-correspondence certificate",
          "Frontier.DepthScalingImplementation"⟩
      , ⟨.newContent, "full-covariance vector activity finite increments",
          "Frontier.DepthScalingVector"⟩
      , ⟨.newContent, "full-covariance matrix-weight finite increments",
          "Frontier.DepthScalingVector"⟩
      , ⟨.newContent, "nonlinear Jacobian remainder and exact increment",
          "Frontier.DepthScalingVector"⟩
      , ⟨.newContent, "vector precision spike, forward error, and residual timing",
          "Frontier.DepthScalingVector"⟩
      , ⟨.newContent, "equal-compute PC-versus-BP work algebra",
          "Frontier.PCBPCompute"⟩
      , ⟨.newContent, "finite-speed PC work lower bound against one BP pass",
          "Frontier.PCBPCompute"⟩
      , ⟨.exactRestatement, "pinned official executable artifacts",
          "changqi97/DeepPCNs@99472b0; changqi97/pcx@b68e746"⟩
      , ⟨.scopeBoundary, "displayed update signs under error equals activity minus prediction",
          "arXiv:2506.23800v3 Equations 2 and 3"⟩
      , ⟨.scopeBoundary, "matrix and nonlinear local identities do not imply trained-network accuracy",
          "Frontier.DepthScalingVector"⟩
      , ⟨.reproductionTarget, "deep nonlinear network accuracy and energy profiles",
          "arXiv:2506.23800v3 experiments"⟩
      , ⟨.reproductionTarget, "universal repair and passive-schedule comparisons",
          "Frontier.DepthScalingRepair"⟩ ]

def contributionCount (rung : FrontierRung) (kind : ContributionKind) : ℕ :=
  (frontierContributions rung).countP fun contribution => contribution.kind = kind

/-- Exact per-rung counts in the order direct lift, new content, exact
restatement, scope boundary, reproduction target. -/
theorem frontierContributionCounts_exact :
    (contributionCount .regimeIndex .directLift,
      contributionCount .regimeIndex .newContent,
      contributionCount .regimeIndex .exactRestatement,
      contributionCount .regimeIndex .scopeBoundary,
      contributionCount .regimeIndex .reproductionTarget) = (4, 2, 0, 2, 0) ∧
    (contributionCount .coordinateRescue .directLift,
      contributionCount .coordinateRescue .newContent,
      contributionCount .coordinateRescue .exactRestatement,
      contributionCount .coordinateRescue .scopeBoundary,
      contributionCount .coordinateRescue .reproductionTarget) = (6, 5, 0, 1, 1) ∧
    (contributionCount .trustRegion .directLift,
      contributionCount .trustRegion .newContent,
      contributionCount .trustRegion .exactRestatement,
      contributionCount .trustRegion .scopeBoundary,
      contributionCount .trustRegion .reproductionTarget) = (2, 4, 0, 3, 0) ∧
    (contributionCount .deepLineRestriction .directLift,
      contributionCount .deepLineRestriction .newContent,
      contributionCount .deepLineRestriction .exactRestatement,
      contributionCount .deepLineRestriction .scopeBoundary,
      contributionCount .deepLineRestriction .reproductionTarget) = (0, 4, 0, 0, 0) ∧
    (contributionCount .smoothChartTransport .directLift,
      contributionCount .smoothChartTransport .newContent,
      contributionCount .smoothChartTransport .exactRestatement,
      contributionCount .smoothChartTransport .scopeBoundary,
      contributionCount .smoothChartTransport .reproductionTarget) = (1, 4, 0, 0, 0) ∧
    (contributionCount .residualBoundary .directLift,
      contributionCount .residualBoundary .newContent,
      contributionCount .residualBoundary .exactRestatement,
      contributionCount .residualBoundary .scopeBoundary,
      contributionCount .residualBoundary .reproductionTarget) = (2, 3, 0, 1, 1) ∧
    (contributionCount .residualMomentBound .directLift,
      contributionCount .residualMomentBound .newContent,
      contributionCount .residualMomentBound .exactRestatement,
      contributionCount .residualMomentBound .scopeBoundary,
      contributionCount .residualMomentBound .reproductionTarget) = (2, 3, 0, 0, 1) ∧
    (contributionCount .prospectiveInterference .directLift,
      contributionCount .prospectiveInterference .newContent,
      contributionCount .prospectiveInterference .exactRestatement,
      contributionCount .prospectiveInterference .scopeBoundary,
      contributionCount .prospectiveInterference .reproductionTarget) = (2, 4, 0, 1, 1) ∧
    (contributionCount .hybridRefinement .directLift,
      contributionCount .hybridRefinement .newContent,
      contributionCount .hybridRefinement .exactRestatement,
      contributionCount .hybridRefinement .scopeBoundary,
      contributionCount .hybridRefinement .reproductionTarget) = (2, 4, 0, 1, 0) ∧
    (contributionCount .depthScalingRepair .directLift,
      contributionCount .depthScalingRepair .newContent,
      contributionCount .depthScalingRepair .exactRestatement,
      contributionCount .depthScalingRepair .scopeBoundary,
      contributionCount .depthScalingRepair .reproductionTarget) = (4, 16, 1, 2, 2) := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor <;> decide

/-- Every rung has at least one newly checked contribution. -/
theorem everyFrontierRung_has_newContent (rung : FrontierRung) :
    0 < contributionCount rung .newContent := by
  cases rung <;> decide

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
