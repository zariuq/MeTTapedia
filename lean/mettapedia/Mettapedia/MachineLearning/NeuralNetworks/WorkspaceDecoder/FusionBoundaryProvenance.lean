import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FusionExpressivity
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.OverlapCalibration
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.NonstationaryFusion
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.DistortionCalibration

/-!
# Content accounting for the boundary theory of hardwired fusion

This family-level ledger distinguishes direct theorem reuse, new formal
content, and explicit scope boundaries for the four completed rungs.  Counts
are computed by the kernel rather than reported manually.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

/-- Completed rungs of the hardwired-fusion boundary theory. -/
inductive FusionBoundaryRung
  | expressivity
  | overlap
  | nonstationarity
  | distortion
  deriving DecidableEq, Repr

/-- Provenance class for one boundary-theory contribution family. -/
inductive FusionBoundaryContributionKind
  | directLift
  | newContent
  | scopeBoundary
  deriving DecidableEq, Repr

/-- One contribution family and its nearest source. -/
structure FusionBoundaryContribution where
  kind : FusionBoundaryContributionKind
  family : String
  source : String
  deriving Repr

/-- Exhaustive family-level ledger for the four completed rungs. -/
def fusionBoundaryContributions :
    FusionBoundaryRung → List FusionBoundaryContribution
  | .expressivity =>
      [ ⟨.directLift, "precision-addition moment chart", "BeliefState"⟩
      , ⟨.newContent, "precision-valid CAROM gate interval", "FusionExpressivity"⟩
      , ⟨.newContent, "fixed-calibration prior-decay representation",
          "FusionExpressivity"⟩
      , ⟨.newContent, "strict-decay complement characterization",
          "FusionExpressivity"⟩
      , ⟨.newContent, "observation-discount and overwrite partition",
          "FusionExpressivity"⟩
      , ⟨.scopeBoundary, "variable precision differs from fixed calibration",
          "FusionExpressivity"⟩
      , ⟨.scopeBoundary, "scalar linear interpolation only", "FusionExpressivity"⟩ ]
  | .overlap =>
      [ ⟨.directLift, "counts-primal independent revision",
          "NaturalEvidenceCoordinates"⟩
      , ⟨.newContent, "exact precision overstatement law", "OverlapCalibration"⟩
      , ⟨.newContent, "exact variance calibration gap", "OverlapCalibration"⟩
      , ⟨.newContent, "discounted Gaussian revision", "OverlapCalibration"⟩
      , ⟨.newContent, "componentwise count-overlap revision",
          "OverlapCalibration"⟩
      , ⟨.scopeBoundary, "declared scalar overlap is not dependence estimation",
          "OverlapCalibration"⟩ ]
  | .nonstationarity =>
      [ ⟨.directLift, "variance-coordinate Kalman risk", "Selectivity"⟩
      , ⟨.newContent, "monotone-accumulator jump separation",
          "NonstationaryFusion"⟩
      , ⟨.newContent, "derived information decay", "NonstationaryFusion"⟩
      , ⟨.newContent, "derived moment retention", "NonstationaryFusion"⟩
      , ⟨.newContent, "exponential fading closed form", "NonstationaryFusion"⟩
      , ⟨.scopeBoundary, "known scalar independent-jump model",
          "NonstationaryFusion"⟩ ]
  | .distortion =>
      [ ⟨.directLift, "scalar gain risk and minimizer", "KalmanCorrespondence"⟩
      , ⟨.newContent, "distorted-measurement risk adapter",
          "DistortionCalibration"⟩
      , ⟨.newContent, "strict learned-mixing boundary", "DistortionCalibration"⟩
      , ⟨.newContent, "measurement-map recalibration factorization",
          "DistortionCalibration"⟩
      , ⟨.scopeBoundary, "fixed nonzero scalar linear distortion",
          "DistortionCalibration"⟩ ]

/-- Count one contribution kind on one boundary rung. -/
def fusionBoundaryContributionCount
    (rung : FusionBoundaryRung) (kind : FusionBoundaryContributionKind) : Nat :=
  ((fusionBoundaryContributions rung).filter fun entry =>
    entry.kind = kind).length

/-- Machine-checked counts, ordered as direct lifts, new content, and scope
boundaries. -/
theorem fusionBoundaryContributionCounts :
    (fusionBoundaryContributionCount .expressivity .directLift,
      fusionBoundaryContributionCount .expressivity .newContent,
      fusionBoundaryContributionCount .expressivity .scopeBoundary) =
        (1, 4, 2) ∧
    (fusionBoundaryContributionCount .overlap .directLift,
      fusionBoundaryContributionCount .overlap .newContent,
      fusionBoundaryContributionCount .overlap .scopeBoundary) =
        (1, 4, 1) ∧
    (fusionBoundaryContributionCount .nonstationarity .directLift,
      fusionBoundaryContributionCount .nonstationarity .newContent,
      fusionBoundaryContributionCount .nonstationarity .scopeBoundary) =
        (1, 4, 1) ∧
    (fusionBoundaryContributionCount .distortion .directLift,
      fusionBoundaryContributionCount .distortion .newContent,
      fusionBoundaryContributionCount .distortion .scopeBoundary) =
        (1, 3, 1) := by
  decide

#print axioms fusionBoundaryContributionCounts

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
