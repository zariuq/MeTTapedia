import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.NaturalEvidenceCoordinates
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.SelectiveBeliefContract
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Predictions

/-!
# Content accounting for sequential and weighted-evidence belief decoding

This family-level ledger distinguishes direct theorem transport, new adapter or
algebra families, and proved scope boundaries for the four extension rungs.
The final theorem computes every published count in the kernel.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

/-- Rungs of the sequential, matrix, decoder-contract, and natural-coordinate
extension. -/
inductive SelectiveBeliefRung
  | sequentialScalar
  | matrixGaussian
  | decoderContract
  | naturalCoordinates
  deriving DecidableEq, Repr

/-- Provenance class for one contribution family. -/
inductive SelectiveBeliefContributionKind
  | directLift
  | newContent
  | scopeBoundary
  deriving DecidableEq, Repr

/-- One family in the extension ledger. -/
structure SelectiveBeliefContribution where
  kind : SelectiveBeliefContributionKind
  family : String
  source : String
  deriving Repr

/-- Exhaustive family-level contribution ledger for the four extension rungs. -/
def selectiveBeliefContributions :
    SelectiveBeliefRung → List SelectiveBeliefContribution
  | .sequentialScalar =>
      [ ⟨.directLift, "one-step Kalman gain risk", "KalmanCorrespondence"⟩
      , ⟨.newContent, "Riccati covariance and gain traces", "SequentialSelectivity"⟩
      , ⟨.newContent, "propagated-prior schedule regret", "SequentialSelectivity"⟩
      , ⟨.newContent, "genuine schedule dynamic optimality",
          "SequentialSelectivity"⟩
      , ⟨.newContent, "sharp prefix and full-tail strict separation",
          "SequentialSelectivity"⟩
      , ⟨.scopeBoundary, "fixed-trace diagnostic is not competitor propagation",
          "SequentialSelectivity"⟩ ]
  | .matrixGaussian =>
      [ ⟨.directLift, "operator posterior and equilibrium",
          "LinearGaussianOperator"⟩
      , ⟨.newContent, "Gaussian information commutative monoid", "MatrixBelief"⟩
      , ⟨.newContent, "matrix-gain moment chart", "MatrixBelief"⟩
      , ⟨.newContent, "matrix Riccati covariance chart", "MatrixBelief"⟩
      , ⟨.scopeBoundary, "zero information is not proper", "MatrixBelief"⟩ ]
  | .decoderContract =>
      [ ⟨.directLift, "legal-action soundness and recall", "TypedRegisters"⟩
      , ⟨.directLift, "exact-gain equilibrium posterior", "MatrixBelief"⟩
      , ⟨.newContent, "weighted-evidence selective decoder",
          "SelectiveBeliefContract"⟩
      , ⟨.newContent, "input-conditioned sequential motivation",
          "SelectiveBeliefContract"⟩
      , ⟨.newContent, "three-lineage weighted-evidence probe schema", "Predictions"⟩
      , ⟨.scopeBoundary, "trained nonlinear trajectory remains empirical",
          "Predictions"⟩ ]
  | .naturalCoordinates =>
      [ ⟨.directLift, "natural-number evidence monoid", "BinEvNat"⟩
      , ⟨.directLift, "reconstructive PLN confidence chart",
          "ConfidenceCoordinates"⟩
      , ⟨.directLift, "Gaussian information addition", "MatrixBelief"⟩
      , ⟨.newContent, "computed strength-confidence chart",
          "NaturalEvidenceCoordinates"⟩
      , ⟨.newContent, "confidence monotonicity under finite revision",
          "NaturalEvidenceCoordinates"⟩
      , ⟨.newContent, "discrete-continuous additive fusion crown",
          "NaturalEvidenceCoordinates"⟩
      , ⟨.scopeBoundary, "zero-total chart is not reconstructive",
          "NaturalEvidenceCoordinates"⟩ ]

/-- Count one contribution kind on one rung. -/
def selectiveBeliefContributionCount
    (rung : SelectiveBeliefRung) (kind : SelectiveBeliefContributionKind) : Nat :=
  ((selectiveBeliefContributions rung).filter fun entry => entry.kind = kind).length

/-- Machine-checked counts, ordered as direct lifts, new content, and scope
boundaries for the four extension rungs. -/
theorem selectiveBeliefContributionCounts :
    (selectiveBeliefContributionCount .sequentialScalar .directLift,
      selectiveBeliefContributionCount .sequentialScalar .newContent,
      selectiveBeliefContributionCount .sequentialScalar .scopeBoundary) =
        (1, 4, 1) ∧
    (selectiveBeliefContributionCount .matrixGaussian .directLift,
      selectiveBeliefContributionCount .matrixGaussian .newContent,
      selectiveBeliefContributionCount .matrixGaussian .scopeBoundary) =
        (1, 3, 1) ∧
    (selectiveBeliefContributionCount .decoderContract .directLift,
      selectiveBeliefContributionCount .decoderContract .newContent,
      selectiveBeliefContributionCount .decoderContract .scopeBoundary) =
        (2, 3, 1) ∧
    (selectiveBeliefContributionCount .naturalCoordinates .directLift,
      selectiveBeliefContributionCount .naturalCoordinates .newContent,
      selectiveBeliefContributionCount .naturalCoordinates .scopeBoundary) =
        (3, 3, 1) := by
  decide

#print axioms selectiveBeliefContributionCounts

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
