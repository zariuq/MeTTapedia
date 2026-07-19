import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.SelectiveBeliefContract
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Predictions

/-!
# Content accounting for weighted evidence and principled forgetting

This family-level ledger distinguishes direct transport from the existing PLN
and nonstationary-fusion spines, genuinely new weighted-evidence content, and
proved or declared scope boundaries.  The final theorem computes every count
in the kernel.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

/-- Rungs of the weighted-evidence and principled-forgetting extension. -/
inductive WeightedEvidenceRung
  | carrierAndChart
  | decayAction
  | jumpTransport
  | decoderInstrumentation
  deriving DecidableEq, Repr

/-- Provenance class for one weighted-evidence contribution family. -/
inductive WeightedEvidenceContributionKind
  | directLift
  | newContent
  | scopeBoundary
  deriving DecidableEq, Repr

/-- One family in the weighted-evidence extension ledger. -/
structure WeightedEvidenceContribution where
  kind : WeightedEvidenceContributionKind
  family : String
  source : String
  deriving Repr

/-- Exhaustive family-level ledger for the four weighted-evidence rungs. -/
def weightedEvidenceContributions :
    WeightedEvidenceRung → List WeightedEvidenceContribution
  | .carrierAndChart =>
      [ ⟨.directLift, "nonnegative-real binary evidence carrier",
          "BinaryEvidence"⟩
      , ⟨.directLift, "binary evidence fusion monoid", "BinaryEvidence"⟩
      , ⟨.directLift, "canonical strength-confidence chart", "BinaryEvidence"⟩
      , ⟨.newContent, "exact additive natural-count embedding",
          "WeightedEvidence"⟩
      , ⟨.scopeBoundary, "operational trajectories require finite evidence",
          "WeightedEvidence"⟩ ]
  | .decayAction =>
      [ ⟨.directLift, "jump-derived information retention", "NonstationaryFusion"⟩
      , ⟨.newContent, "distributive scalar decay action", "WeightedEvidence"⟩
      , ⟨.newContent, "iterated exponential fading", "WeightedEvidence"⟩
      , ⟨.newContent, "online fade-then-fuse decomposition",
          "WeightedEvidence"⟩
      , ⟨.scopeBoundary, "online fresh evidence differs from batch fading",
          "WeightedEvidence"⟩ ]
  | .jumpTransport =>
      [ ⟨.directLift, "jump predictive precision identity", "NonstationaryFusion"⟩
      , ⟨.directLift, "jump-risk unique minimizer", "NonstationaryFusion"⟩
      , ⟨.newContent, "faded-precision optimal-gain transport",
          "WeightedEvidenceDynamics"⟩
      , ⟨.newContent, "faded estimator optimal-risk transport",
          "WeightedEvidenceDynamics"⟩
      , ⟨.newContent, "effective-evidence confidence replacement",
          "WeightedEvidenceDynamics"⟩
      , ⟨.scopeBoundary, "positive jump refutes monotone confidence",
          "WeightedEvidenceDynamics"⟩
      , ⟨.scopeBoundary, "risk theorem is scalar linear-Gaussian",
          "NonstationaryFusion"⟩ ]
  | .decoderInstrumentation =>
      [ ⟨.directLift, "legal-action soundness and recall", "TypedRegisters"⟩
      , ⟨.newContent, "weighted selective-decoder payload",
          "SelectiveBeliefContract"⟩
      , ⟨.newContent, "registered decay with jump-derived default",
          "SelectiveBeliefContract"⟩
      , ⟨.newContent, "hash-pinned weighted trajectory schema", "Predictions"⟩
      , ⟨.scopeBoundary, "trained nonlinear trajectory remains empirical",
          "Predictions"⟩ ]

/-- Count one contribution kind on one weighted-evidence rung. -/
def weightedEvidenceContributionCount
    (rung : WeightedEvidenceRung)
    (kind : WeightedEvidenceContributionKind) : Nat :=
  ((weightedEvidenceContributions rung).filter fun entry =>
    entry.kind = kind).length

/-- Machine-checked counts, ordered as direct lifts, new content, and scope
boundaries for the four weighted-evidence rungs. -/
theorem weightedEvidenceContributionCounts :
    (weightedEvidenceContributionCount .carrierAndChart .directLift,
      weightedEvidenceContributionCount .carrierAndChart .newContent,
      weightedEvidenceContributionCount .carrierAndChart .scopeBoundary) =
        (3, 1, 1) ∧
    (weightedEvidenceContributionCount .decayAction .directLift,
      weightedEvidenceContributionCount .decayAction .newContent,
      weightedEvidenceContributionCount .decayAction .scopeBoundary) =
        (1, 3, 1) ∧
    (weightedEvidenceContributionCount .jumpTransport .directLift,
      weightedEvidenceContributionCount .jumpTransport .newContent,
      weightedEvidenceContributionCount .jumpTransport .scopeBoundary) =
        (2, 3, 2) ∧
    (weightedEvidenceContributionCount .decoderInstrumentation .directLift,
      weightedEvidenceContributionCount .decoderInstrumentation .newContent,
      weightedEvidenceContributionCount .decoderInstrumentation .scopeBoundary) =
        (1, 3, 1) := by
  decide

#print axioms weightedEvidenceContributionCounts

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
