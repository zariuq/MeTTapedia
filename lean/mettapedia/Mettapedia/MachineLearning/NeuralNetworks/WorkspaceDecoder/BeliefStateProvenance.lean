import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.StateSpaceScan
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.BeliefState
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Selectivity
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.BeliefWorldModel

/-!
# Content accounting for the state-space and belief-state ladder

This ledger separates transported results from genuinely new constructions and
explicit scope boundaries.  Entries count coherent theorem or construction
families rather than individual helper lemmas.  The final theorem checks the
published counts by reduction.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

/-- Rungs in the state-space and belief-state extension. -/
inductive BeliefWorkspaceRung
  | kalman
  | stateSpaceScan
  | beliefState
  | selectivity
  | beliefWorldModel
  deriving DecidableEq, Repr

/-- Whether a contribution is transported, new, or a proved scope boundary. -/
inductive ContributionKind
  | directLift
  | newContent
  | scopeBoundary
  deriving DecidableEq, Repr

/-- One auditable family in the content ledger. -/
structure BeliefWorkspaceContribution where
  kind : ContributionKind
  family : String
  source : String
  deriving Repr

/-- Exhaustive family-level accounting for each rung. -/
def beliefWorkspaceContributions :
    BeliefWorkspaceRung → List BeliefWorkspaceContribution
  | .kalman =>
      [ ⟨.directLift, "scalar update", "LinearGaussianChain"⟩
      , ⟨.directLift, "equilibrium posterior", "LinearGaussianOperator"⟩
      , ⟨.newContent, "workspace Kalman family", "KalmanCorrespondence"⟩
      , ⟨.newContent, "gain risk and unique optimum", "KalmanCorrespondence"⟩
      , ⟨.scopeBoundary, "repeated-observation double counting",
          "KalmanCorrespondence"⟩ ]
  | .stateSpaceScan =>
      [ ⟨.directLift, "fixed-gate workspace step", "Dynamics"⟩
      , ⟨.newContent, "linear state-space cell and LTI instance", "StateSpaceScan"⟩
      , ⟨.newContent, "affine-transition monoid", "StateSpaceScan"⟩
      , ⟨.newContent, "prefix-scan trajectory correctness", "StateSpaceScan"⟩
      , ⟨.newContent, "ordered scalar scan fixture", "StateSpaceScan"⟩
      , ⟨.scopeBoundary, "input order is semantically relevant", "StateSpaceScan"⟩ ]
  | .beliefState =>
      [ ⟨.directLift, "Gaussian fusion", "GaussianFusion"⟩
      , ⟨.directLift, "conditional posterior mean", "LinearGaussianChain"⟩
      , ⟨.directLift, "weighted PLN revision", "GaussianRevisionBridge"⟩
      , ⟨.directLift, "conjugate observation count", "ConjugateEvidenceCore"⟩
      , ⟨.newContent, "precision interpolation algebra", "BeliefState"⟩
      , ⟨.newContent, "mean-precision belief slot", "BeliefState"⟩
      , ⟨.newContent, "five-interface unification crown", "BeliefState"⟩
      , ⟨.scopeBoundary, "zero-precision proposal freezes", "BeliefState"⟩ ]
  | .selectivity =>
      [ ⟨.directLift, "precision-variance gain coordinates", "KalmanCorrespondence"⟩
      , ⟨.newContent, "variance-risk excess square", "Selectivity"⟩
      , ⟨.newContent, "two-regime strict separation", "Selectivity"⟩
      , ⟨.newContent, "concrete two-noise witness", "Selectivity"⟩
      , ⟨.newContent, "regime-conditioned optimum", "Selectivity"⟩
      , ⟨.scopeBoundary, "constant noise has no separation", "Selectivity"⟩ ]
  | .beliefWorldModel =>
      [ ⟨.directLift, "additive query extraction", "PLNWorldModelGeneric"⟩
      , ⟨.directLift, "proof-carrying mask hook", "CertifiedMaskHook"⟩
      , ⟨.newContent, "query-indexed binary belief world", "BeliefWorldModel"⟩
      , ⟨.newContent, "residue belief readout", "BeliefWorldModel"⟩
      , ⟨.newContent, "certified state-mask round trip", "BeliefWorldModel"⟩
      , ⟨.scopeBoundary, "empty slot lacks readout evidence", "BeliefWorldModel"⟩ ]

/-- Number of contribution families of one kind on one rung. -/
def contributionCount (rung : BeliefWorkspaceRung) (kind : ContributionKind) : Nat :=
  ((beliefWorkspaceContributions rung).filter fun entry => entry.kind = kind).length

/-- Machine-checked content counts, ordered as direct lifts, new families, and
scope boundaries for T1 through T5. -/
theorem beliefWorkspaceContributionCounts :
    (contributionCount .kalman .directLift,
      contributionCount .kalman .newContent,
      contributionCount .kalman .scopeBoundary) = (2, 2, 1) ∧
    (contributionCount .stateSpaceScan .directLift,
      contributionCount .stateSpaceScan .newContent,
      contributionCount .stateSpaceScan .scopeBoundary) = (1, 4, 1) ∧
    (contributionCount .beliefState .directLift,
      contributionCount .beliefState .newContent,
      contributionCount .beliefState .scopeBoundary) = (4, 3, 1) ∧
    (contributionCount .selectivity .directLift,
      contributionCount .selectivity .newContent,
      contributionCount .selectivity .scopeBoundary) = (1, 4, 1) ∧
    (contributionCount .beliefWorldModel .directLift,
      contributionCount .beliefWorldModel .newContent,
      contributionCount .beliefWorldModel .scopeBoundary) = (2, 3, 1) := by
  decide

#print axioms beliefWorkspaceContributionCounts

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
