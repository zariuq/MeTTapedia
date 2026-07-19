import Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry.InterferenceGram

/-!
# Provenance for coupling, curvature, and forgetting geometry

This family-level ledger distinguishes direct transport from the sealed
continual-learning, evidence, predictive-coding, and Mathlib spines;
genuinely new content including refutations; theorem restatements; and scope
boundaries.  Counts are computed by the kernel.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry

/-- Rungs of the forgetting-geometry development. -/
inductive ForgettingGeometryRung
  | metricDictionary
  | rankOneTrichotomy
  | elementaryHolonomy
  | transferRigidity
  | interferenceGram
  deriving DecidableEq, Repr

/-- Provenance class for one contribution family. -/
inductive ForgettingGeometryContributionKind
  | directLift
  | newContent
  | restatement
  | scopeBoundary
  deriving DecidableEq, Repr

/-- One family and its nearest formal source. -/
structure ForgettingGeometryContribution where
  kind : ForgettingGeometryContributionKind
  family : String
  source : String
  deriving Repr

/-- Exhaustive family-level ledger for the five completed rungs. -/
def forgettingGeometryContributions :
    ForgettingGeometryRung → List ForgettingGeometryContribution
  | .metricDictionary =>
      [ ⟨.directLift, "exact overlap precision overstatement",
          "WorkspaceDecoder.OverlapCalibration"⟩
      , ⟨.directLift, "exact sequential quadratic reuse remainder",
          "ContinualLearning.QuadraticTwoTask"⟩
      , ⟨.newContent, "effective multiplicity equivalence",
          "ForgettingGeometry.MetricDictionary"⟩
      , ⟨.newContent, "metric mismatch plus connection remainder",
          "ForgettingGeometry.MetricDictionary"⟩
      , ⟨.scopeBoundary, "declared scalar overlap and quadratic reference",
          "ForgettingGeometry.MetricDictionary"⟩ ]
  | .rankOneTrichotomy =>
      [ ⟨.directLift, "two-task curvature commutator mechanism",
          "ContinualLearning.QuadraticTwoTask"⟩
      , ⟨.newContent, "parametric rank-one normal form",
          "ForgettingGeometry.RankOneTrichotomy"⟩
      , ⟨.newContent, "parallel orthogonal oblique classification",
          "ForgettingGeometry.RankOneTrichotomy"⟩
      , ⟨.restatement, "observational energy blindness conjunction",
          "PredictiveCoding.CausalDirectionIdentifiability"⟩
      , ⟨.scopeBoundary, "order blindness is not causal identifiability",
          "ForgettingGeometry.RankOneTrichotomy"⟩ ]
  | .elementaryHolonomy =>
      [ ⟨.directLift, "symmetric matrix exponential",
          "Mathlib.MatrixExponential"⟩
      , ⟨.directLift, "scalar identity exponential factorization",
          "Mathlib.MatrixExponential"⟩
      , ⟨.newContent, "two-factor symmetry iff commutation",
          "ForgettingGeometry.ElementaryHolonomy"⟩
      , ⟨.newContent, "noncommuting positive-definite palindrome refutation",
          "ForgettingGeometry.ElementaryHolonomy"⟩
      , ⟨.scopeBoundary, "symmetry proxy requires positive polar context",
          "ForgettingGeometry.ElementaryHolonomy"⟩
      , ⟨.scopeBoundary, "arbitrary-curriculum converse is false",
          "ForgettingGeometry.ElementaryHolonomy"⟩ ]
  | .transferRigidity =>
      [ ⟨.directLift, "characteristic polynomial under unit conjugation",
          "Mathlib.Matrix.Charpoly"⟩
      , ⟨.newContent, "commutator covariance under similarity",
          "ForgettingGeometry.TransferRigidity"⟩
      , ⟨.newContent, "nonorthogonal shear refutation",
          "ForgettingGeometry.TransferRigidity"⟩
      , ⟨.newContent, "first-jet Hessian counterexample",
          "ForgettingGeometry.TransferRigidity"⟩
      , ⟨.restatement, "orthogonal symmetry transport",
          "ForgettingGeometry.TransferRigidity"⟩
      , ⟨.scopeBoundary, "Euclidean angles require orthogonality or metric transport",
          "ForgettingGeometry.TransferRigidity"⟩ ]
  | .interferenceGram =>
      [ ⟨.directLift, "Frobenius square zero criterion",
          "Mathlib.Matrix.PosDef"⟩
      , ⟨.newContent, "Gram diagonal detects pairwise conflict graph",
          "ForgettingGeometry.InterferenceGram"⟩
      , ⟨.newContent, "rank-one interference energy closed form",
          "ForgettingGeometry.InterferenceGram"⟩
      , ⟨.newContent, "scalar identity shifts are Gram-invisible",
          "ForgettingGeometry.InterferenceGram"⟩
      , ⟨.restatement, "finite-speed nonlinear locality crown",
          "PredictiveCoding.LocalityCeiling"⟩
      , ⟨.scopeBoundary, "logarithmic localization law remains heuristic",
          "ForgettingGeometry.InterferenceGram"⟩ ]

/-- Count one provenance class on one rung. -/
def forgettingGeometryContributionCount
    (rung : ForgettingGeometryRung)
    (kind : ForgettingGeometryContributionKind) : Nat :=
  ((forgettingGeometryContributions rung).filter fun entry =>
    entry.kind = kind).length

/-- Machine-checked counts, ordered as direct lifts, new content,
restatements, and scope boundaries. -/
theorem forgettingGeometryContributionCounts :
    (forgettingGeometryContributionCount .metricDictionary .directLift,
      forgettingGeometryContributionCount .metricDictionary .newContent,
      forgettingGeometryContributionCount .metricDictionary .restatement,
      forgettingGeometryContributionCount .metricDictionary .scopeBoundary) =
        (2, 2, 0, 1) ∧
    (forgettingGeometryContributionCount .rankOneTrichotomy .directLift,
      forgettingGeometryContributionCount .rankOneTrichotomy .newContent,
      forgettingGeometryContributionCount .rankOneTrichotomy .restatement,
      forgettingGeometryContributionCount .rankOneTrichotomy .scopeBoundary) =
        (1, 2, 1, 1) ∧
    (forgettingGeometryContributionCount .elementaryHolonomy .directLift,
      forgettingGeometryContributionCount .elementaryHolonomy .newContent,
      forgettingGeometryContributionCount .elementaryHolonomy .restatement,
      forgettingGeometryContributionCount .elementaryHolonomy .scopeBoundary) =
        (2, 2, 0, 2) ∧
    (forgettingGeometryContributionCount .transferRigidity .directLift,
      forgettingGeometryContributionCount .transferRigidity .newContent,
      forgettingGeometryContributionCount .transferRigidity .restatement,
      forgettingGeometryContributionCount .transferRigidity .scopeBoundary) =
        (1, 3, 1, 1) ∧
    (forgettingGeometryContributionCount .interferenceGram .directLift,
      forgettingGeometryContributionCount .interferenceGram .newContent,
      forgettingGeometryContributionCount .interferenceGram .restatement,
      forgettingGeometryContributionCount .interferenceGram .scopeBoundary) =
        (1, 3, 1, 1) := by
  decide

#print axioms forgettingGeometryContributionCounts

end Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry
