import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Carom

/-!
# Content accounting for the CAROM formalization

This family-level ledger separates direct transport from new adapters and
algebra, exact restatements, and proved scope boundaries.  It counts theorem
families rather than individual declarations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Carom

/-- Rungs of the CAROM formalization. -/
inductive ProvenanceRung
  | recurrentWrite
  | settlingAndSafety
  | selectionMetrics
  | interferenceGeometry
  | twoRecurrences
  deriving DecidableEq, Repr

/-- Provenance class for one theorem family. -/
inductive ContributionKind
  | directLift
  | newContent
  | exactRestatement
  | scopeBoundary
  deriving DecidableEq, Repr

/-- One family in the CAROM contribution ledger. -/
structure Contribution where
  kind : ContributionKind
  family : String
  source : String
  deriving Repr

/-- Exhaustive family-level ledger for the five formalization rungs. -/
def contributions : ProvenanceRung → List Contribution
  | .recurrentWrite =>
      [ ⟨.directLift, "gated workspace dynamics", "Dynamics"⟩
      , ⟨.newContent, "read-transform-gate mechanism adapter", "Carom"⟩
      , ⟨.exactRestatement, "simultaneous recurrent-write equation", "Carom"⟩
      , ⟨.newContent, "gain-weighted target collapse", "Carom"⟩
      , ⟨.scopeBoundary, "zero-gate and nondegenerate scalar fixtures", "Carom"⟩ ]
  | .settlingAndSafety =>
      [ ⟨.directLift, "spectral equilibrium and convergence", "LinearSettling"⟩
      , ⟨.directLift, "geometric residual envelope", "LinearSettling"⟩
      , ⟨.directLift, "legal-action soundness and recall", "TypedRegisters"⟩
      , ⟨.newContent, "exact affine linearization certificate", "Carom"⟩
      , ⟨.scopeBoundary, "contraction has no finite optimum in general", "Carom"⟩ ]
  | .selectionMetrics =>
      [ ⟨.directLift, "finite target-mismatch optimum", "LinearSettling"⟩
      , ⟨.directLift, "shift-chain entropy turnover", "EntropyTurnover"⟩
      , ⟨.newContent, "target and equilibrium residual separation", "Carom"⟩
      , ⟨.newContent, "hard-positive cross-entropy functional", "Carom"⟩
      , ⟨.scopeBoundary, "cross-entropy reversal witness", "Carom"⟩ ]
  | .interferenceGeometry =>
      [ ⟨.directLift, "zero energy iff curvature commutes", "InterferenceGram"⟩
      , ⟨.directLift, "centered sequential order theorem", "QuadraticTwoTask"⟩
      , ⟨.directLift, "sequential connection remainder", "MetricDictionary"⟩
      , ⟨.newContent, "labeled quadratic operator family", "Carom"⟩
      , ⟨.exactRestatement, "positive-energy simultaneous write remains exact", "Carom"⟩
      , ⟨.scopeBoundary, "energy and remainder are incomparable", "Carom"⟩ ]
  | .twoRecurrences =>
      [ ⟨.directLift, "sealed atomic transition", "AtomicRefinement"⟩
      , ⟨.newContent, "two-scale product state", "Carom"⟩
      , ⟨.newContent, "finite and equilibrium outer steps", "Carom"⟩
      , ⟨.exactRestatement, "root projection equals sealed transition", "Carom"⟩
      , ⟨.scopeBoundary, "finite depths differ away from equilibrium", "Carom"⟩ ]

/-- Count one provenance class on one rung. -/
def contributionCount (rung : ProvenanceRung) (kind : ContributionKind) : Nat :=
  ((contributions rung).filter fun entry => entry.kind = kind).length

/-- Machine-checked counts ordered as direct lift, new content, exact
restatement, and scope boundary for each rung. -/
theorem contributionCounts :
    (contributionCount .recurrentWrite .directLift,
      contributionCount .recurrentWrite .newContent,
      contributionCount .recurrentWrite .exactRestatement,
      contributionCount .recurrentWrite .scopeBoundary) = (1, 2, 1, 1) ∧
    (contributionCount .settlingAndSafety .directLift,
      contributionCount .settlingAndSafety .newContent,
      contributionCount .settlingAndSafety .exactRestatement,
      contributionCount .settlingAndSafety .scopeBoundary) = (3, 1, 0, 1) ∧
    (contributionCount .selectionMetrics .directLift,
      contributionCount .selectionMetrics .newContent,
      contributionCount .selectionMetrics .exactRestatement,
      contributionCount .selectionMetrics .scopeBoundary) = (2, 2, 0, 1) ∧
    (contributionCount .interferenceGeometry .directLift,
      contributionCount .interferenceGeometry .newContent,
      contributionCount .interferenceGeometry .exactRestatement,
      contributionCount .interferenceGeometry .scopeBoundary) = (3, 1, 1, 1) ∧
    (contributionCount .twoRecurrences .directLift,
      contributionCount .twoRecurrences .newContent,
      contributionCount .twoRecurrences .exactRestatement,
      contributionCount .twoRecurrences .scopeBoundary) = (1, 2, 1, 1) := by
  decide

#print axioms contributionCounts

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Carom
