import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.CarrierDecisionPipeline

/-!
# Carrier decision-pipeline provenance

This ledger separates source-shaped ideal-real maps, reusable support
theorems, and explicit scope boundaries. It counts theorem families rather
than declarations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.CarrierDecisionPipelineProvenance

inductive ContributionKind
  | exactRestatement
  | newContent
  | scopeBoundary
  deriving DecidableEq, Repr

structure Contribution where
  kind : ContributionKind
  family : String
  source : String
  deriving Repr

def contributions : List Contribution :=
  [ ⟨.exactRestatement,
      "clamped allocated-slot mean and active-address injection",
      "typed workspace decoder source"⟩
  , ⟨.exactRestatement,
      "masked query-to-key reads and routed write gates",
      "workspace and selective belief decoder sources"⟩
  , ⟨.exactRestatement,
      "carrier-specific control and shared active-pooled-control decision waist",
      "workspace and selective belief decoder sources"⟩
  , ⟨.exactRestatement,
      "masked source attention, operator dot score, bias, and final legal mask",
      "TGAD O2 policy host source"⟩
  , ⟨.newContent,
      "inactive-slot irrelevance and exact empty-pool boundary",
      "CarrierDecisionPipeline"⟩
  , ⟨.newContent,
      "nonempty masked-query normalization",
      "CarrierDecisionPipeline"⟩
  , ⟨.newContent,
      "exact legal-support independence from learned scores",
      "CarrierDecisionPipeline"⟩
  , ⟨.newContent,
      "complete source-shaped policy-readout support theorem",
      "CarrierDecisionPipeline"⟩
  , ⟨.scopeBoundary,
      "broadcast typed-hole injection changes inactive addresses",
      "CarrierDecisionPipeline"⟩
  , ⟨.scopeBoundary,
      "workspace and belief controls differ at the typed-hole branch",
      "CarrierDecisionPipeline"⟩
  , ⟨.scopeBoundary,
      "active and pooled concatenation order is observable",
      "CarrierDecisionPipeline"⟩
  , ⟨.scopeBoundary,
      "omitting the final legal mask admits rejected operators",
      "CarrierDecisionPipeline"⟩ ]

def contributionCount (kind : ContributionKind) : Nat :=
  (contributions.filter fun contribution ↦ contribution.kind = kind).length

theorem contributionCounts :
    (contributionCount .exactRestatement,
      contributionCount .newContent,
      contributionCount .scopeBoundary) = (4, 4, 4) := by
  decide

#print axioms contributionCounts

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.CarrierDecisionPipelineProvenance
