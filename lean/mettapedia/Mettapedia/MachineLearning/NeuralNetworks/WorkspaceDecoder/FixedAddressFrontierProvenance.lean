import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FixedAddressFrontier

/-!
# Fixed-address frontier provenance

This ledger separates the inherited bounded-completion equation, the shared
frontier theory, exact source-layout restatements, and proved negative
boundaries.  It counts theorem families rather than declarations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FixedAddressFrontierProvenance

inductive ContributionKind
  | directLift
  | newContent
  | exactRestatement
  | scopeBoundary
  deriving DecidableEq, Repr

structure Contribution where
  kind : ContributionKind
  family : String
  source : String
  deriving Repr

def contributions : List Contribution :=
  [ ⟨.directLift,
      "bounded completion equals cursor-capacity admission",
      "TGAD top-down adapter"⟩
  , ⟨.newContent,
      "carrier-independent fixed-address previous-action transition",
      "FixedAddressFrontier"⟩
  , ⟨.newContent,
      "cursor identity, bounds, and distinctness preservation",
      "FixedAddressFrontier"⟩
  , ⟨.newContent,
      "parametric child-content initialization",
      "FixedAddressFrontier"⟩
  , ⟨.exactRestatement,
      "workspace payload followed by the shared discrete tail",
      "FixedAddressFrontier"⟩
  , ⟨.exactRestatement,
      "positive and negative belief payloads followed by the same tail",
      "FixedAddressFrontier"⟩
  , ⟨.scopeBoundary,
      "tail-first frontier order changes the active address",
      "FixedAddressFrontier"⟩
  , ⟨.scopeBoundary,
      "updated-cursor child allocation changes content writes",
      "FixedAddressFrontier"⟩
  , ⟨.scopeBoundary,
      "swapped length and cursor fields change the packed row",
      "FixedAddressFrontier"⟩ ]

def contributionCount (kind : ContributionKind) : Nat :=
  (contributions.filter fun contribution => contribution.kind = kind).length

theorem contributionCounts :
    (contributionCount .directLift,
      contributionCount .newContent,
      contributionCount .exactRestatement,
      contributionCount .scopeBoundary) = (1, 3, 2, 3) := by
  decide

#print axioms contributionCounts

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FixedAddressFrontierProvenance
