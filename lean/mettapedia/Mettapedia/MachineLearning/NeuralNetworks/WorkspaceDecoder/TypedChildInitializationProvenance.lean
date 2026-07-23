import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.TypedChildInitialization

/-!
# Typed child-initialization provenance

This ledger separates exact source-shaped maps, new carrier-independent
factorization and invariants, and proved scope boundaries.  It counts theorem
families rather than declarations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.TypedChildInitializationProvenance

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
      "shared role-parent-argument-depth metadata map",
      "typed workspace and selective belief decoder sources"⟩
  , ⟨.exactRestatement,
      "workspace two-branch tanh child initialization",
      "typed workspace decoder source"⟩
  , ⟨.exactRestatement,
      "belief sigmoid-softplus complementary packet initialization",
      "selective belief decoder source"⟩
  , ⟨.newContent,
      "carrier-independent typed metadata factorization",
      "TypedChildInitialization"⟩
  , ⟨.newContent,
      "belief packet precision, positivity, and strength recovery",
      "TypedChildInitialization"⟩
  , ⟨.newContent,
      "composition with permanent-address child allocation",
      "TypedChildInitialization"⟩
  , ⟨.scopeBoundary,
      "unclamped argument and depth embeddings change metadata",
      "TypedChildInitialization"⟩
  , ⟨.scopeBoundary,
      "zero-based parent identifiers change metadata",
      "TypedChildInitialization"⟩
  , ⟨.scopeBoundary,
      "collapsing the workspace affine branches changes child values",
      "TypedChildInitialization"⟩
  , ⟨.scopeBoundary,
      "omitting minimum belief precision changes the stored packet",
      "TypedChildInitialization"⟩ ]

def contributionCount (kind : ContributionKind) : Nat :=
  (contributions.filter fun contribution ↦ contribution.kind = kind).length

theorem contributionCounts :
    (contributionCount .exactRestatement,
      contributionCount .newContent,
      contributionCount .scopeBoundary) = (3, 3, 4) := by
  decide

#print axioms contributionCounts

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.TypedChildInitializationProvenance
