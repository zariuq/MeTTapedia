import Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract
import Mettapedia.Languages.MeTTa.PeTTa.BoundaryContract
import Mettapedia.Languages.MeTTa.PeTTa.SemanticBundle
import Mettapedia.Languages.MeTTa.PeTTa.PrologBridge

/-!
# PeTTa Executable Boundary

Additive implementation-facing boundary for the canonical declarative PeTTa
semantics.

## Design

- `DeclarativeSpec.lean` keeps the readable declarative meaning layer.
- `ExecutionContract.lean` records executable contract slices for the live
  evaluator surface.
- `BoundaryContract.lean` classifies two-phase witness/residual behavior for
  boundary-aware operations.
- `SemanticBundle.lean` packages the stage-indexed runtime-facing semantic
  object consumed by proof-side and runtime exports.
- `PrologBridge.lean` anchors the Prolog-grounded execution story.

Positive example:
- arithmetic, reflection, and compat-head behavior belong in the executable
  boundary layer, where runtime lane policy matters.

Negative example:
- backend search policy or host-only surfaces should not be mistaken for the
  canonical declarative meaning of PeTTa programs.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa

/-- Canonical stage-indexed executable boundary bundle for PeTTa. -/
abbrev PeTTaExecutableBoundaryBundle := SemanticBundle.PeTTaSemanticBundle

/-- Canonical executable contract artifact for PeTTa. -/
def pettaExecutionBoundaryArtifact :=
  ExecutionContract.pettaExecutionContractArtifact

/-- Canonical operational boundary artifact for PeTTa's boundary-aware stage. -/
def pettaOperationalBoundaryArtifact :=
  BoundaryContract.pettaBoundaryContractArtifact

/-- PeTTa's Prolog-grounded executable oracle. -/
def peTTaPrologGrounding (s : PeTTaSpace) := meTTaPrologOracle s

end Mettapedia.Languages.MeTTa.PeTTa
