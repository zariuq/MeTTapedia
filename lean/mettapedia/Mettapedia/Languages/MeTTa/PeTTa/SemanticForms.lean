import Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec
import Mettapedia.Languages.MeTTa.PeTTa.MinimalInstructions
import Mettapedia.Languages.MeTTa.PeTTa.ExecutableBoundary

/-!
# PeTTa Semantic Forms

Light public facade making the major PeTTa semantic layers explicit.

## Semantic Layers

1. **Expression-level declarative semantics**
   `PureDecl` in `DeclarativeSpec.lean`.
2. **Stateful declarative semantics**
   `CoreDecl` in `DeclarativeSpec.lean`.
3. **Operational instruction semantics**
   `MeTTaStep` in `MinimalInstructions.lean`.
4. **Executable boundary**
   `PeTTaExecutableBoundaryBundle`,
   `pettaExecutionBoundaryArtifact`,
   `pettaOperationalBoundaryArtifact`,
   and `peTTaPrologGrounding`.

Positive example:
- `PureDecl` and `CoreDecl` explain what PeTTa programs mean independent of a
  particular Prolog search trace, while the executable boundary says how the
  live runtime is organized.

Negative example:
- the executable boundary artifacts are not a replacement for the declarative
  semantics; they are the implementation-facing layer above it.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa

/-- Expression-level declarative semantics for PeTTa. -/
abbrev PeTTaExpressionDeclarativeSemantics := PureDecl

/-- Stateful command-level declarative semantics for PeTTa. -/
abbrev PeTTaCommandDeclarativeSemantics := CoreDecl

/-- Published operational instruction semantics for PeTTa. -/
abbrev PeTTaInstructionOperationalSemantics := MeTTaStep

end Mettapedia.Languages.MeTTa.PeTTa
