import Mettapedia.Languages.MeTTa.HE.DeclarativeSpec
import Mettapedia.Languages.MeTTa.HE.MinimalMeTTa
import Mettapedia.Languages.MeTTa.HE.ExecutableBoundary
import Mettapedia.Languages.MeTTa.HE.Certification

/-!
# HE Semantic Forms

Light public facade making the major HE semantic layers explicit.

## Semantic Layers

1. **Declarative evaluation semantics**
   `EvalAtom` and its five mutually-recursive companion relations in
   `EvalSpec.lean`, with the auditable clause-form surface in
   `DeclarativeSpec.lean`.
2. **Operational instruction semantics**
   `MinimalStep` in `MinimalMeTTa.lean`.
3. **Executable boundary**
   `EvalAtomStablyReaches` in `ExecutableBoundary.lean`.
4. **Certified public boundary**
   `EvalAtomCertified` in `Certification.lean`.

Positive example:
- `EvalAtomCertified` expresses a top-level HE result that is both
  declaratively valid and stably supported by the executable evaluator.

Negative example:
- a coarse `EvalAtom` derivation can still be transient and therefore fail to
  inhabit the certified boundary.
-/

namespace Mettapedia.Languages.MeTTa.HE

/-- Top-level declarative HE evaluation semantics. -/
abbrev HETopLevelDeclarativeSemantics := EvalAtom

/-- Published operational instruction semantics for HE. -/
abbrev HEInstructionOperationalSemantics := MinimalStep

/-- Minimal executable HE boundary: stable evaluator reachability. -/
abbrev HEStableExecutableBoundary := EvalAtomStablyReaches

/-- Top-level certified HE executable semantics. -/
abbrev HECertifiedTopLevelSemantics := EvalAtomCertified

end Mettapedia.Languages.MeTTa.HE
