import Mettapedia.Languages.MeTTa.HE.SemanticForms
import Mettapedia.Languages.MeTTa.PeTTa.SemanticForms
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslate

/-!
# HE ↔ PeTTa Semantic Forms

Public cross-dialect facade naming the aligned semantic layers for HE and
PeTTa together with the translator bridge between them.

## Layered Alignment

1. **HE declarative core**
   `Mettapedia.Languages.MeTTa.HE.HETopLevelDeclarativeSemantics`
2. **PeTTa declarative core**
   `Mettapedia.Languages.MeTTa.PeTTa.PeTTaExpressionDeclarativeSemantics`
   and `PeTTaCommandDeclarativeSemantics`
3. **Operational layers**
   `HEInstructionOperationalSemantics` and
   `PeTTaInstructionOperationalSemantics`
4. **Executable layers**
   `HEStableExecutableBoundary`, `HECertifiedTopLevelSemantics`, and
   `PeTTaExecutableBoundaryBundle`
5. **Translator bridge**
   `HEPeTTaTranslateCore`, validated roundtrip theorems, and the operational
   bridge for the currently shared state/space/import fragments

Positive example:
- HE can remain the clearest declarative anchor while PeTTa contributes a
  stronger operational grounding, with the translator making the relationship
  explicit rather than informal.

Negative example:
- runtime-only host surfaces or backend quirks are not automatically promoted
  into a shared semantic core just because a translator exists.
-/
