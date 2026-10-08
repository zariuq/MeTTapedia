import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.DeclarativeSpec
import Mettapedia.Languages.MeTTa.PeTTa.MinimalInstructions

/-!
# PeTTa Semantic Forms

Public names for the declarative and instruction layers of the MeTTaIL view:
`PureDecl` and `CoreDecl` in `DeclarativeSpec`, and `MeTTaStep` in
`MinimalInstructions`. These are one-step relations over `Pattern`; the
semantics of PeTTa programs is the machine in `Eval`.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa

/-- Expression-level declarative semantics for PeTTa. -/
abbrev PeTTaExpressionDeclarativeSemantics := PureDecl

/-- Stateful command-level declarative semantics for PeTTa. -/
abbrev PeTTaCommandDeclarativeSemantics := CoreDecl

/-- Published operational instruction semantics for PeTTa. -/
abbrev PeTTaInstructionOperationalSemantics := MeTTaStep

end Mettapedia.Languages.MeTTa.PeTTa
