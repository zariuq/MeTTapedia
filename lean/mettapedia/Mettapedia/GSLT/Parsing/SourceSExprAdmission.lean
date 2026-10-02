import Mettapedia.GSLT.Parsing.SourceScanSegments
import Mettapedia.GSLT.Parsing.SourceLexSegments
import Mettapedia.GSLT.Parsing.SExprTokenRoundTrip

/-! Source admission through the existing scanner, lexer and token parser. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourceSExprAdmission

open Algorithms.MeTTa.Simple.Parser
open SExprTokenRoundTrip
open private tokenizeWith parserDialectOf parseSingleSExprWith parseSExprOne
  splitProgramForms from Algorithms.MeTTa.Simple.Parser

theorem single_of_tokens (source : String) (expression : SExpr) (valid : safe expression)
    (lexed : tokenizeWith (parserDialectOf MeTTailCore.MeTTaSyntax.petta) source =
      tokens expression) :
    parseSingleSExprWith (parserDialectOf MeTTailCore.MeTTaSyntax.petta) source =
      .ok expression := by
  have nonempty : (tokens expression).isEmpty = false := by
    cases equal : tokens expression with
    | nil =>
        have positive := tokens_positive expression
        rw [equal] at positive
        simp at positive
    | cons token rest => rfl
  unfold parseSingleSExprWith
  rw [lexed]
  simp only [nonempty, Bool.false_eq_true, ↓reduceIte]
  unfold parseSExprOne
  rw [parse_tokens_whole expression valid]
  rfl

theorem parsed_of_forms (source : String) (expression : SExpr)
    (forms : splitProgramForms (parserDialectOf MeTTailCore.MeTTaSyntax.petta) source =
      .ok [(1, source)])
    (single : parseSingleSExprWith (parserDialectOf MeTTailCore.MeTTaSyntax.petta) source =
      .ok expression) :
    parseSExprWithDetailed MeTTailCore.MeTTaSyntax.petta source = .ok expression := by
  unfold parseSExprWithDetailed
  dsimp only
  rw [forms]
  exact single

end Mettapedia.GSLT.Parsing.SourceSExprAdmission
