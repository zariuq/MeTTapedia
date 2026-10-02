import Mettapedia.GSLT.LanguageDef.NativeOpsSource

/-! Text admission composes the existing carrier parser with complete operational admission. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open Algorithms.MeTTa.Simple.Parser (SExpr)

def admitProgramText? (catalogue : Catalogue) (source : String) : Option Program :=
  match Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed MeTTailCore.MeTTaSyntax.petta source with
  | .ok sourceSyntax => admitProgram? catalogue sourceSyntax
  | .error _ => none

theorem admitProgramText?_of_parsed (catalogue : Catalogue) (source : String)
    (sourceSyntax : SExpr) (program : Program)
    (parsed : Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed
      MeTTailCore.MeTTaSyntax.petta source = .ok sourceSyntax)
    (admitted : admitProgram? catalogue sourceSyntax = some program) :
    admitProgramText? catalogue source = some program := by
  simp only [admitProgramText?, parsed, admitted]

end Mettapedia.GSLT.LanguageDef.NativeOps
