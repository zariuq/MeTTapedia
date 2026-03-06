import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.Languages.MM0Lite.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Export
open Mettapedia.Languages.MM0Lite.LanguageDef

private def withMM0LogicStub (src : String) : String :=
  if src.endsWith "}" then
    (src.dropEnd 1).toString
      ++ "\n\n    logic {\n"
      ++ "        relation thmConcl(Thm, Formula);\n"
      ++ "    },\n"
      ++ "}"
  else
    src

/-- Print MM0-Lite as Rust `language!` macro text to stdout. -/
def main (_args : List String) : IO UInt32 := do
  IO.println (withMM0LogicStub (renderLanguageWithUserSyntax mm0Lite))
  pure 0
