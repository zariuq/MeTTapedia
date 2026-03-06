import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.Languages.MinskyLite.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Export
open Mettapedia.Languages.MinskyLite.LanguageDef

/-- Print MinskyLite as Rust `language!` macro text to stdout. -/
def main (_args : List String) : IO UInt32 := do
  IO.println (renderLanguageWithUserSyntax minskyLite)
  pure 0
