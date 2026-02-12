import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.OSLF.MeTTaIL.Syntax

open Mettapedia.OSLF.MeTTaIL.Export
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- TinyML core smoke subset for Lean->Rust loop testing.
    This intentionally avoids higher-order/eval forms that current macro
    ingestion cannot yet reconstruct from generic export text. -/
def tinyMLSmoke : LanguageDef := {
  name := "TinyMLSmoke",
  types := ["Expr", "Val"],
  terms := [
    { label := "Inject", category := "Expr",
      params := [.simple "v" (.base "Val")],
      syntaxPattern := [.nonTerminal "v"] },
    { label := "BoolT", category := "Val", params := [],
      syntaxPattern := [.terminal "true"] },
    { label := "BoolF", category := "Val", params := [],
      syntaxPattern := [.terminal "false"] },
    { label := "Thunk", category := "Val",
      params := [.simple "e" (.base "Expr")],
      syntaxPattern := [.terminal "thunk", .nonTerminal "e"] }
  ],
  equations := [],
  rewrites := [
    { name := "Force",
      typeContext := [("e", .base "Expr")],
      premises := [],
      left := .apply "Inject" [.apply "Thunk" [.fvar "e"]],
      right := .fvar "e" }
  ]
}

/-- Print TinyML as Rust `language!` macro text to stdout. -/
def main (_args : List String) : IO UInt32 := do
  IO.println (renderLanguage tinyMLSmoke)
  pure 0
