import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.OSLF.MeTTaIL.Syntax

open Mettapedia.OSLF.MeTTaIL.Export
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- TinyML core smoke subset for Lean->Rust loop testing. -/
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

/-- Round-trip smoke input term, serialized for mettail-rust parser. -/
def tinyMLSmokeInput : String :=
  "C_Inject(C_Thunk(C_Inject(C_BoolT)))"

/-- Expected one-step rewrite result in mettail-rust. -/
def tinyMLSmokeExpected : String :=
  "C_Inject(C_BoolT)"

private def usage : String :=
  String.intercalate "\n"
    [ "Usage:"
    , "  lake env lean --run Mettapedia/OSLF/Tools/ExportTinyMLSmokeRoundTrip.lean"
    , "  lake env lean --run Mettapedia/OSLF/Tools/ExportTinyMLSmokeRoundTrip.lean <lang_out> <input_out> <expected_out>"
    ]

/--
Emit round-trip artifacts for the Lean->Rust tiny smoke loop.

- No args: print all artifacts to stdout.
- 3 args: write language macro text, input term, expected output term to files.
-/
def main (args : List String) : IO UInt32 := do
  let rendered := renderLanguage tinyMLSmoke
  match args with
  | [] =>
      IO.println "=== LANGUAGE ==="
      IO.println rendered
      IO.println "=== INPUT ==="
      IO.println tinyMLSmokeInput
      IO.println "=== EXPECTED ==="
      IO.println tinyMLSmokeExpected
      pure 0
  | [langOut, inputOut, expectedOut] =>
      IO.FS.writeFile langOut (rendered ++ "\n")
      IO.FS.writeFile inputOut (tinyMLSmokeInput ++ "\n")
      IO.FS.writeFile expectedOut (tinyMLSmokeExpected ++ "\n")
      pure 0
  | _ =>
      IO.eprintln usage
      pure 1
