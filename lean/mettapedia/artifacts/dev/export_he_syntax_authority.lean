import Mettapedia.Languages.MeTTa.HE.SyntaxSpec

open Mettapedia.Languages.MeTTa.HE

def defaultOutDir : System.FilePath :=
  "/home/zar/claude/lean-projects/mettapedia/artifacts/syntax"

def main (_args : List String) : IO UInt32 := do
  let outDir := defaultOutDir
  let exportCode ← exportHeSyntaxAuthority outDir
  if exportCode != 0 then
    pure exportCode
  else
    checkHeSyntaxAuthority outDir
