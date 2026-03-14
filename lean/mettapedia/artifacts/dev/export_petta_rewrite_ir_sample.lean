import Mettapedia.Languages.MeTTa.PeTTa.RewriteIR

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.RewriteIR

private def defaultOutDir : System.FilePath :=
  "/home/zar/claude/lean-projects/mettapedia/.artifacts/petta_rewrite_ir_sample"

private def sampleSpace : PeTTaSpace :=
  { facts := []
    rules :=
      [ { name := "ordinary"
          typeContext := []
          premises := []
          left := .apply "foo" [.fvar "X"]
          right := .apply "bar" [.fvar "X"] }
      , { name := "tail_rule"
          typeContext := []
          premises := []
          left := .apply "tail" [.fvar "xs"]
          right := .apply "cons" [.fvar "x", .fvar "xs"] }
      , { name := "use_wrap"
          typeContext := []
          premises := []
          left := .apply "use" [.apply "mk" [.fvar "x"], .fvar "y"]
          right := .apply "pair" [.fvar "x", .fvar "y"] } ] }

def main (args : List String) : IO UInt32 := do
  let outDir :=
    match args with
    | dir :: _ => dir
    | [] => defaultOutDir.toString
  let outPath : System.FilePath := outDir
  let exportCode ← exportPeTTaRewriteIR outPath sampleSpace
  if exportCode != 0 then
    pure exportCode
  else
    checkPeTTaRewriteIR outPath sampleSpace
