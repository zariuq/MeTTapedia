import Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract
import Mettapedia.Languages.MeTTa.PeTTa.ScopeContract

open Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract
open Mettapedia.Languages.MeTTa.PeTTa.ScopeContract

private def defaultOutDir : System.FilePath :=
  "/home/zar/claude/lean-projects/mettapedia/artifacts/transition"

def main (args : List String) : IO UInt32 := do
  let outDir :=
    match args with
    | dir :: _ => dir
    | [] => defaultOutDir.toString
  let outPath : System.FilePath := outDir
  let exportCode ← exportPeTTaExecutionContract outPath
  if exportCode != 0 then
    pure exportCode
  else
    let scopeExportCode ← exportPeTTaScopeContract outPath
    if scopeExportCode != 0 then
      pure scopeExportCode
    else
      let checkCode ← checkPeTTaExecutionContract outPath
      if checkCode != 0 then
        pure checkCode
      else
        checkPeTTaScopeContract outPath
