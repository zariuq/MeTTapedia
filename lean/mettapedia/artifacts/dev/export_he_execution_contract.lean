import Mettapedia.Languages.MeTTa.HE.ExecutionContract

open Mettapedia.Languages.MeTTa.HE.ExecutionContract

def defaultOutDir : System.FilePath :=
  "/home/zar/claude/lean-projects/mettapedia/artifacts/transition"

def main (_args : List String) : IO UInt32 := do
  let outDir := defaultOutDir
  let exportCode ← exportHeExecutionContract outDir
  if exportCode != 0 then
    pure exportCode
  else
    checkHeExecutionContract outDir
