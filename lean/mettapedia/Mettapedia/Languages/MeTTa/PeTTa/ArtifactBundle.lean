import Mettapedia.Languages.MeTTa.PeTTa.LookupPlan
import Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract
import Mettapedia.Languages.MeTTa.PeTTa.ScopeContract
import Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec
import Mettapedia.Languages.MeTTa.PeTTa.RewriteIR

/-!
# PeTTa Artifact Bundle

Pure spec-side artifact bundle over `PeTTaSpace`.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.Artifacts

private def writeLookupPlan (outDir : System.FilePath) : IO UInt32 := do
  let artifact := Mettapedia.Languages.MeTTa.PeTTa.LookupPlan.pettaLookupPlanArtifact
  let jsonPath := outDir / "petta.lookup_plan.json"
  let checksumPath := outDir / "petta.lookup_plan.checksum"
  IO.FS.createDirAll outDir
  IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
  IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
  pure 0

private def checkLookupPlan (outDir : System.FilePath) : IO UInt32 := do
  let artifact := Mettapedia.Languages.MeTTa.PeTTa.LookupPlan.pettaLookupPlanArtifact
  let jsonPath := outDir / "petta.lookup_plan.json"
  let checksumPath := outDir / "petta.lookup_plan.checksum"
  try
    let jsonText ← IO.FS.readFile jsonPath
    let checksumText ← IO.FS.readFile checksumPath
    let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
    let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
    if jsonOk && checksumOk then
      pure 0
    else
      pure 3
  catch _ =>
    pure 2

def exportPeTTaArtifacts (outDir : System.FilePath) (s : PeTTaSpace) : IO UInt32 := do
  let a ← writeLookupPlan outDir
  let b ← Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract.exportPeTTaExecutionContract outDir
  let c ← Mettapedia.Languages.MeTTa.PeTTa.ScopeContract.exportPeTTaScopeContract outDir
  let d ← Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec.exportPeTTaTransitionSpec outDir s
  let e ← Mettapedia.Languages.MeTTa.PeTTa.RewriteIR.exportPeTTaRewriteIR outDir s
  if a == 0 && b == 0 && c == 0 && d == 0 && e == 0 then
    IO.println s!"exported petta artifact bundle to {outDir}"
    pure 0
  else
    pure 2

def checkPeTTaArtifacts (outDir : System.FilePath) (s : PeTTaSpace) : IO UInt32 := do
  let a ← checkLookupPlan outDir
  let b ← Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract.checkPeTTaExecutionContract outDir
  let c ← Mettapedia.Languages.MeTTa.PeTTa.ScopeContract.checkPeTTaScopeContract outDir
  let d ← Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec.checkPeTTaTransitionSpec outDir s
  let e ← Mettapedia.Languages.MeTTa.PeTTa.RewriteIR.checkPeTTaRewriteIR outDir s
  if a == 0 && b == 0 && c == 0 && d == 0 && e == 0 then
    IO.println s!"[ok] petta artifact bundle matches at {outDir}"
    pure 0
  else
    pure 3

end Mettapedia.Languages.MeTTa.PeTTa.Artifacts
