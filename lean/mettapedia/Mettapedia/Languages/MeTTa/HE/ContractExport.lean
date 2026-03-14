import Mettapedia.Languages.MeTTa.HE.ContractCatalog

/-!
# HE Contract Export

Artifact export/check layer for the HE execution-contract catalog.
-/

namespace Mettapedia.Languages.MeTTa.HE.ExecutionContract

def exportHeExecutionContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := heExecutionContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"he execution contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "he.execution_contract.json"
    let checksumPath := outDir / "he.execution_contract.checksum"
    IO.FS.createDirAll outDir
    IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
    IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
    IO.println s!"exported he execution contract to {outDir}"
    pure 0

def checkHeExecutionContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := heExecutionContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"he execution contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "he.execution_contract.json"
    let checksumPath := outDir / "he.execution_contract.checksum"
    try
      let jsonText ← IO.FS.readFile jsonPath
      let checksumText ← IO.FS.readFile checksumPath
      let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
      let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
      if jsonOk && checksumOk then
        IO.println s!"[ok] he execution contract matches at {outDir}"
        pure 0
      else
        if !jsonOk then
          IO.println s!"[drift] he execution contract json mismatch at {jsonPath}"
        if !checksumOk then
          IO.println s!"[drift] he execution contract checksum mismatch at {checksumPath}"
        pure 3
    catch e =>
      IO.println s!"he execution contract check failed: {e}"
      pure 2

section Canaries
#check @heEqQueryLookupContract
#check @heExecutionContractArtifact
#check @exportHeExecutionContract
#check @checkHeExecutionContract
end Canaries

end Mettapedia.Languages.MeTTa.HE.ExecutionContract
