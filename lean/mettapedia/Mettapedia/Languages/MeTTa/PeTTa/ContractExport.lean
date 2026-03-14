import Mettapedia.Languages.MeTTa.PeTTa.ContractCatalog

/-!
# PeTTa Contract Export

Artifact export/check layer for the PeTTa execution-contract catalog.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract

def exportPeTTaExecutionContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := pettaExecutionContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"petta execution contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "petta.execution_contract.json"
    let checksumPath := outDir / "petta.execution_contract.checksum"
    IO.FS.createDirAll outDir
    IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
    IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
    IO.println s!"exported petta execution contract to {outDir}"
    pure 0

def checkPeTTaExecutionContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := pettaExecutionContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"petta execution contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "petta.execution_contract.json"
    let checksumPath := outDir / "petta.execution_contract.checksum"
    try
      let jsonText ← IO.FS.readFile jsonPath
      let checksumText ← IO.FS.readFile checksumPath
      let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
      let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
      if jsonOk && checksumOk then
        IO.println s!"[ok] petta execution contract matches at {outDir}"
        pure 0
      else
        if !jsonOk then
          IO.println s!"[drift] petta execution contract json mismatch at {jsonPath}"
        if !checksumOk then
          IO.println s!"[drift] petta execution contract checksum mismatch at {checksumPath}"
        pure 3
    catch e =>
      IO.println s!"petta execution contract check failed: {e}"
      pure 2

section Canaries
#check @spaceMatchLookupContract
#check @pettaExecutionContractArtifact
#check @exportPeTTaExecutionContract
#check @checkPeTTaExecutionContract
end Canaries

end Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract
