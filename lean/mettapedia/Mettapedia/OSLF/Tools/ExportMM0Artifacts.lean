import Mettapedia.Languages.MM0.ArtifactBundle

open Mettapedia.Languages.MM0.ArtifactBundle in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["export-all", outDir] => exportMM0ManifestBundle outDir
  | ["export-all"] => exportMM0ManifestBundle defaultOutDir
  | ["check-all", outDir] => checkMM0ManifestBundle outDir
  | ["check-all"] => checkMM0ManifestBundle defaultOutDir
  | _ =>
    IO.println "MM0 syntax-metadata commands: export-all [outDir] | check-all [outDir]"
    pure 1
