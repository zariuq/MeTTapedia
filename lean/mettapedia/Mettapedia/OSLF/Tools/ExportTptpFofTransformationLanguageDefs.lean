import Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedFormulaLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofNormalizationLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofPrenexNormalizationLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfGenerationLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchGenerationLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofCnfNameAllocationLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationLanguageDef

/-!
# Export the TPTP FOF transformation LanguageDefs

This tool projects the ten validated `LanguageDef` values used by the complete
FOF-to-official-CNF-AST pipeline into the canonical five-field wire.  Projection
is fail-closed: an unsupported row aborts the export instead of being erased.
-/

namespace Mettapedia.OSLF.Tools.ExportTptpFofTransformationLanguageDefs

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

private structure Artifact where
  filename : String
  language : LanguageDef

private def artifacts : List Artifact := [
  { filename := "official_fof_to_named_v1.metta"
    language := TptpOfficialFofToNamedFormulaLanguageDef.language },
  { filename := "named_fof_to_resolved_v1.metta"
    language := TptpNamedFofToResolvedLanguageDef.language },
  { filename := "fof_normalization_v1.metta"
    language := TptpFofNormalizationLanguageDef.language },
  { filename := "fof_prenex_normalization_v1.metta"
    language := TptpFofPrenexNormalizationLanguageDef.language },
  { filename := "fof_skolemization_v1.metta"
    language := TptpFofSkolemizationLanguageDef.language },
  { filename := "fof_definitional_naming_v1.metta"
    language := TptpFofDefinitionalNamingLanguageDef.language },
  { filename := "fof_definitional_cnf_generation_v1.metta"
    language := TptpFofDefinitionalCnfGenerationLanguageDef.language },
  { filename := "fof_clausification_batch_generation_v1.metta"
    language := TptpFofClausificationBatchGenerationLanguageDef.language },
  { filename := "fof_cnf_name_allocation_v1.metta"
    language := TptpFofCnfNameAllocationLanguageDef.language },
  { filename := "fof_cnf_official_ast_v1.metta"
    language := TptpFofCnfOfficialSerializationLanguageDef.language }
]

private def writeArtifact (outDir : System.FilePath)
    (artifact : Artifact) : IO Unit := do
  match CanonicalWire.renderLanguage? artifact.language with
  | some wire => IO.FS.writeFile (outDir / artifact.filename) wire
  | none =>
      throw (IO.userError
        s!"canonical wire does not support every row of {artifact.language.name}")

private def exportAll (outDir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll outDir
  for artifact in artifacts do
    writeArtifact outDir artifact

def runCli (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outDir] =>
      exportAll outDir
      pure 0
  | _ =>
      IO.eprintln
        "usage: ExportTptpFofTransformationLanguageDefs <output-directory>"
      pure 2

end Mettapedia.OSLF.Tools.ExportTptpFofTransformationLanguageDefs

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportTptpFofTransformationLanguageDefs.runCli arguments
