import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangPrimitiveControls

open Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangPrimitiveControls

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected output-directory")
  IO.FS.createDirAll directory
  IO.FS.writeFile (System.FilePath.mk directory / "controls.metta") primitiveControls
  IO.println s!"emitted {primitiveCases.length} primitive controls"
