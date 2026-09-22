/-
Emit the test-only CArray0 shadow interface and implementation from the target
instruction language in `CArray0SequenceHosting`.

Run:
  lake env lean --run scripts/EmitCArray0Pilot.lean [output-directory]
-/
import Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting

open Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting

def outputPath (directory name : String) : String :=
  if directory.endsWith "/" then directory ++ name else directory ++ "/" ++ name

def main (args : List String) : IO UInt32 := do
  let directory := args.head?.getD "."
  IO.FS.createDirAll directory
  IO.FS.writeFile
    (outputPath directory "carray0_shadow_v1.generated.h")
    emitCArray0ShadowHeader
  IO.FS.writeFile
    (outputPath directory "carray0_shadow_v1.generated.c")
    emitCArray0ShadowSource
  IO.println "emitted CArray0 shadow target"
  return 0
