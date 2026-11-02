import Lean
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxCommand
import Mettapedia.GSLT.LanguageDef.ModuleSource.Loader

/-! A compiled entry point for module-driven source syntax I/O. Module
loading uses the existing reader and elaborator; all operations call the
same checked source interface as an interpreted driver. -/

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxMain

open Lean

def source (modulePath : String) (arguments : List String) : String :=
  "import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxCommand\n" ++
  "import Mettapedia.GSLT.LanguageDef.ModuleSource.Loader\n" ++
  "set_option maxRecDepth 32768\nset_option maxHeartbeats 8000000\n" ++
  "namespace SourceInput\n" ++
  s!"#module_tree {modulePath.quote} as Loaded\n" ++
  "end SourceInput\n" ++
  "#eval Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxCommand.run " ++
  s!"SourceInput.Loaded.library SourceInput.Loaded.module {arguments.map String.quote}\n"

def main (arguments : List String) : IO UInt32 := do
  let modulePath :: operations := arguments
    | IO.eprintln "usage: sourceSyntax LANGUAGE.module OPERATION ARGUMENTS..."; return 2
  let resolved ← IO.FS.realPath modulePath
  initSearchPath (← findSysroot)
  unsafe Lean.enableInitializersExecution
  let options := ({} : Options).setBool `interpreter.prefer_native true
  let result ← Lean.Elab.runFrontend (source resolved.toString operations) options
    (resolved.parent.getD "." / "SourceSyntaxInput.lean").toString `SourceSyntaxInput
  return if result.isSome then 0 else 1

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxMain

def main := Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxMain.main
