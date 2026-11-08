import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler

/-! Write CeTTa's ground CHR package: the source grammar, parser plan, core
and execution records, with a compiler written in MeTTa. Generating the
package needs Lean; using it does not. -/

open Mettapedia.GSLT.LanguageDef.ModuleFormat

def main (arguments : List String) : IO Unit := do
  let [path] := arguments | throw (IO.userError "expected the output path")
  match CHRRuntimeCompiler.mettaPackage with
  | .error reason => throw (IO.userError reason)
  | .ok json =>
    match json.getObjValAs? String "module" with
    | .error reason => throw (IO.userError reason)
    | .ok text =>
      IO.FS.writeFile path text
      IO.println s!"wrote the ground CHR package ({text.length} characters)"
