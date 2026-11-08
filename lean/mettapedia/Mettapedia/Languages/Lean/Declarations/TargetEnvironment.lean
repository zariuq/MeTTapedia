import Lean

/-!
# Module inventories for declaration exporters

A target's `modules.txt` contains `source Module.Name` and `import Module.Name`
entries. Source modules own the declarations whose display exclusions are
reported; import-only modules provide supporting declarations and executable
instances. A bare module name is a source entry. The inventory is data, so a
new export target does not require editing the exporter script's imports.
-/

namespace Mettapedia.Languages.Lean.Declarations.TargetEnvironment

open _root_.Lean

structure Modules where
  sources : Array Name := #[]
  imports : Array Name := #[]
  deriving DecidableEq, Repr

def parse (text : String) : Except String Modules := do
  let mut result : Modules := {}
  for raw in text.splitOn "\n" do
    let line := ((raw.splitOn "#").headD "").trimAscii.toString
    if line.isEmpty then continue
    let parts := (line.splitOn " ").filter (!·.isEmpty)
    let (source, name) ← match parts with
      | [name] => pure (true, name)
      | ["source", name] => pure (true, name)
      | ["import", name] => pure (false, name)
      | _ => throw ("malformed target module entry: " ++ line)
    unless (name.splitOn ".").all (fun part => !part.isEmpty &&
      part.toList.all (fun c => c.isAlphanum || c == '_')) do
      throw ("invalid target module name: " ++ name)
    let name := name.toName
    if result.imports.contains name then throw ("duplicate target module: " ++ name.toString)
    result := {
      sources := if source then result.sources.push name else result.sources
      imports := result.imports.push name }
  return result

def read (directory : System.FilePath) : IO Modules := do
  let file := directory / "modules.txt"
  unless ← file.pathExists do throw (IO.userError ("target module inventory is missing: " ++ file.toString))
  IO.ofExcept (parse (← IO.FS.readFile file))

/-- Import the inventory alongside the exporter's fixed infrastructure. The
resulting environment is used for declaration lookup, elaboration and replay. -/
def load (directory : System.FilePath) : CoreM Modules := do
  let modules ← read directory
  let previous ← getEnv
  if modules.imports.all (fun name => (previous.getModuleIdx? name).isSome) then return modules
  let mut imports := previous.header.imports
  for name in modules.imports do
    unless imports.any (·.module == name) do imports := imports.push { module := name }
  unsafe enableInitializersExecution
  let imported ← importModules imports (← getOptions) (leakEnv := true) (loadExts := true)
  setEnv (imported.setMainModule previous.mainModule)
  return modules

end Mettapedia.Languages.Lean.Declarations.TargetEnvironment
