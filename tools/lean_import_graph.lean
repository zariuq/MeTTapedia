import Lean

set_option autoImplicit false

open Lean System

structure SnapshotModule where
  name : String
  relative : String
  object : String
  imports : Array String
  moduleSystem : Bool
  deriving ToJson

/-- Read the same import headers and compiled import names that Lean uses. -/
def main (args : List String) : IO Unit := do
  let searchPath :: sources := args
    | throw (IO.userError "expected an import search path and Lean source files")
  let roots := if searchPath.isEmpty then [] else SearchPath.parse searchPath
  searchPathRef.set (roots ++ (← getBuiltinSearchPath (← findSysroot)))
  let mut pending : List Name := []
  for source in sources do
    let (imports, _, messages) ← Elab.parseImports (← IO.FS.readFile source) source
    if messages.hasErrors then
      throw (IO.userError s!"could not parse import header of {source}")
    pending := (imports.toList.map (·.module)) ++ pending
  let mut modules : Array SnapshotModule := #[]
  let mut visited : NameSet := {}
  while let name :: rest := pending do
    pending := rest
    if visited.contains name then
      continue
    visited := visited.insert name
    let path ← findOLean name
    let (data, _) ← readModuleData path
    pending := data.imports.toList.map (·.module) ++ pending
    modules := modules.push {
      name := name.toString
      relative := (modToFilePath (FilePath.mk ".") name "olean").toString
      object := path.toString
      imports := data.imports.map (·.module.toString)
      moduleSystem := data.isModule
    }
  IO.println (toJson modules).compress
