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

private structure ImportRequest where
  searchPath : String
  sourceOnly : List String
  sources : List String
  deriving FromJson

private def readJsonValue {α : Type} [FromJson α] (encoded : String) : IO α :=
  match Json.parse encoded >>= fromJson? with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def readRequest : List String → IO ImportRequest
  | ["--request", path] => do
    readJsonValue (← IO.FS.readFile path)
  | searchPath :: "--from-source" :: encoded :: sources => do
    pure ⟨searchPath, ← readJsonValue encoded, sources⟩
  | searchPath :: sources => pure ⟨searchPath, [], sources⟩
  | [] => throw (IO.userError "expected an import search path and Lean source files")

/-- Read the same import headers and compiled import names that Lean uses. -/
def main (args : List String) : IO Unit := do
  let request ← readRequest args
  let sourceOnly := request.sourceOnly.foldl (fun (names : NameSet) name => names.insert name.toName) {}
  let roots := if request.searchPath.isEmpty then [] else SearchPath.parse request.searchPath
  searchPathRef.set (roots ++ (← getBuiltinSearchPath (← findSysroot)))
  let mut pending : List (Name × String) := []
  for source in request.sources do
    let (imports, _, messages) ← Elab.parseImports (← IO.FS.readFile source) source
    if messages.hasErrors then
      throw (IO.userError s!"could not parse import header of {source}")
    pending := (imports.toList.map fun imported => (imported.module, source)) ++ pending
  let mut modules : Array SnapshotModule := #[]
  let mut visited : NameSet := {}
  while let (name, importer) :: rest := pending do
    pending := rest
    if visited.contains name || sourceOnly.contains name then
      continue
    visited := visited.insert name

    let (path, data) ← try
      let path ← findOLean name
      let (data, _) ← readModuleData path
      pure (path, data)
    catch error =>
      throw (IO.userError s!"{importer} imports {name}: {error}")
    let importerName := name.toString
    pending := (data.imports.toList.map fun imported => (imported.module, importerName)) ++ pending
    modules := modules.push {
      name := importerName
      relative := (modToFilePath (FilePath.mk ".") name "olean").toString
      object := path.toString
      imports := data.imports.map (·.module.toString)
      moduleSystem := data.isModule
    }
  IO.println (toJson modules).compress
