import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

/-! File loading reuses the existing module parser and elaborator. Imports are
loaded in dependency order. Cycles and conflicting module names are diagnosed
before a dependent module is elaborated. -/

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.Loader

open Lean Elab Command
open Commands

private partial def load (path : System.FilePath) (active : List String)
    (loaded : List (String × Name)) : CommandElabM (Name × List (String × Name)) := do
  let resolved ← IO.FS.realPath path
  let key := resolved.toString
  if let some name := loaded.lookup key then return (name,loaded)
  if active.contains key then throwError "cyclic module import: {key}"
  let text ← IO.FS.readFile resolved
  activateScoped `Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
  activateScoped `Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
  let .ok parsed := Parser.runParserCategory (← getEnv) `moduleFile (stripBlockComments text) key
    | throwError "module parser refused {key}"
  let moduleSyntax : TSyntax `moduleFile := ⟨parsed⟩
  let `(moduleFile| $imports:moduleImport* Module $name:ident { $_theories:moduleTheory* $[$_entry:moduleEntry]? }) := moduleSyntax
    | throwError "invalid module declaration in {key}"
  if loaded.any (fun entry => entry.2 == name.getId) then
    throwError "conflicting module name {name.getId} in {key}"
  let mut current := loaded
  for declaration in imports do
    let `(moduleImport| import $file:str as $_qualifier:ident) := declaration
      | throwError "invalid module import in {key}"
    let child := resolved.parent.getD "." / file.getString
    let (childName,next) ← load child (key :: active) current
    let expected := Name.mkSimple ((file.getString.splitOn "/").getLast!.replace ".module" "")
    unless childName == expected do
      throwError "import {file.getString} declares {childName}; the existing module format expects {expected}"
    current := next
  elabModuleFile moduleSyntax
  pure (name.getId,(key,name.getId) :: current)

syntax (name := moduleTreeCommand) "#module_tree " str " as " ident : command

@[command_elab moduleTreeCommand] def elabModuleTree : CommandElab := fun stx => do
  let `(command| #module_tree $file:str as $exportId:ident) := stx | throwUnsupportedSyntax
  let source := System.FilePath.mk (← getFileName)
  let (name,_) ← load (source.parent.getD "." / file.getString) [] []
  let currentNamespace ← getCurrNamespace
  for field in [`module, `library, `language] do
    let target := mkIdent (exportId.getId ++ field)
    let value := mkIdent (currentNamespace ++ name ++ field)
    elabCommand (← `(def $target := $value))

end Mettapedia.GSLT.LanguageDef.ModuleSource.Loader
