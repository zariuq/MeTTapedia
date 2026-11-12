import Lean
import Lean.Elab.Import

/-!
# Pinned upstream semantic definitions

This build adapter elaborates an upstream Lean source file after checking its
exact digest. Its definitions and proofs are checked by the ordinary kernel.
The adapter is not imported by the portable resource semantics. Qualification
re-elaborates clients, since the external source is not a Lake dependency.
-/

set_option autoImplicit false

open Lean Elab Command

private def loadPinnedCommands (filename digest : String)
    (expectedImports : Array Name) : CommandElabM Unit := do
  let hash ← IO.Process.output { cmd := "sha256sum", args := #[filename] }
  unless hash.exitCode == 0 && hash.stdout.startsWith (digest ++ " ") do
    throwError "architecture model source digest mismatch"
  let source ← IO.FS.readFile filename
  let context := Parser.mkInputContext source filename
  let (header, initialCursor, headerMessages) ← Parser.parseHeader context
  if headerMessages.hasErrors || HeaderSyntax.isModule header then
    throwError "unsupported architecture model source header"
  let dependencies := HeaderSyntax.imports header false
  unless dependencies.map (·.module) == expectedImports &&
      dependencies.all (fun dependency => !dependency.isMeta && !dependency.importAll) do
    throwError "architecture model source imports differ from the declared dependency list"
  let complete ← withReader (fun reader => { reader with fileName := filename, fileMap := context.fileMap }) do
    let mut cursor := initialCursor
    for _ in [0:source.utf8ByteSize + 1] do
      let scope ← getScope
      let parseContext : Parser.ParserModuleContext := {
        env := ← getEnv
        options := ← getOptions
        currNamespace := scope.currNamespace
        openDecls := scope.openDecls }
      let (command, next, messages) := Parser.parseCommand context parseContext cursor {}
      if messages.hasErrors then throwError "architecture model source parse failed"
      if command.isOfKind ``Parser.Command.eoi then return true
      if Parser.isTerminalCommand command then
        throwError "architecture model source contains an import or early exit"
      unless next.pos.byteIdx > cursor.pos.byteIdx do
        throwError "architecture model source parser made no progress"
      elabCommand command
      if (← get).messages.hasErrors then throwError "architecture model source elaboration failed"
      cursor := next
    pure false
  unless complete do throwError "architecture model source did not terminate"

elab "tisa_model_source% " path:str " sha256 " digest:str : command =>
  loadPinnedCommands path.getString digest.getString #[]

/-- Headers are checked; file-local openings and EOF namespace closure do not leak. -/
elab "tisa_model_file% " path:str " sha256 " digest:str
    " imports " "[" dependencies:ident,* "]" : command => do
  withScope (fun scope => { scope with openDecls := [] }) do
    loadPinnedCommands path.getString digest.getString (dependencies.getElems.map (·.getId))
