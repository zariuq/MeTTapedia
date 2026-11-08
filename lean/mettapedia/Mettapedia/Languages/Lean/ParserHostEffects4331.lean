import Mettapedia.Languages.Lean.LeanSyntaxReadback4331
import Mettapedia.Languages.Lean.ParserDescriptorProgress
import Mettapedia.Languages.Lean.FrontendReplay4331

/-!
# Host elaboration boundary for declarative grammar effects

The source command syntax comes from GSLT readback. Lean executes its existing
declaration elaborator and supplies the resulting ParserDescr value. The
portable source and compiled grammar states are then advanced by explicit
effects. No source fragment is parsed to obtain those effects here.
-/

namespace Mettapedia.Languages.Lean.ParserHostEffects4331

open _root_.Lean _root_.Lean.Elab
open Mettapedia.GSLT.Parsing
open ParserRegistrationCompiler

structure State where
  host : Command.State
  source : SourceState
  target : TargetState
  coherent : compileState LeanSyntaxBootstrap.bindings source = target
  baseTokens : List String
  mainModule : _root_.Lean.Name
  imports : Array _root_.Lean.Name := #[`Lean]
  imported : List (ScopedGrammarState.Entry ParserDescription.Name Registration) := []
  canImport : Bool := true

def initial (mainModule : _root_.Lean.Name) : IO State := do
  unless ParserAdapter4331.hostSupported do throw (IO.userError "unqualified Lean parser release")
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Lean }] {} (leakEnv := true) (loadExts := true)
  let env := env.setMainModule mainModule
  let source : SourceState := ScopedGrammarState.initial []
  return {
    host := Command.mkState env {} {}
    source
    target := compileState LeanSyntaxBootstrap.bindings source
    coherent := rfl
    baseTokens := (Parser.getTokenTable env).values.toList
    mainModule }

def advance (state : State) (effects : List Effect) (host : Command.State) : State :=
  { state with
    host
    source := effects.foldl (fun current effect => sourceEffect effect current) state.source
    target := effects.foldl (fun current effect => targetEffect LeanSyntaxBootstrap.bindings effect current) state.target
    coherent := by rw [effects_commute, state.coherent] }

def categoryNames (env : Environment) (category : _root_.Lean.Name) : List _root_.Lean.Name :=
  match Parser.getParserCategory? env category with
  | none => []
  | some info => info.kinds.toList.map Prod.fst

def descriptor (env : Environment) (options : Options) (name : _root_.Lean.Name) : IO ParserDescr := do
  let some info := env.find? name | throw (IO.userError "registered parser declaration is absent")
  match info.type with
  | .const `Lean.ParserDescr _ | .const `Lean.TrailingParserDescr _ =>
      unsafe IO.ofExcept (env.evalConst ParserDescr options name)
  | _ => throw (IO.userError ("executable parser boundary: " ++ name.toString))

def elaborate (state : State) (syntaxTree : Syntax) (input : String) : IO Command.State := do
  let context : Frontend.Context := { inputCtx := Parser.mkInputContext input "<gslt-command>" }
  let initial : Frontend.State := { commandState := state.host, parserState := {}, cmdPos := 0 }
  let (_, result) ← (Frontend.elabCommandAtFrontend syntaxTree context).run initial
  FrontendReplay4331.requireNoErrors "grammar declaration elaboration" result.commandState.messages
  return result.commandState

def scope (host : Command.State) : IO Command.Scope :=
  match host.scopes.head? with
  | some value => pure value
  | none => throw (IO.userError "missing host command scope")

def registration (env : Environment) (options : Options) (baseTokens : List String)
    (category name : _root_.Lean.Name) (priority : Nat) : IO Registration := do
  unless category == `term do throw (IO.userError ("parser category boundary: " ++ category.toString))
  let value ← descriptor env options name
  let exported := ParserAdapter4331.exportDescription value
  let some info := ParserRegistrationCompiler.header exported
    | throw (IO.userError "unsupported parser descriptor header")
  unless ParserDescriptorProgress.tokenLed info.body do
    throw (IO.userError "parser body has no admitted token-led progress witness")
  if let some token := ParserDescriptorProgress.firstToken info.body then
    if baseTokens.contains token then
      throw (IO.userError ("existing host-token parser is outside the fresh-extension profile: " ++ token))
  let some _ := ParserDescriptorLowering.lower LeanSyntaxBootstrap.bindings info.body
    | throw (IO.userError ("unsupported parser body: " ++ reprStr info.body))
  return ⟨ParserAdapter4331.exportName category, ParserAdapter4331.exportName name, priority, exported⟩

def loadModule (state : State) (name : _root_.Lean.Name) : IO State := do
  unless state.canImport do throw (IO.userError "import after a non-header command")
  if state.imports.contains name then return state
  let imports := state.imports.push name
  unsafe enableInitializersExecution
  let env ← importModules (imports.map fun name => { module := name }) {} (leakEnv := true) (loadExts := true)
  let env := env.setMainModule state.mainModule
  let mut imported := state.imported
  let mut tokenEntries : List (Option ParserDescription.Name × String) := []
  for moduleName in env.header.moduleNames do
    if state.host.env.getModuleIdx? moduleName |>.isSome then continue
    let some index := env.getModuleIdx? moduleName | throw (IO.userError "imported module has no index")
    for update in Parser.parserExtension.ext.getModuleEntries env index do
      match update with
      | .global (.parser category declaration priority) =>
          imported := imported ++ [.global (← registration env {} state.baseTokens category declaration priority)]
      | .scoped scopeName (.parser category declaration priority) =>
          imported := imported ++ [.scoped (ParserAdapter4331.exportName scopeName)
            (← registration env {} state.baseTokens category declaration priority)]
      | .global (.kind _) | .scoped _ (.kind _) => pure ()
      | .global (.token token) => tokenEntries := tokenEntries ++ [(none, token)]
      | .scoped scopeName (.token token) =>
          tokenEntries := tokenEntries ++ [(some (ParserAdapter4331.exportName scopeName), token)]
      | _ => throw (IO.userError "imported non-parser grammar entry needs a declared translation")
  -- Lean exports a token entry alongside each declarative parser. The compiled
  -- descriptor already contributes that token, in the same registration scope.
  -- Standalone token registrations are a separate, explicitly refused profile.
  for (scopeName, token) in tokenEntries do
    unless imported.any (fun entry => match entry with
      | .global rule => scopeName.isNone && (ParserRegistrationCompiler.tokens rule.descriptor).contains token
      | .scoped name rule => scopeName == some name && (ParserRegistrationCompiler.tokens rule.descriptor).contains token) do
      throw (IO.userError ("imported standalone token needs a declared translation: " ++ token))
  let source := ScopedGrammarState.imports id sourceAdd [] imported
  let target := ScopedGrammarState.imports id targetAdd (compileTable LeanSyntaxBootstrap.bindings [])
    (imported.map (ScopedGrammarTranslation.entry (compileEntry LeanSyntaxBootstrap.bindings)))
  return { state with
    host := Command.mkState env {} {}
    imports
    imported
    source
    target
    coherent := compile_imports LeanSyntaxBootstrap.bindings [] imported }

def declared (state : State) (host : Command.State) (header : LeanSyntaxReadback4331.Header)
    (category : _root_.Lean.Name) : IO (List Effect) := do
  let old := categoryNames state.host.env category
  let fresh := (categoryNames host.env category).filter (!old.contains ·)
  unless fresh.length == 1 do
    throw (IO.userError s!"declaration installed {fresh.length} parsers; expected one named descriptor")
  let name := fresh[0]!
  let current ← scope host
  let priority : Nat ← match header.priority with
    | none => pure 1000
    | some text => match text.toNat? with
      | some value => pure value
      | none => throw (IO.userError "non-numeric parser priority")
  let registration ← registration host.env current.opts state.baseTokens category name priority
  return [match header.scopeKind with
    | .global => .registration (.global registration)
    | .local => .localRule registration
    | .scoped => .registration (.scoped (ParserAdapter4331.exportName current.currNamespace) registration)]

def applyCommand (state : State) (command : LeanSyntaxReadback4331.Command)
    (syntaxTree : Syntax) (input : String) : IO State := do
  match command with
  | .check _ => return { state with canImport := false }
  | .existing (.import_ name) => return ← loadModule state name.toName
  | _ => pure ()
  let host ← elaborate state syntaxTree input
  let effects : List Effect ← match command with
    | .mixfix header .. | .notation_ header .. => declared state host header `term
    | .syntax_ header _ category => do
        if category != "term" then throw (IO.userError "this frontend profile admits term extensions")
        declared state host header category.toName
    | .existing (.namespace_ _) => do
        let count := host.scopes.length - state.host.scopes.length
        let fresh := (host.scopes.take count).reverse
        let mut effects : List Effect := []
        for current in fresh do
          effects := effects ++ [.push, .activate true (ParserAdapter4331.exportName current.currNamespace)]
        pure (effects ++ [.delimit (count - 1)])
    | .existing (.section_ _) => pure [.push]
    | .existing (.end_ _) => pure (List.replicate (state.host.scopes.length - host.scopes.length) .pop)
    | .existing (.open_ _ names) => do
        let current ← scope state.host
        let mut effects : List Effect := []
        for name in names do
          for resolved in ResolveName.resolveNamespace state.host.env current.currNamespace current.openDecls name.toName do
            effects := effects ++ [.activate true (ParserAdapter4331.exportName resolved)]
        pure effects
    | _ => throw (IO.userError "unsupported command effect")
  return { advance state effects host with canImport := false }

end Mettapedia.Languages.Lean.ParserHostEffects4331
