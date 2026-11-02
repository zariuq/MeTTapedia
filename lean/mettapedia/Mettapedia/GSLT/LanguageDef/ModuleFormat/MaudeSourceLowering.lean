import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSourceResolution
import Mettapedia.Languages.Maude.Syntax
import Mettapedia.Languages.Maude.DecidableEquality

/-! Maude declarations and commands lower into the existing independent IR.
Opaque identifiers may be allocated by a caller-provided symbol table; only
actual source declarations enter the signature. Source origins and authored
labels remain separate. An imported signature is an interface for elaboration,
not an implementation or an equational certificate for the imported module.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSourceLowering

open SourcePacket MaudeSourceResolution
open Mettapedia.Languages

structure OperatorBinding where
  id : String
  sourceName : String
  arguments : List String
  result : String
  deriving Repr, DecidableEq

def OperatorBinding.ofOperator (operator : Maude.Operator) : OperatorBinding :=
  ⟨operator.id, operator.sourceName, operator.arguments, operator.result⟩

structure Names where
  operators : List OperatorBinding := []
  equations : List String := []
  rules : List String := []

/-- This imports declarations only. Its equation theory must be supplied and
justified before the module can be admitted for execution. -/
structure ImportSignature where
  moduleName : String
  interfaceName : String
  signature : Maude.Signature

structure Settings where
  names : List (String × Names) := []
  imports : List ImportSignature := []

structure Origin where
  declaration : Nat
  position : Nat := 0
  label : Option String := none
  id : String
  deriving Repr, DecidableEq

inductive ModuleKind where
  | functional | system
  deriving Repr, DecidableEq, BEq

inductive ImportMode where
  | protecting | including | extending
  deriving Repr, DecidableEq, BEq

structure ImportDeclaration where
  moduleName : String
  interfaceName : String
  mode : ImportMode
  deriving Repr, DecidableEq

deriving instance DecidableEq for SurfaceOperator

structure SourceModule where
  kind : ModuleKind
  theory : Maude.Theory
  operators : List SurfaceOperator
  context : Maude.VariableContext
  operatorOrigins : List Origin
  equationOrigins : List Origin
  ruleOrigins : List Origin
  importInterfaces : List ImportDeclaration
  deriving Repr, DecidableEq

inductive CommandKind where
  | reduce | rewrite | searchStar | searchNormal | searchPlus | searchOne
  deriving Repr, BEq, DecidableEq

structure Command where
  kind : CommandKind
  moduleName : String
  context : Maude.VariableContext
  sort : String
  source : Maude.Term
  target : Option Maude.Term := none
  conditions : List Maude.Condition := []
  deriving Repr, DecidableEq

structure SourceFile where
  modules : List SourceModule
  commands : List Command
  deriving Repr, DecidableEq

private def binding (settings : Settings) (moduleName : String) : Names :=
  (settings.names.lookup moduleName).getD {}

private def allocate (names : Names) (moduleName sourceName : String)
    (arguments : List String) (result : String) (index position : Nat) : Lower String := do
  match names.operators.filter (fun op => op.sourceName == sourceName && op.arguments == arguments && op.result == result) with
  | [operator] => pure operator.id
  | [] => pure (moduleName ++ "/op/" ++ toString index ++ "/" ++ toString position)
  | _ => .error "ambiguous declaration-identifier allocation"

private def sourceNames (fuel : Nat) (source : Packet) : Lower (List String) := do
  (← series "maude-src:names" fuel source).mapM name

private def argumentSorts : Nat → Packet → Lower (List String)
  | 0, _ => .error "argument sorts exceed their packet size"
  | fuel + 1, source => do
      match ← view source with
      | ("maude-src:argument-sorts-empty", []) => pure []
      | ("maude-src:argument-sorts-more", [first, rest]) =>
          pure ((← name first) :: (← argumentSorts fuel rest))
      | _ => .error "malformed argument sorts"

structure PendingOperator where
  operator : SurfaceOperator
  identity : Option Packet
  origin : Origin

private def attributes (fuel : Nat) (source : Packet) :
    Lower (Maude.Attributes × Option Packet × Option Nat) := do
  let entries ← match ← view source with
    | ("maude-src:attributes-none", []) => pure []
    | ("maude-src:attributes-some", [entries]) => series "maude-src:attributes" fuel entries
    | _ => .error "malformed operator attributes"
  let mut result : Maude.Attributes := {}
  let mut identity := none
  let mut precedence := none
  for entry in entries do
    match ← view entry with
    | ("maude-src:attribute-ctor", []) => result := {result with constructor := true}
    | ("maude-src:attribute-assoc", []) => result := {result with associative := true}
    | ("maude-src:attribute-comm", []) => result := {result with commutative := true}
    | ("maude-src:attribute-id", [term]) =>
        if identity.isSome then .error "repeated identity attribute" else identity := some term
    | ("maude-src:attribute-prec", [digits]) =>
        if precedence.isSome then .error "repeated precedence attribute" else
          precedence := some (← requireSome "invalid operator precedence" (← text "SrcDigits" digits).toNat?)
    | (label, _) => .error s!"unsupported operator attribute {label}"
  pure (result, identity, precedence)

private def label (source : Packet) : Lower (Option String) := do
  match ← view source with
  | ("maude-src:label-none", []) => pure none
  | ("maude-src:label-some", [spelling]) => some <$> name spelling
  | _ => .error "malformed statement label"

private def pair (operators : List SurfaceOperator) (context : Maude.VariableContext)
    (left right : Packet) : Lower (Maude.Term × Maude.Term) := do
  let left ← terms operators context left
  let right ← terms operators context right
  let pairs := (left.flatMap fun first => right.filterMap fun second =>
    if first.sort == second.sort then some (first.term, second.term) else none).eraseDups
  match pairs with
  | [pair] => pure pair
  | [] => .error "equation sides have no common sorted interpretation"
  | _ => .error "ambiguous sorted equation; provide parentheses"

private def conditions (fuel : Nat) (operators : List SurfaceOperator) (context : Maude.VariableContext)
    (source : Packet) : Lower (List Maude.Condition) := do
  (← series "maude-src:conditions" fuel source).mapM fun source => do
    match ← view source with
    | ("maude-src:condition-equal", [left, right]) =>
        let (left, right) ← pair operators context left right
        pure ⟨left, right⟩
    | ("maude-src:condition-term", [term]) =>
        let left ← resolve operators context term (some "Bool")
        let choices := operators.filter fun op =>
          op.declaration.sourceName == "true" && op.declaration.arguments.isEmpty && op.declaration.result == "Bool"
        let [truth] := choices | .error "Boolean condition requires one declared true literal"
        pure ⟨left, .app truth.declaration.id []⟩
    | ("maude-src:condition-rewrite", _) => .error "rewrite conditions require the retained M1 reachability profile"
    | _ => .error "malformed condition"

private def statement (fuel : Nat) (operators : List SurfaceOperator) (context : Maude.VariableContext)
    (names : Names) (index declaration : Nat) (source : Packet) : Lower (Bool × Maude.Row × Origin) := do
  let (kind, fields) ← view source
  let (sourceLabel, left, right, guards) ← match fields with
    | [sourceLabel, left, right] => pure (sourceLabel, left, right, [])
    | [sourceLabel, left, right, guards] => do
        pure (sourceLabel, left, right, ← conditions fuel operators context guards)
    | _ => .error "malformed equation or rule"
  let sourceLabel ← label sourceLabel
  let isRule := kind == "maude-src:rl" || kind == "maude-src:crl"
  let id := ((if isRule then names.rules else names.equations)[index]?).getD
    (sourceLabel.getD ((if isRule then "rule:" else "equation:") ++ toString index))
  let (left, right) ← pair operators context left right
  let row : Maude.Row := ⟨id, context, guards, left, right⟩
  pure (isRule, {row with formals := row.usedContext}, ⟨declaration, 0, sourceLabel, id⟩)

private def module (fuel : Nat) (settings : Settings) (source : Packet) : Lower SourceModule := do
  let (kind, [moduleName, declarations]) ← view source | .error "expected a Maude module"
  unless kind == "maude-src:mod" || kind == "maude-src:fmod" do .error "expected a module declaration"
  let moduleName ← name moduleName
  let names := binding settings moduleName
  let declarations ← series "maude-src:declarations" fuel declarations
  let mut sorts := []
  let mut context : Maude.VariableContext := []
  let mut pending : List PendingOperator := []
  let mut interfaces := []
  for (source, index) in declarations.zipIdx do
    let (declarationKind, declarationFields) ← view source
    match (declarationKind, declarationFields) with
    | ("maude-src:sort", [entries]) | ("maude-src:sorts", [entries]) =>
        sorts := sorts ++ (← sourceNames fuel entries)
    | ("maude-src:var", [entries, sort]) | ("maude-src:vars", [entries, sort]) =>
        let sort ← name sort
        context := context ++ (← sourceNames fuel entries).map (·, sort)
    | ("maude-src:op", [entries, arguments, result, attrs])
    | ("maude-src:ops", [entries, arguments, result, attrs]) =>
        let entries ← sourceNames fuel entries
        let arguments ← argumentSorts fuel arguments
        let result ← name result
        let (attrs, identity, precedence) ← attributes fuel attrs
        for (sourceName, position) in entries.zipIdx do
          let id ← allocate names moduleName sourceName arguments result index position
          let holes := (sourceName.splitOn "_").length - 1
          unless holes == 0 || holes == arguments.length do .error "operator placeholders do not match its arity"
          let operator : Maude.Operator := ⟨id, sourceName, arguments, result, attrs⟩
          let precedence := if holes == 0 then 0 else
            precedence.getD (defaultPrecedence sourceName arguments.length)
          pending := pending ++ [⟨⟨operator, precedence⟩, identity, ⟨index, position, none, id⟩⟩]
    | ("maude-src:protecting", [imported]) | ("maude-src:including", [imported])
    | ("maude-src:extending", [imported]) =>
        let imported ← name imported
        let interface ← requireSome s!"import {imported} needs a declared signature interface"
          (settings.imports.find? (·.moduleName == imported))
        sorts := sorts ++ interface.signature.sorts
        let mode := if declarationKind == "maude-src:protecting" then ImportMode.protecting
          else if declarationKind == "maude-src:including" then ImportMode.including else ImportMode.extending
        interfaces := interfaces ++ [⟨imported, interface.interfaceName, mode⟩]
        for (declaration, position) in interface.signature.operators.zipIdx do
          let id ← allocate names moduleName declaration.sourceName declaration.arguments declaration.result index position
          let declaration := {declaration with id := id}
          pending := pending ++ [⟨⟨declaration, defaultPrecedence declaration.sourceName declaration.arguments.length⟩,
            none, ⟨index, position, some ("import:" ++ imported), id⟩⟩]
    | (label, _) =>
        unless ["maude-src:eq", "maude-src:ceq", "maude-src:rl", "maude-src:crl"].contains label do
          .error s!"unsupported declaration {label}"
  sorts := sorts.eraseDups
  unless (context.map (·.1)).eraseDups.length == context.length do .error "repeated module variable"
  unless context.all (fun entry => sorts.contains entry.2) do .error "variable has an undeclared sort"
  let initial := pending.map (·.operator)
  let mut operators := []
  for entry in pending do
    let identity ← entry.identity.mapM fun term => resolve initial [] term (some entry.operator.declaration.result)
    let declaration := {entry.operator.declaration with attributes := {entry.operator.declaration.attributes with
      identity := identity.or entry.operator.declaration.attributes.identity}}
    operators := operators ++ [{entry.operator with declaration := declaration}]
  let signature : Maude.Signature := ⟨sorts, operators.map (·.declaration)⟩
  unless signature.check do .error "invalid sorted operator signature or algebra attributes"
  let mut equations := []
  let mut rules := []
  let mut equationOrigins := []
  let mut ruleOrigins := []
  for (source, declaration) in declarations.zipIdx do
    let (label, _) ← view source
    if ["maude-src:eq", "maude-src:ceq", "maude-src:rl", "maude-src:crl"].contains label then
      let isRule := label == "maude-src:rl" || label == "maude-src:crl"
      let (_, row, origin) ← statement fuel operators context names
        (if isRule then rules.length else equations.length) declaration source
      unless row.check signature do .error "invalid sorted equation or rule"
      if isRule then
        rules := rules ++ [row]
        ruleOrigins := ruleOrigins ++ [origin]
      else
        equations := equations ++ [row]
        equationOrigins := equationOrigins ++ [origin]
  unless kind != "maude-src:fmod" || rules.isEmpty do .error "functional modules cannot contain rules"
  pure ⟨(if kind == "maude-src:fmod" then .functional else .system),
    ⟨moduleName, signature, equations, rules⟩, operators, context,
    pending.map (·.origin), equationOrigins, ruleOrigins, interfaces⟩

/-- Imported signature interfaces are not enough to admit executable modules. -/
def SourceModule.closedTheory (source : SourceModule) : Lower Maude.Theory :=
  if source.importInterfaces.isEmpty then pure source.theory
  else .error "imported equation theories and their certificates remain required"

private def command (fuel : Nat) (modules : List SourceModule) (source : Packet) : Lower Command := do
  let (kind, fields) ← view source
  let (moduleName, input, target, guards) ← match fields with
    | [moduleName, input] => pure (moduleName, input, none, none)
    | [moduleName, input, target, guards] => pure (moduleName, input, some target, some guards)
    | _ => .error "malformed Maude command"
  let selected ← match ← view moduleName with
    | ("maude-src:command-module-none", []) => requireSome "no current module" modules.getLast?
    | ("maude-src:command-module-some", [spelling]) => do
        let spelling ← name spelling
        requireSome "unknown command module" (modules.find? (·.theory.name == spelling))
    | _ => .error "malformed command module"
  let input ← resolve selected.operators selected.context input
  let sort ← requireSome "command term has no sort" (Maude.inferSort? selected.theory.signature selected.context input)
  let target ← target.mapM fun target => resolve selected.operators selected.context target (some sort)
  let guards ← guards.mapM fun guards => do
    match ← view guards with
    | ("maude-src:search-condition-none", []) => pure []
    | ("maude-src:search-condition-some", [guards]) => conditions fuel selected.operators selected.context guards
    | _ => .error "malformed search condition"
  let commandKind ← match kind with
    | "maude-src:red" | "maude-src:reduce" => pure CommandKind.reduce
    | "maude-src:rew" | "maude-src:rewrite" => pure CommandKind.rewrite
    | "maude-src:search=>*" => pure CommandKind.searchStar
    | "maude-src:search=>!" => pure CommandKind.searchNormal
    | "maude-src:search=>+" => pure CommandKind.searchPlus
    | "maude-src:search=>1" => pure CommandKind.searchOne
    | _ => .error "unsupported command"
  pure ⟨commandKind, selected.theory.name, selected.context, sort, input, target, guards.getD []⟩

def lower (input : String) (source : Packet) (settings : Settings := {}) : Lower SourceFile := do
  let grammar ← description
  unless validates grammar.grammar grammar.profile "SourceProgram" input source do
    .error "source packet readback differs from the complete original input"
  let ("maude-src:program", [body]) ← view source | .error "expected a Maude program"
  let fuel := packetNodes source + 1
  let entries ← series "maude-src:file" fuel body
  let mut modules : List SourceModule := []
  let mut commands : List Command := []
  for entry in entries do
    let (kind, _) ← view entry
    if kind == "maude-src:mod" || kind == "maude-src:fmod" then
      let elaborated ← module fuel settings entry
      unless !modules.any (fun old => old.theory.name == elaborated.theory.name) do .error "repeated source module name"
      modules := modules ++ [elaborated]
    else
      commands := commands ++ [← command fuel modules entry]
  pure ⟨modules, commands⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSourceLowering
