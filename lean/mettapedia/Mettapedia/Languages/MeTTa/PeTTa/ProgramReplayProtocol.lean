import Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay
import Lean.Data.Json

/-!
# Authored program replay protocol

Both replay clients use this source reader, closed read-only profile and exact
structural observation encoding. Evaluation policy belongs to each client.

Program files, JSON decoding and source reading are host boundaries. The finite
state encoding covers only the checked read-only store; `ProgramReplay` proves
its reconstruction. Unknown constructor heads retain the evaluator's data
interpretation. This profile alone does not certify native operation registries
or native parser agreement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ProgramReplayProtocol

open Lean
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.PeTTa.Eval

mutual
  def atomJson : Atom → Json
    | .symbol value => Json.mkObj [("kind", .str "symbol"), ("value", .str value)]
    | .var value => Json.mkObj [("kind", .str "variable"), ("value", .str value)]
    | .grounded (.int value) => Json.mkObj [("kind", .str "number"), ("value", toJson value)]
    | .grounded (.bool value) => Json.mkObj [("kind", .str "boolean"), ("value", toJson value)]
    | .grounded (.string value) => Json.mkObj [("kind", .str "string"), ("value", .str value)]
    | .grounded (.custom name value) => Json.mkObj [
        ("kind", .str "custom"), ("type", .str name), ("value", .str value)]
    | .expression items => Json.mkObj [("kind", .str "expression"), ("items", toJson (atomsJson items))]

  def atomsJson : List Atom → List Json
    | [] => []
    | first :: rest => atomJson first :: atomsJson rest
end

mutual
  def atomString : Atom → String
    | .symbol value => value
    | .var name => "$" ++ name
    | .grounded (.int value) => toString value
    | .grounded (.bool value) => if value then "true" else "false"
    | .grounded (.string value) => (Json.str value).compress
    | .grounded (.custom name value) => "(" ++ name ++ " " ++ (Json.str value).compress ++ ")"
    | .expression items => "(" ++ " ".intercalate (atomsString items) ++ ")"

  def atomsString : List Atom → List String
    | [] => []
    | first :: rest => atomString first :: atomsString rest
end

def bindingsJson (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) : Json :=
  toJson (bindings.map fun (name, value) =>
    Json.mkObj [("name", .str name), ("value", atomJson value)])

def targetJson : Target → Json
  | .data => Json.mkObj [("kind", .str "data")]
  | .function head => Json.mkObj [("kind", .str "function"), ("head", .str head)]

def faultJson : Effects.Fault → Json
  | .invalidSpace => Json.mkObj [("kind", .str "invalidSpace")]
  | .missingCell name => Json.mkObj [("kind", .str "missingCell"), ("name", .str name)]
  | .invalidArguments head => Json.mkObj [("kind", .str "invalidArguments"), ("head", .str head)]
  | .zeroDivisor => Json.mkObj [("kind", .str "zeroDivisor")]
  | .overApplication head arities count => Json.mkObj [("kind", .str "overApplication"),
      ("head", .str head), ("arities", toJson arities), ("count", toJson count)]

def casesJson (cases : SpaceSemantics.Cases) : Json :=
  toJson (cases.map fun (pattern, body) =>
    Json.mkObj [("pattern", atomJson pattern), ("body", atomJson body)])

def stateJson (state : Effects.State) : Json :=
  Json.mkObj [
    ("core", toJson (atomsJson state.core)), ("next", toJson state.next),
    ("spaces", toJson (state.spacesPrefix.map fun rows => toJson (atomsJson rows))),
    ("unallocated_spaces", toJson ([] : List Json)),
    ("cells", toJson ([] : List Json)), ("absent_cells", Json.null)]

private def fields (request : Json) : Except String Unit := do
  let object ← request.getObj?
  let required := ["program_path", "expression", "fuel_chunks"]
  for (key, _) in object.toList do
    unless (required ++ ["input"]).contains key do throw s!"unexpected field '{key}'"
  for key in required do
    let _ ← request.getObjVal? key

/-- The general JSON reader stores objects as maps. This total lexical check
retains top-level key occurrences so repeated keys cannot be silently replaced. -/
def uniqueKeys (text : String) : Except String Unit := do
  let mut depth := 0
  let mut quoted := false
  let mut escaped := false
  let mut keyExpected := false
  let mut readingKey := false
  let mut token := ""
  let mut keys : List String := []
  for character in text.toList do
    if quoted then
      if readingKey then token := token.push character
      if escaped then escaped := false
      else if character == '\\' then escaped := true
      else if character == '"' then
        quoted := false
        if readingKey then
          let key ← (← Json.parse token).getStr?
          if keys.contains key then throw s!"duplicate field '{key}'"
          keys := key :: keys
          readingKey := false
    else if character == '"' then
      quoted := true
      readingKey := depth == 1 && keyExpected
      if readingKey then token := "\""
    else if character == '{' || character == '[' then
      depth := depth + 1
      if depth == 1 && character == '{' then keyExpected := true
    else if character == '}' || character == ']' then depth := depth - 1
    else if depth == 1 && character == ',' then keyExpected := true
    else if depth == 1 && character == ':' then keyExpected := false

private def readOne (source : String) : Except String Atom := do
  if source.trimAscii.toString.startsWith "!" then
    throw "expressions must not have a top-level request marker"
  match ← SpaceSemantics.readSource source with
  | [expression] => return expression
  | _ => throw "expected exactly one source expression"

mutual
  private def variableNames : Atom → List String
    | .var name => [name]
    | .expression items => variableNamesList items
    | _ => []
  private def variableNamesList : List Atom → List String
    | [] => []
    | first :: rest => variableNames first ++ variableNamesList rest
end

private def symbolProfile (symbol : String) : Except String Unit := do
  let characters := symbol.toList
  let unsigned := match characters with
    | '+' :: rest | '-' :: rest => rest
    | _ => characters
  let numericStart := match unsigned with
    | first :: _ => first.isDigit || first == '.'
    | [] => false
  if numericStart && symbol.contains '.' && characters.any Char.isDigit then
    throw s!"numeric-looking dotted lexeme '{symbol}' is outside the integer reader profile"
  match Json.parse symbol with
  | .ok (.num _) => throw s!"numeric lexeme '{symbol}' is outside the integer reader profile"
  | _ => return ()

mutual
  private def literalProfile : Atom → Except String Unit
    | .symbol name => symbolProfile name
    | .grounded (.custom _ _) => .error "custom grounded values are outside the source profile"
    | .expression items => literalProfiles items
    | _ => .ok ()

  private def literalProfiles : List Atom → Except String Unit
    | [] => .ok ()
    | first :: rest => do
        literalProfile first
        literalProfiles rest
end

private def patternProfile (program : SpaceSemantics.Program) (pattern : Atom) : Except String Unit := do
  unless passivePattern program pattern do throw "computed patterns are outside the passive-pattern profile"

private def controlHead (head : String) : Bool :=
  head ∈ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]

mutual
  private def closedExpression (program : SpaceSemantics.Program) (bound : List String) :
      Atom → Except String Unit
    | .var name =>
        if bound.contains name then .ok () else .error s!"free variable '${name}' is outside the closed profile"
    | .symbol name => symbolProfile name
    | .grounded (.custom _ _) => .error "custom grounded values are outside the source profile"
    | .grounded _ => .ok ()
    | .expression [.symbol "let", pattern, value, body] => do
        patternProfile program pattern
        closedExpression program bound value
        closedExpression program (variableNames pattern ++ bound) body
    | .expression [.symbol "let*", .expression pairs, body] => do
        unless (nestedLets pairs body).isSome do throw "malformed let* pairs"
        closedLets program bound pairs body
    | .expression [.symbol "case", value, .expression rows] => do
        closedExpression program bound value
        closedCases program bound rows
    | .expression [.symbol "if", condition, yes, no] => do
        closedExpression program bound condition
        closedExpression program bound yes
        closedExpression program bound no
    | .expression [.symbol "superpose", .expression alternatives] =>
        closedExpressions program bound alternatives
    | .expression [.symbol "collapse", expression] | .expression [.symbol "quote", expression] =>
        closedExpression program bound expression
    | .expression [.symbol "empty"] => pure ()
    | .expression (.symbol head :: arguments) => do
        if controlHead head then throw s!"unsupported shape for control '{head}'"
        if head ∈ ["get-state", "get-atoms", "match"] then
          throw s!"space/cell service '{head}' is outside this replay profile"
        if program.equations.any (·.head == head) then
          unless program.equations.any (fun equation => equation.head == head &&
              equation.arguments.length == arguments.length) do
            throw s!"unsaturated authored call '{head}'"
        closedExpressions program bound (.symbol head :: arguments)
    | .expression (.var _ :: _) => .error "variable application heads are outside this replay profile"
    | .expression items => closedExpressions program bound items
  termination_by expression => sizeOf expression
  decreasing_by all_goals simp_wf; all_goals omega

  private def closedExpressions (program : SpaceSemantics.Program) (bound : List String) :
      List Atom → Except String Unit
    | [] => .ok ()
    | first :: rest => do
        closedExpression program bound first
        closedExpressions program bound rest
  termination_by items => sizeOf items
  decreasing_by all_goals simp_wf; all_goals omega

  private def closedLets (program : SpaceSemantics.Program) (bound : List String) :
      List Atom → Atom → Except String Unit
    | [], body => closedExpression program bound body
    | .expression [pattern, value] :: rest, body => do
        patternProfile program pattern
        closedExpression program bound value
        closedLets program (variableNames pattern ++ bound) rest body
    | _, _ => .error "malformed let* pairs"
  termination_by pairs body => sizeOf pairs + sizeOf body
  decreasing_by all_goals simp_wf; all_goals omega

  private def closedCases (program : SpaceSemantics.Program) (bound : List String) :
      List Atom → Except String Unit
    | [] => .ok ()
    | .expression [pattern, body] :: rest => do
        patternProfile program pattern
        closedExpression program (variableNames pattern ++ bound) body
        closedCases program bound rest
    | _ => .error "malformed case rows"
  termination_by rows => sizeOf rows
  decreasing_by all_goals simp_wf; all_goals omega
end

private def checkedProgram (program : SpaceSemantics.Program) : Except String Unit := do
  unless program.initializers.isEmpty do throw "program request initializers are outside expression-request mode"
  unless ProgramReplay.readOnlyProgram program do throw "program contains mutable or dynamic operations"
  unless constructorPatterns program do throw "program has a computed pattern"
  literalProfiles (SpaceSemantics.loadedAtoms program)
  for equation in program.equations do
    if ioHead equation.head || StdLib.known equation.head || controlHead equation.head then
      throw s!"authored intrinsic head '{equation.head}' is outside this profile"
    closedExpression program (variableNamesList equation.arguments) equation.body
  for declaration in program.declarations do
    match declaration with
    | .expression [.symbol ":", _, .expression (.symbol "->" :: types)] =>
        unless !(types.dropLast.any (· == .symbol "Atom")) do
          throw "raw Atom formals are outside the eager replay profile"
    | _ => pure ()
  for fact in program.facts do
    if !(variableNames fact).isEmpty then throw "open stored facts are outside the ground profile"
    match fact with
    | .expression (.symbol head :: _) =>
        if head == "=" || head == ":" then throw "malformed equation or declaration"
    | _ => pure ()

private def naturalChunks (request : Json) : Except String (List Nat) := do
  let items ← (← request.getObjVal? "fuel_chunks").getArr?
  if items.isEmpty then throw "fuel_chunks must be nonempty"
  items.toList.mapM fun item => item.getNat?.mapError (fun _ => "fuel_chunks must contain natural numbers")

private def inputValues (request : Json) : Except String (List Atom) := do
  let object ← request.getObj?
  if object.contains "input" then
    let items ← (← request.getObjVal? "input").getArr?
    items.toList.mapM fun item => do
      let value ← readOne (← item.getStr?)
      unless (variableNames value).isEmpty do throw "input values must be ground"
      literalProfile value
      return value
  else return []

/-- A checked request retains its authored program and full chunk population. -/
structure Request where
  program : SpaceSemantics.Program
  expression : Atom
  fuels : List Nat
  input : List Atom

/-- Load the declared source profile without choosing an evaluation policy. -/
def load (request : Json) : IO Request := do
  let parsed ← match (do
      fields request
      let path ← (← request.getObjVal? "program_path").getStr?
      if path.isEmpty then throw "program_path must be nonempty"
      let expression ← readOne (← (← request.getObjVal? "expression").getStr?)
      let fuels ← naturalChunks request
      let input ← inputValues request
      pure (path, expression, fuels, input) : Except String (String × Atom × List Nat × List Atom)) with
    | .error message => throw (IO.userError message)
    | .ok parsed => pure parsed
  let (path, expression, fuels, input) := parsed
  let source ← IO.FS.readFile path
  let program ← match (do
      let program ← SpaceSemantics.readProgram source
      checkedProgram program
      unless codeWithin ProgramReplay.readOnlyHead expression do
        throw "request contains mutable or dynamic operations"
      closedExpression program [] expression
      pure program : Except String SpaceSemantics.Program) with
    | .error message => throw (IO.userError message)
    | .ok program => pure program
  return ⟨program, expression, fuels, input⟩

end Mettapedia.Languages.MeTTa.PeTTa.ProgramReplayProtocol
