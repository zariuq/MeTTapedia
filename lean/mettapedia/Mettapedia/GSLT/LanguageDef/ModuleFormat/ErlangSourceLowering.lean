import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketView
import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntax
import Mettapedia.Languages.Erlang.Assembly
import Mettapedia.Languages.Erlang.Scope

/-! Textual Core Erlang entry compilation. The selected grammar packet is
read back before names are resolved into the independent code arena. An
explicit exported entry determines a transitive set of function definitions;
unsupported reachable operations are refused. Entry specialization and
source-to-code correspondence remain separate proof obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangSourceLowering

open Mettapedia.Languages.Erlang
open SourcePacket
open SourcePacketView (requireSome)
abbrev Lower := Except String
abbrev Datum := Mettapedia.Languages.Erlang.Value

private def description : Lower Portable.SyntaxDescription :=
  requireSome "Core Erlang syntax description is unavailable" GoldCoreSyntax.Erlang.description?

private def text (sort : String) (source : Packet) : Lower String :=
  SourcePacketView.text description sort source

private def keepField : Mettapedia.OSLF.MeTTaIL.Syntax.TermParam → Bool
    | .simple _ (.base "SrcTrivia") | .simple _ (.base "SrcSpacing")
    | .simple _ (.base "ErAnnotation") => false
    | _ => true

private def view (source : Packet) : Lower (String × List Packet) :=
  SourcePacketView.view description keepField source

private def series (family : String) : Nat → Packet → Lower (List Packet) :=
  SourcePacketView.series view family

private def escapedChars : List Char → Lower (List Char)
  | [] => pure []
  | '\\' :: next :: rest => do
      let character ← match next with
        | 'n' => pure '\n' | 'r' => pure '\r' | 't' => pure '\t'
        | 'b' => pure (Char.ofNat 8) | 'f' => pure (Char.ofNat 12)
        | 'v' => pure (Char.ofNat 11) | 'e' => pure (Char.ofNat 27)
        | 's' => pure ' ' | '\\' => pure '\\' | '\'' => pure '\'' | '"' => pure '"'
        | _ => .error "escape requires an additional literal profile"
      pure (character :: (← escapedChars rest))
  | ['\\'] => .error "unfinished escape"
  | first :: rest => (first :: ·) <$> escapedChars rest

private def quoted (sort : String) (source : Packet) : Lower String := do
  let spelling ← text sort source
  pure (String.ofList (← escapedChars (spelling.toList.drop 1 |>.dropLast)))

inductive Name where
  | variable (spelling : String)
  | function (spelling : String) (arity : Nat)
  | receiveLoop | receiveFlag | receiveMessage
  deriving Repr, DecidableEq, BEq

private def functionName : Nat → Packet → Lower Name
  | 0, _ => .error "function name exceeds its packet size"
  | fuel + 1, source => do
      match ← view source with
      | ("core-erlang-src:function-name", [name, arity]) =>
          let arity ← requireSome "invalid function arity" (← text "SrcDigits" arity).toNat?
          pure (.function (← quoted "SrcQuotedAtom" name) arity)
      | (_, [child]) => functionName fuel child
      | _ => .error "malformed function name"

private def variableName : Nat → Packet → Lower String
  | 0, _ => .error "variable exceeds its packet size"
  | fuel + 1, source => do
      match ← view source with
      | ("core-erlang-src:variable", [name]) => text "SrcVariableName" name
      | ("core-erlang-src:variable-annotated", [child]) => variableName fuel child
      | _ => .error "malformed variable"

abbrev Context := List Name

private def extendNames (context : Context) (names : List Name) : Context := names.reverse ++ context

private def distinct {α : Type} [BEq α] (names : List α) : Bool := names.eraseDups.length == names.length

private def lookup (context : Context) (name : Name) : Lower Assembly.Expression := do
  let index ← requireSome s!"unbound name {reprStr name}" (context.idxOf? name)
  pure (Assembly.variableRef index)

private def unwrap : Nat → Packet → Lower Packet
  | 0, _ => .error "source wrappers exceed their packet size"
  | fuel + 1, source => do
      let (label, fields) ← view source
      match label, fields with
      | "core-erlang-src:expr-raw", [child] | "core-erlang-src:expr-single", [child]
      | "core-erlang-src:single-raw", [child] | "core-erlang-src:single-annotated", [child]
      | "core-erlang-src:expr-annotated", [child] | "core-erlang-src:expr-literal", [child]
      | "core-erlang-src:literal-raw", [child] | "core-erlang-src:literal-atomic", [child]
      | "core-erlang-src:literal-annotated", [child] | "core-erlang-src:expr-fun", [child]
      | "core-erlang-src:function-body", [child] | "core-erlang-src:function-body-annotated", [child]
      | "core-erlang-src:pattern-raw", [child] | "core-erlang-src:pattern-annotated", [child]
      | "core-erlang-src:pattern-literal", [child] | "core-erlang-src:clause-annotated", [child]
      | "core-erlang-src:module-annotated", [child] => unwrap fuel child
      | _, _ => pure source

private def atomic : Packet → Lower Literal := fun source => do
  match ← view source with
  | ("core-erlang-src:integer", [number]) =>
      pure (.integer (← requireSome "invalid integer" (← text "SrcInteger" number).toInt?))
  | ("core-erlang-src:atom", [name]) => pure (.atom (← quoted "SrcQuotedAtom" name))
  | ("core-erlang-src:literal-empty-list", []) => pure .nil
  | _ => .error "expected atomic Core literal"

private def atomName (fuel : Nat) (source : Packet) : Lower String := do
  let .atom name ← atomic (← unwrap fuel source) | .error "expected a literal atom"
  pure name

private def patternFuel : Nat → Packet → Lower (MatchPattern × List Name)
  | 0, _ => .error "pattern exceeds its packet size"
  | fuel + 1, source => do
      let source ← unwrap fuel source
      let (label, fields) ← view source
      let lower := patternFuel fuel
      let result ← match label, fields with
        | "core-erlang-src:pattern-variable", [identifier] => do
            let name ← variableName fuel identifier
            pure (MatchPattern.bind, [Name.variable name])
        | "core-erlang-src:pattern-alias", [identifier, pattern] => do
            let (pattern, names) ← lower pattern
            pure (.alias pattern, .variable (← variableName fuel identifier) :: names)
        | "core-erlang-src:pattern-tuple", [items] => do
            let patterns ← (← series "core-erlang-src:patterns" fuel items).mapM lower
            pure (.tuple (patterns.map (·.1)), patterns.flatMap (·.2))
        | "core-erlang-src:pattern-cons", [items] => do
            let (label, fields) ← view items
            let rec list : Nat → String → List Packet → Lower (MatchPattern × List Name)
              | 0, _, _ => .error "pattern list exceeds its packet size"
              | fuel + 1, label, fields => do
                  match label, fields with
                  | "core-erlang-src:pattern-list-one", [head] =>
                      let (head, names) ← lower head
                      pure (.cons head (.literal .nil), names)
                  | "core-erlang-src:pattern-list-tail", [head, tail] =>
                      let (head, first) ← lower head
                      let (tail, rest) ← lower tail
                      pure (.cons head tail, first ++ rest)
                  | "core-erlang-src:pattern-list-more", [head, tail] =>
                      let (head, first) ← lower head
                      let (label, fields) ← view tail
                      let (tail, rest) ← list fuel label fields
                      pure (.cons head tail, first ++ rest)
                  | _, _ => .error "malformed pattern list"
            list fuel label fields
        | _, _ => do pure (.literal (← atomic source), [])
      unless distinct result.2 do .error "repeated variable in Core pattern"
      pure result

private def definition (fuel : Nat) (source : Packet) : Lower (Name × Packet) := do
  let ("core-erlang-src:definition", [name, body]) ← view source | .error "malformed function definition"
  pure (← functionName fuel name, body)

mutual
  private def literalValue : Nat → Packet → Lower Datum
    | 0, _ => .error "literal exceeds its packet size"
    | fuel + 1, source => do
        let source ← unwrap fuel source
        match ← view source with
        | ("core-erlang-src:literal-tuple", [items]) =>
            Mettapedia.Languages.Erlang.Value.tuple <$>
              (← series "core-erlang-src:literals" fuel items).mapM (literalValue fuel)
        | ("core-erlang-src:literal-list", [items]) => literalList fuel items
        | ("core-erlang-src:string", [string]) =>
            let characters ← quoted "SrcString" string
            pure (characters.toList.foldr (fun char rest =>
              Mettapedia.Languages.Erlang.Value.cons (.literal (.integer char.toNat)) rest) (.literal .nil))
        | _ => Mettapedia.Languages.Erlang.Value.literal <$> atomic source

  private def literalList : Nat → Packet → Lower Datum
    | 0, _ => .error "literal list exceeds its packet size"
    | fuel + 1, source => do
        match ← view source with
        | ("core-erlang-src:literal-list-one", [head]) =>
            pure (.cons (← literalValue fuel head) (.literal .nil))
        | ("core-erlang-src:literal-list-more", [head, tail]) =>
            pure (.cons (← literalValue fuel head) (← literalList fuel tail))
        | ("core-erlang-src:literal-list-tail", [head, tail]) =>
            pure (.cons (← literalValue fuel head) (← literalValue fuel tail))
        | _ => .error "malformed literal list"
end

private def dataExpression : Datum → Lower Assembly.Expression
  | .literal value => pure (Assembly.literal value)
  | .tuple fields => Assembly.tuple <$> fields.mapM dataExpression
  | .cons head tail => do pure (Assembly.cons (← dataExpression head) (← dataExpression tail))
  | .pid _ | .closure _ _ _ => .error "entry argument needs an explicit runtime identity context"

private def funParts (fuel : Nat) (source : Packet) : Lower (List Name × Packet) := do
  let ("core-erlang-src:fun", [parameters, body]) ← view (← unwrap fuel source)
    | .error "function definition requires a fun"
  let parameters ← (← series "core-erlang-src:variables" fuel parameters).mapM fun identifier =>
    Name.variable <$> variableName fuel identifier
  unless distinct parameters do .error "repeated function parameter"
  pure (parameters, body)

private def primitive? (name : String) (arity : Nat) : Option Primitive :=
  match name, arity with
  | "+", 2 => some .add | "-", 2 => some .subtract | "-", 1 => some .negate
  | "*", 2 => some .multiply | "div", 2 => some .divide | "rem", 2 => some .remainder
  | "==", 2 | "=:=", 2 => some .equal
  | "/=", 2 | "=/=", 2 => some .different
  | "<", 2 => some .less | "=<", 2 => some .lessEqual
  | ">", 2 => some .greater | ">=", 2 => some .greaterEqual
  | "is_integer", 1 => some .isInteger | "is_atom", 1 => some .isAtom
  | "is_tuple", 1 => some .isTuple | "is_list", 1 => some .isList | "is_pid", 1 => some .isPid
  | "is_function", 1 => some .isFunction | "is_function", 2 => some .isFunctionArity
  | "and", 2 => some .andBool | "or", 2 => some .orBool
  | "xor", 2 => some .xorBool | "not", 1 => some .notBool
  | _, _ => none

mutual
  private def expression : Nat → Context → Packet → Lower Assembly.Expression
    | 0, _, _ => .error "expression exceeds its packet size"
    | fuel + 1, context, source => do
        let source ← unwrap fuel source
        let (label, fields) ← view source
        let lower := expression fuel context
        match label, fields with
        | "core-erlang-src:expr-variable", [name] => lookup context (.variable (← text "SrcVariableName" name))
        | "core-erlang-src:expr-function-name", [name] => lookup context (← functionName fuel name)
        | "core-erlang-src:expr-values", [items] =>
            pure (Assembly.values (← (← series "core-erlang-src:expressions" fuel items).mapM lower))
        | "core-erlang-src:expr-tuple", [items] =>
            pure (Assembly.tuple (← (← series "core-erlang-src:expressions" fuel items).mapM lower))
        | "core-erlang-src:literal-tuple", [items] =>
            pure (Assembly.tuple (← (← series "core-erlang-src:literals" fuel items).mapM lower))
        | "core-erlang-src:expr-list", [items] => listExpression fuel context "core-erlang-src:expr-list" items
        | "core-erlang-src:literal-list", [items] => listExpression fuel context "core-erlang-src:literal-list" items
        | "core-erlang-src:string", [string] => do
            let characters ← quoted "SrcString" string
            pure (Assembly.integers (characters.toList.map (Int.ofNat ∘ Char.toNat)))
        | "core-erlang-src:fun", _ =>
            let (parameters, body) ← funParts fuel source
            pure (Assembly.lambda parameters.length (← expression fuel (extendNames context parameters) body))
        | "core-erlang-src:let", [binders, argument, body] =>
            let names ← (← series "core-erlang-src:variables" fuel binders).mapM fun identifier =>
              Name.variable <$> variableName fuel identifier
            unless distinct names do .error "repeated let variable"
            pure (Assembly.letValues names.length (← lower argument)
              (← expression fuel (extendNames context names) body))
        | "core-erlang-src:letrec", [definitions, body] =>
            let definitions ← (← series "core-erlang-src:definitions" fuel definitions).mapM (definition fuel)
            let names := definitions.map (·.1)
            unless distinct names do .error "repeated recursive function"
            let inner := extendNames context names
            let definitions ← definitions.mapM (functionDefinition fuel inner)
            pure (Assembly.letRecursive definitions (← expression fuel inner body))
        | "core-erlang-src:case", [argument, clauses] =>
            pure (Assembly.caseValues (← lower argument) (← clausesFuel fuel context clauses))
        | "core-erlang-src:do", [first, second] => pure (Assembly.sequence (← lower first) (← lower second))
        | "core-erlang-src:apply", [function, arguments] =>
            pure (Assembly.apply (← lower function)
              (← (← series "core-erlang-src:expressions" fuel arguments).mapM lower))
        | "core-erlang-src:call", [module, function, arguments] =>
            unless (← atomName fuel module) == "erlang" do .error "only admitted erlang calls are supported"
            let name ← atomName fuel function
            let arguments ← (← series "core-erlang-src:expressions" fuel arguments).mapM lower
            match name, arguments with
            | "self", [] => pure (Assembly.actor .self [])
            | "spawn", [function] => pure (Assembly.actor .spawn [function])
            | "!", [receiver, message] => pure (Assembly.actor .send [receiver, message])
            | _, _ =>
                let operator ← requireSome s!"unsupported builtin {name}/{arguments.length}" (primitive? name arguments.length)
                pure (Assembly.primitive operator arguments)
        | "core-erlang-src:primop", [name, arguments] =>
            let name ← quoted "SrcQuotedAtom" name
            let packets ← series "core-erlang-src:expressions" fuel arguments
            match name, packets with
            | "recv_peek_message", [] => pure (Assembly.actor .peekMessage [])
            | "recv_next", [] => pure (Assembly.actor .nextMessage [])
            | "remove_message", [] => pure (Assembly.actor .removeMessage [])
            | "recv_wait_timeout", [timeout] =>
                unless (← atomName fuel timeout) == "infinity" do .error "only an infinite receive wait is admitted"
                pure (Assembly.actor .waitInfinity [])
            | "match_fail", [reason] => pure (Assembly.matchFail (← lower reason))
            | _, _ => .error s!"unsupported primop {name}/{packets.length}"
        | "core-erlang-src:receive", [clauses, timeout, afterBody] =>
            unless (← atomName fuel timeout) == "infinity" && (← atomName fuel afterBody) == "true" do
              .error "receive requires the declared infinite-wait profile"
            let inner := [.receiveMessage, .receiveFlag, .receiveLoop] ++ context
            let clauses ← clausesFuel fuel inner clauses
            unless clauses.all (fun (patterns, _, _) => patterns.length == 1) do
              .error "receive clauses match one message"
            let yes := Assembly.atom "true"
            let again := Assembly.apply (Assembly.variableRef 2) []
            pure (Assembly.letRecursive [(0, Assembly.letValues 2 (Assembly.actor .peekMessage [])
              (Assembly.caseValues (Assembly.variableRef 1)
                [([.literal (.atom "true")], yes,
                  Assembly.caseValues (Assembly.variableRef 0)
                    (clauses.map (fun (patterns, guard, body) =>
                      (patterns, guard, Assembly.sequence (Assembly.actor .removeMessage []) body)) ++
                     [([.wildcard], yes, Assembly.sequence (Assembly.actor .nextMessage []) again)])),
                 ([.wildcard], yes, Assembly.sequence (Assembly.actor .waitInfinity []) again)]))]
              (Assembly.apply (Assembly.variableRef 0) []))
        | _, _ => Assembly.literal <$> atomic source

  private def listExpression : Nat → Context → String → Packet → Lower Assembly.Expression
    | 0, _, _, _ => .error "literal list exceeds its packet size"
    | fuel + 1, context, family, source => do
        let (label, fields) ← view source
        match fields with
        | [head] =>
            if label == family ++ "-one" then
              pure (Assembly.cons (← expression fuel context head) Assembly.nil)
            else .error "malformed list"
        | [head, tail] =>
            let head ← expression fuel context head
            if label == family ++ "-tail" then pure (Assembly.cons head (← expression fuel context tail))
            else if label == family ++ "-more" then pure (Assembly.cons head (← listExpression fuel context family tail))
            else .error "malformed list"
        | _ => .error "malformed list"

  private def clausesFuel : Nat → Context → Packet → Lower (List (List MatchPattern × Assembly.Expression × Assembly.Expression))
    | 0, _, _ => .error "clauses exceed their packet size"
    | fuel + 1, context, source => do
        (← series "core-erlang-src:clauses" fuel source).mapM fun source => do
          let ("core-erlang-src:clause", [patterns, guard, body]) ← view (← unwrap fuel source)
            | .error "malformed clause"
          let patterns ← (← series "core-erlang-src:patterns" fuel patterns).mapM (patternFuel fuel)
          let names := patterns.flatMap (·.2)
          unless distinct names do .error "repeated variable in Core clause patterns"
          let inner := extendNames context names
          pure (patterns.map (·.1), ← expression fuel inner guard, ← expression fuel inner body)

  private def functionDefinition : Nat → Context → (Name × Packet) → Lower (Nat × Assembly.Expression)
    | 0, _, _ => .error "function exceeds its packet size"
    | fuel + 1, context, (name, source) => do
        let .function _ arity := name | .error "expected a function identifier"
        let (parameters, body) ← funParts fuel source
        unless parameters.length == arity do .error "function name and parameter arities differ"
        pure (arity, ← expression fuel (extendNames context parameters) body)
end

/-- Function references are collected with local letrec shadowing respected.
Annotations and lexical tokens cannot add executable dependencies. -/
private def references : Nat → List Name → Packet → Lower (List Name)
  | 0, _, _ => .error "dependency traversal exceeds its packet size"
  | fuel + 1, locals, source => do
      let (label, _) ← requireSome "malformed dependency node" (node? source)
      if label.startsWith "source-lex:" then pure [] else do
        let (label, fields) ← view source
        match label, fields with
        | "core-erlang-src:expr-function-name", [name] =>
            let name ← functionName fuel name
            pure (if locals.contains name then [] else [name])
        | "core-erlang-src:letrec", [definitions, body] =>
            let definitions ← (← series "core-erlang-src:definitions" fuel definitions).mapM (definition fuel)
            let locals := definitions.map (·.1) ++ locals
            let children ← (definitions.map (·.2) ++ [body]).mapM (references fuel locals)
            pure children.flatten
        | _, _ => do pure (← fields.mapM (references fuel locals)).flatten

private def reachable (definitions : List (Name × Packet)) (packetFuel : Nat) :
    Nat → List Name → List Name → Lower (List Name)
  | 0, _, _ => .error "function dependency closure did not settle"
  | fuel + 1, pending, seen => do
      let pending := pending.filter (fun name => !seen.contains name) |>.eraseDups
      if pending.isEmpty then pure seen else do
        let dependencies ← pending.mapM fun name => do
          let (_, body) ← requireSome s!"undefined function {reprStr name}" (definitions.find? (·.1 == name))
          references packetFuel [] body
        reachable definitions packetFuel fuel dependencies.flatten (seen ++ pending)

structure CompiledEntry where
  moduleName : String
  attributes : List (String × Datum)
  exported : List Name
  entry : Name
  retained : List Name
  omitted : List Name
  program : Program

/-- Compile an explicitly chosen exported entry on closed data arguments. Source data
records omitted definitions; they receive no placeholder runtime behavior. -/
def lower (input : String) (source : Packet) (entryName : String := "run")
    (arguments : List Datum := []) : Lower CompiledEntry := do
  let grammar ← description
  unless validates grammar.grammar grammar.profile "SourceProgram" input source do
    .error "source packet readback differs from the complete original input"
  let fuel := packetNodes source + 1
  let ("core-erlang-src:program", [module]) ← view source | .error "expected a Core Erlang program"
  let ("core-erlang-src:module", [moduleName, exported, attributes, definitions]) ← view (← unwrap fuel module)
    | .error "expected a Core Erlang module"
  let moduleName ← quoted "SrcQuotedAtom" moduleName
  let attributes ← (← series "core-erlang-src:attributes" fuel attributes).mapM fun source => do
    let ("core-erlang-src:attribute", [name, value]) ← view source | .error "malformed module attribute"
    pure (← quoted "SrcQuotedAtom" name, ← literalValue fuel value)
  let exported ← (← series "core-erlang-src:function-names" fuel exported).mapM (functionName fuel)
  let definitions ← (← series "core-erlang-src:definitions" fuel definitions).mapM (definition fuel)
  unless distinct (definitions.map (·.1)) && distinct exported do .error "repeated module function identifier"
  unless exported.all (fun name => definitions.any (·.1 == name)) do .error "export has no function definition"
  for (name, body) in definitions do
    let .function _ arity := name | .error "malformed module function identifier"
    let (parameters, _) ← funParts fuel body
    unless parameters.length == arity do .error "function name and parameter arities differ"
  let entry := Name.function entryName arguments.length
  unless exported.contains entry do .error "selected entry is not exported"
  let needed ← reachable definitions fuel (definitions.length + 2) [entry] []
  let selected := definitions.filter (fun row => needed.contains row.1)
  let retained := selected.map (·.1)
  let context := retained.reverse
  let bodies ← selected.mapM (functionDefinition fuel context)
  let program := Assembly.assemble (Assembly.letRecursive bodies
    (Assembly.apply (← lookup context entry) (← arguments.mapM dataExpression)))
  unless program.checkScope do .error "lowered program fails independent IR formation"
  pure ⟨moduleName, attributes, exported, entry, retained,
    (definitions.map (·.1)).filter (fun name => !needed.contains name), program⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangSourceLowering
