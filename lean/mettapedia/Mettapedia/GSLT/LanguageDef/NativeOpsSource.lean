import Mettapedia.GSLT.LanguageDef.NativeOpsTyping
import Algorithms.MeTTa.Simple.Parser
import Mettapedia.GSLT.LanguageDef.NativeOpsQuotedString

/-!
# Native operational source admission

Admission begins with the existing occurrence-preserving S-expression carrier.
It recognizes each authored expression and statement, retains ordered operands,
checks complete function headers before bodies, and authorizes opaque/external
declarations only through exact entries in the supplied primitive catalogue.
Lexing and the textual parser have their separate source correspondence laws.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open Algorithms.MeTTa.Simple.Parser (SExpr)
open NativeWord64 (Word Byte admitWord)

private def letter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def identifier (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest => letter first &&
      rest.all (fun c => letter c || ('0' ≤ c && c ≤ '9') || c == '_' || c == '-')

def name? : SExpr → Option String
  | .atom token => if identifier token then some token else none
  | _ => none

def literalString? : SExpr → Option String
  | .atom token => NativeOpsQuotedString.decode token
  | _ => none

def decimal? (characters : List Char) : Option Nat :=
  if characters.isEmpty || !characters.all (fun c => '0' ≤ c && c ≤ '9') then none
  else some (characters.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0)

def natural? : SExpr → Option Nat
  | .atom token => match token.toList with
      | '-' :: characters => do
          let n ← decimal? characters
          if n = 0 then some 0 else none
      | characters => decimal? characters
  | _ => none

def word? (expression : SExpr) : Option Word := (natural? expression).bind admitWord

def byte? (expression : SExpr) : Option Byte := do
  let value ← natural? expression
  if h : value < 2 ^ 8 then some ⟨value, h⟩ else none

def type? : SExpr → Option NativeType
  | .atom "unit" => some .unit
  | .atom "u64" => some .word
  | .atom "byte" => some .byte
  | .atom "bool" => some .bool
  | .atom "bytes" => some bytesType
  | .atom "ref" | .atom "array" => none
  | .atom name => (name? (.atom name)).map NativeType.named
  | .list [.atom "ref", element] => (type? element).map NativeType.ref
  | .list [.atom "array", element] => (type? element).map NativeType.array
  | _ => none
termination_by expression => sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals omega

def parameter? : SExpr → Option Parameter
  | .list [name, type] => do
      let name ← name? name
      let type ← type? type
      some ⟨name, type⟩
  | _ => none

def parameters? : SExpr → Option (List Parameter)
  | .list values => do
      let parameters ← values.mapM parameter?
      if (parameters.map Parameter.name).Nodup then some parameters else none
  | _ => none

def unary? : String → Option Unary
  | "not" => some .not
  | "bnot" => some .complement
  | "to-u64" => some .toWord
  | "to-byte" => some .toByte
  | _ => none

def binary? : String → Option Binary
  | "add" => some (.word .add)
  | "sub" => some (.word .sub)
  | "mul" => some (.word .mul)
  | "div" => some (.word .div)
  | "mod" => some (.word .mod)
  | "shl" => some (.word .shl)
  | "shr" => some (.word .shr)
  | "band" => some (.word .band)
  | "bor" => some (.word .bor)
  | "bxor" => some (.word .bxor)
  | "eq" => some (.compare .eq)
  | "ne" => some (.compare .ne)
  | "lt" => some (.compare .lt)
  | "le" => some (.compare .le)
  | "gt" => some (.compare .gt)
  | "ge" => some (.compare .ge)
  | "and" => some .and
  | "or" => some .or
  | _ => none

mutual
  def expr? : SExpr → Option Expr
    | .list [.atom "u64", literal] => (word? literal).map Expr.word
    | .list [.atom "byte", literal] => (byte? literal).map Expr.byte
    | .list [.atom "bool", .atom "true"] => some (.bool true)
    | .list [.atom "bool", .atom "false"] => some (.bool false)
    | .list [.atom "var", name] => (name? name).map Expr.variable
    | .list [.atom "zero", type] => (type? type).map Expr.zero
    | .list [.atom "null", type] => (type? type).map Expr.null
    | .list [.atom "new", type] => (type? type).map Expr.new
    | .list [.atom "new-array", element, count] => do
        some (.newArray (← type? element) (← expr? count))
    | .list [.atom "field", base, field] => do
        some (.field (← expr? base) (← name? field))
    | .list [.atom "index", array, index] => do
        some (.index (← expr? array) (← expr? index))
    | .list [.atom "length", array] => (expr? array).map Expr.length
    | .list [.atom "slice", array, start, count] => do
        some (.slice (← expr? array) (← expr? start) (← expr? count))
    | .list [.atom "address", location] => (expr? location).map Expr.address
    | .list [.atom "load", reference] => (expr? reference).map Expr.load
    | .list (.atom "call" :: name :: arguments) => do
        some (.call (← name? name) (← exprList? arguments))
    | .list [.atom operator, operand] => do
        some (.unary (← unary? operator) (← expr? operand))
    | .list [.atom operator, left, right] => do
        some (.binary (← binary? operator) (← expr? left) (← expr? right))
    | _ => none
  termination_by expression => sizeOf expression
  decreasing_by
  all_goals simp_wf
  all_goals omega

  def exprList? : List SExpr → Option (List Expr)
    | [] => some []
    | expression :: rest => do
        some ((← expr? expression) :: (← exprList? rest))
  termination_by expressions => sizeOf expressions
  decreasing_by
  all_goals simp_wf
  all_goals omega
end

inductive SwitchArm where
  | case (selector : Word) (body : List Statement)
  | default (body : List Statement)
  deriving Repr

def assembleSwitch? (selector : Expr) (arms : List SwitchArm) : Option Statement :=
  let cases := arms.filterMap fun arm => match arm with
    | .case word body => some (word, body)
    | _ => none
  let defaults := arms.filterMap fun arm => match arm with
    | .default body => some body
    | _ => none
  match defaults with
  | [body] => if (cases.map Prod.fst).Nodup then some (.switch selector cases body) else none
  | _ => none

mutual
  def statement? : SExpr → Option Statement
    | .list [.atom "let", name, type, initializer] => do
        some (.declare (← name? name) (← type? type) (← expr? initializer))
    | .list [.atom "set", location, value] => do
        some (.set (← expr? location) (← expr? value))
    | .list [.atom "if", condition, thenBody, elseBody] => do
        some (.branch (← expr? condition) (← block? thenBody) (← block? elseBody))
    | .list [.atom "while", condition, body] => do
        some (.while (← expr? condition) (← block? body))
    | .list (.atom "switch" :: selector :: arms) => do
        assembleSwitch? (← expr? selector) (← switchArms? arms)
    | .list [.atom "break"] => some .break
    | .list [.atom "continue"] => some .continue
    | .list [.atom "effect", expression] => (expr? expression).map Statement.effect
    | .list [.atom "free", expression] => (expr? expression).map Statement.free
    | .list [.atom "return"] => some (.return none)
    | .list [.atom "return", expression] => do some (.return (some (← expr? expression)))
    | .list (.atom "block" :: body) => (statements? body).map Statement.block
    | _ => none
  termination_by expression => sizeOf expression
  decreasing_by
  all_goals simp_wf
  all_goals omega

  def block? : SExpr → Option (List Statement)
    | .list (.atom "block" :: body) => statements? body
    | _ => none
  termination_by expression => sizeOf expression
  decreasing_by
  all_goals simp_wf
  all_goals omega

  def statements? : List SExpr → Option (List Statement)
    | [] => some []
    | statement :: rest => do
        some ((← statement? statement) :: (← statements? rest))
  termination_by expressions => sizeOf expressions
  decreasing_by
  all_goals simp_wf
  all_goals omega

  def switchArms? : List SExpr → Option (List SwitchArm)
    | [] => some []
    | .list [.atom "case", selector, body] :: rest => do
        some (.case (← word? selector) (← block? body) :: (← switchArms? rest))
    | .list [.atom "default", body] :: rest => do
        some (.default (← block? body) :: (← switchArms? rest))
    | _ => none
  termination_by expressions => sizeOf expressions
  decreasing_by
  all_goals simp_wf
  all_goals omega
end

structure Catalogue where
  opaques : List Opaque
  externals : List External
  deriving DecidableEq, Repr

def cKeywords : List String :=
  ["auto", "break", "case", "char", "const", "continue", "default", "do", "double",
   "else", "enum", "extern", "float", "for", "goto", "if", "inline", "int", "long",
   "register", "restrict", "return", "short", "signed", "sizeof", "static", "struct",
   "switch", "typedef", "union", "unsigned", "void", "volatile", "while", "_Alignas",
   "_Alignof", "_Atomic", "_Bool", "_Complex", "_Generic", "_Imaginary", "_Noreturn",
   "_Static_assert", "_Thread_local", "bool", "true", "false"]

def cIdentifierCharacters : List Char → List Char
  | [] => []
  | '_' :: rest => ['_', 'u', '_'] ++ cIdentifierCharacters rest
  | '-' :: rest => ['_', 'h', '_'] ++ cIdentifierCharacters rest
  | c :: rest => c :: cIdentifierCharacters rest

def cIdentifier (name : String) : String :=
  let encoded := String.ofList (cIdentifierCharacters name.toList)
  if cKeywords.contains encoded then "gslt_keyword_" ++ encoded else encoded

def functionSymbol (moduleName functionName : String) : String :=
  "cetta_gslt_" ++ cIdentifier moduleName ++ "_" ++ cIdentifier functionName ++ "_v1"

def validCName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest => letter first &&
      rest.all (fun c => letter c || ('0' ≤ c && c ≤ '9') || c == '_') &&
      !cKeywords.contains name

def headerCharacters : List Char → Bool → Bool
  | [], segmentNonempty => segmentNonempty
  | '/' :: rest, segmentNonempty => segmentNonempty && headerCharacters rest false
  | c :: rest, _ =>
      (letter c || ('0' ≤ c && c ≤ '9') || c == '_' || c == '-') &&
        headerCharacters rest true

def validHeader (name : String) : Bool :=
  match name.toList.reverse with
  | 'h' :: '.' :: rest => headerCharacters rest false
  | _ => false

def catalogueValid (catalogue : Catalogue) : Bool :=
  (catalogue.opaques.map Opaque.name).Nodup &&
    (catalogue.externals.map (fun declaration => declaration.header.name)).Nodup &&
    (catalogue.externals.map External.cSymbol).Nodup &&
    catalogue.opaques.all (fun declaration => identifier declaration.name &&
      validCName declaration.cType && validHeader declaration.includeHeader) &&
    catalogue.externals.all (fun declaration => identifier declaration.header.name &&
      validCName declaration.cSymbol &&
      (declaration.header.parameters.map Parameter.name).Nodup &&
      declaration.header.parameters.all (fun parameter => identifier parameter.name) &&
      match declaration.includeHeader with
      | none => true
      | some header => validHeader header)

inductive Declaration where
  | record (declaration : Record)
  | opaqueDeclaration (declaration : Opaque)
  | external (declaration : External)
  | function (declaration : Function)
  deriving Repr

def declarationName : Declaration → String
  | .record declaration => declaration.name
  | .opaqueDeclaration declaration => declaration.name
  | .external declaration => declaration.header.name
  | .function declaration => declaration.header.name

def declaration? (catalogue : Catalogue) : SExpr → Option Declaration
  | .list [.atom "record", name, fields] => do
      let name ← name? name
      let fields ← parameters? fields
      if fields.isEmpty then none else some (.record ⟨name, fields⟩)
  | .list [.atom "opaque", name, cType, includeHeader] => do
      let declaration : Opaque := ⟨← name? name, ← literalString? cType,
        ← literalString? includeHeader⟩
      if declaration ∈ catalogue.opaques then some (.opaqueDeclaration declaration) else none
  | .list [.atom "extern", name, cSymbol, parameters, result, .atom effect] => do
      let name ← name? name
      let supplied ← catalogue.externals.find? (fun external => external.header.name == name)
      let parameters ← parameters? parameters
      let result ← type? result
      let cSymbol ← literalString? cSymbol
      let policy ← match effect with
        | "pure" => some Effect.pure
        | "effect" => some Effect.effect
        | _ => none
      let declaration : External := ⟨⟨name, parameters, result⟩, cSymbol, policy,
        supplied.includeHeader⟩
      if declaration = supplied then some (.external declaration) else none
  | .list [.atom "function", name, parameters, result, body] => do
      some (.function ⟨⟨← name? name, ← parameters? parameters, ← type? result⟩, ← block? body⟩)
  | _ => none

private def inlineDependency : NativeType → Option String
  | .named name => some name
  | _ => none

/-- The traversal bound is the number of declarations, not a guest runtime limit. -/
def recordOrder? : Nat → List String → List Record → Option (List String)
  | _, accepted, [] => some accepted
  | 0, _, _ :: _ => none
  | fuel + 1, accepted, remaining => do
      let ready ← remaining.find? fun record => record.fields.all fun field =>
        match inlineDependency field.type with
        | none => true
        | some name => accepted.contains name
      recordOrder? fuel (accepted ++ [ready.name]) (remaining.filter (fun record => record.name != ready.name))

def programValid (program : Program) : Bool :=
  let interface := program.interface
  let names := interface.records.map Record.name ++ interface.opaques.map Opaque.name ++
    interface.externals.map (fun external => external.header.name) ++
    program.functions.map (fun function => function.header.name)
  identifier program.name && !program.functions.isEmpty && names.Nodup &&
    names.all (fun name => identifier name &&
      !( ["unit", "u64", "byte", "bool", "bytes"].contains name)) &&
    interface.records.all (fun record => !record.fields.isEmpty &&
      (record.fields.map Parameter.name).Nodup &&
      record.fields.all (fun field => validType interface field.type true)) &&
    (recordOrder? interface.records.length [] interface.records).isSome &&
    (interface.externals.map External.cSymbol).Nodup &&
    interface.externals.all (fun external => !program.functions.any
      (fun function => functionSymbol program.name function.header.name == external.cSymbol)) &&
    interface.externals.all (fun external =>
      external.header.parameters.all (fun parameter => validType interface parameter.type true) &&
      validType interface external.header.result (external.header.result != .unit)) &&
    decide (interface.functions = program.functions.map Function.header) &&
    program.functions.all (checkFunction interface)

def assembleProgram (name : String) (declarations : List Declaration) : Program :=
  let records := declarations.filterMap fun declaration => match declaration with
    | .record record => some record
    | _ => none
  let opaques := declarations.filterMap fun declaration => match declaration with
    | .opaqueDeclaration opaqueDeclaration => some opaqueDeclaration
    | _ => none
  let externals := declarations.filterMap fun declaration => match declaration with
    | .external external => some external
    | _ => none
  let functions := declarations.filterMap fun declaration => match declaration with
    | .function function => some function
    | _ => none
  ⟨name, ⟨records, opaques, functions.map Function.header, externals⟩, functions⟩

def parseProgram? (catalogue : Catalogue) : SExpr → Option Program
  | .list (.atom "gslt-native-ops-v1" :: name :: declarations) => do
      some (assembleProgram (← name? name) (← declarations.mapM (declaration? catalogue)))
  | _ => none

def admitProgram? (catalogue : Catalogue) (sourceSyntax : SExpr) : Option Program := do
  if !catalogueValid catalogue then none else
    let program ← parseProgram? catalogue sourceSyntax
    if programValid program then some program else none

theorem admitted_program_parsed {catalogue : Catalogue} {sourceSyntax : SExpr} {program : Program}
    (admitted : admitProgram? catalogue sourceSyntax = some program) :
    parseProgram? catalogue sourceSyntax = some program ∧ programValid program = true := by
  unfold admitProgram? at admitted
  split at admitted
  · contradiction
  · cases parsed : parseProgram? catalogue sourceSyntax with
      | none => simp [parsed] at admitted
      | some actual =>
          simp only [parsed, bind, Option.bind] at admitted
          split at admitted
          · cases admitted
            exact ⟨rfl, by assumption⟩
          · contradiction

end Mettapedia.GSLT.LanguageDef.NativeOps
