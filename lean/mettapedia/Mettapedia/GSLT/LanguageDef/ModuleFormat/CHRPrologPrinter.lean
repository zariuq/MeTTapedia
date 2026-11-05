import Mettapedia.Languages.CHR.Syntax

/-! Canonical ordinary CHR source, separate from IR-value serialization and
runtime instruction emission. Printed variables use a whole-scope canonical
allocation; quoted atoms cannot introduce source operators or directives. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologPrinter

open Mettapedia.Languages

def atom (text : String) : String :=
  "'" ++ String.join (text.toList.map fun character => match character with
    | '\'' => "''" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
    | '\u0007' => "\\a" | '\u0008' => "\\b" | '\u000b' => "\\v" | '\u000c' => "\\f"
    | other => String.singleton other) ++ "'"

def arguments (fields : List String) : String := "(" ++ String.intercalate ", " fields ++ ")"
def variableName (index : Nat) : String := "V" ++ toString index

def value : CHR.Value → String
  | .integer number => toString number
  | .atom name => atom name
  | .tuple fields => "tuple" ++ arguments (fields.map value)

def term : CHR.Term → String
  | .value datum => value datum
  | .var index => variableName index
  | .tuple fields => "tuple" ++ arguments (fields.map term)

def head (source : CHR.Head) : String :=
  atom source.name ++ if source.arguments.isEmpty then "" else arguments (source.arguments.map term)

def constraint (source : CHR.Constraint) : String :=
  atom source.name ++ if source.arguments.isEmpty then "" else arguments (source.arguments.map value)

def operator : CHR.IntOperator → String
  | .add => "+" | .subtract => "-" | .multiply => "*"
  | .quotient => "//" | .remainder => "rem" | .modulo => "mod"

def expression : CHR.IntExpr → String
  | .literal number => toString number
  | .index index => variableName index
  | .operation operation left right =>
      "(" ++ expression left ++ " " ++ operator operation ++ " " ++ expression right ++ ")"

def comparison : CHR.Comparison → String
  | .equal => "=:=" | .different => "=\\=" | .less => "<"
  | .lessEqual => "=<" | .greater => ">" | .greaterEqual => ">="

def guard : CHR.Guard → String
  | .identical left right => term left ++ " == " ++ term right
  | .distinct left right => term left ++ " \\== " ++ term right
  | .compare operation left right => expression left ++ " " ++ comparison operation ++ " " ++ expression right

def goal : CHR.Goal → String
  | .tell source => head source
  | .assign index source => variableName index ++ " is " ++ expression source
  | .fail => "fail"

def conjunction (fields : List String) : String :=
  if fields.isEmpty then "true" else String.intercalate ", " fields

def rule (source : CHR.Rule) : String :=
  let kept := conjunction (source.kept.map head)
  let removed := conjunction (source.removed.map head)
  let heads := if source.removed.isEmpty then kept ++ " ==> "
    else if source.kept.isEmpty then removed ++ " <=> " else kept ++ " \\ " ++ removed ++ " <=> "
  let guards := if source.guards.isEmpty then "" else conjunction (source.guards.map guard) ++ " | "
  atom source.name ++ " @ " ++ heads ++ guards ++ conjunction (source.body.map goal) ++ ".\n"

def declaration (source : CHR.Declaration) : String := atom source.name ++ "/" ++ toString source.arity

def program (source : CHR.Program) (inputs : List CHR.Constraint := []) : String :=
  let declarations := if source.declarations.isEmpty then "" else
    ":- chr_constraint " ++ String.intercalate ", " (source.declarations.map declaration) ++ ".\n" ++
      ":- chr_option(optimize,off).\n"
  ":- use_module(library(chr)).\n" ++ declarations ++ String.join (source.rules.map rule) ++
    if inputs.isEmpty then "" else "?- " ++ conjunction (inputs.map constraint) ++ ".\n"

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologPrinter
