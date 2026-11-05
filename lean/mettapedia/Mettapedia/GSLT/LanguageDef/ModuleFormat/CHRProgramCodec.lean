import Mettapedia.GSLT.LanguageDef.ModuleFormat.Value
import Mettapedia.Languages.CHR.Syntax

/-! Transport the independent CHR IR using the existing module-value
carrier and the constructor inventory of CHRIR/CHRProgram. Integer and
string fields retain their types. This data codec is separate from both
Prolog source syntax and the controller's execution-instruction lowering. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRProgramCodec

open Mettapedia.Languages

def node (name : String) (fields : List Value) : Value :=
  .record [("head", .string name), ("arguments", .list fields)]

def node? : Value → Option (String × List Value)
  | .record [("head", .string name), ("arguments", .list fields)] => some (name, fields)
  | _ => none

def natural? : Value → Option Nat
  | .integer number => if number < 0 then none else some number.toNat
  | _ => none

def integer? : Value → Option Int
  | .integer number => some number
  | _ => none

def values? {α : Type} (read : Value → Option α) : Value → Option (List α)
  | .list values => values.mapM read
  | _ => none

def value : CHR.Value → Value
  | .integer number => node "ChrInt" [.integer number]
  | .atom text => node "ChrSymbol" [.string text]
  | .tuple fields => node "ChrTuple" [.list (fields.map value)]

def value? : Value → Option CHR.Value
  | .record [("head", .string "ChrInt"), ("arguments", .list [number])] => CHR.Value.integer <$> integer? number
  | .record [("head", .string "ChrSymbol"), ("arguments", .list [.string text])] => some (.atom text)
  | .record [("head", .string "ChrTuple"), ("arguments", .list [.list fields])] => CHR.Value.tuple <$> fields.mapM value?
  | _ => none

def term : CHR.Term → Value
  | .value datum => node "ChrLiteral" [value datum]
  | .var index => node "ChrVariable" [.integer index]
  | .tuple fields => node "ChrTermTuple" [.list (fields.map term)]

def term? : Value → Option CHR.Term
  | .record [("head", .string "ChrLiteral"), ("arguments", .list [datum])] => CHR.Term.value <$> value? datum
  | .record [("head", .string "ChrVariable"), ("arguments", .list [index])] => CHR.Term.var <$> natural? index
  | .record [("head", .string "ChrTermTuple"), ("arguments", .list [.list fields])] => CHR.Term.tuple <$> fields.mapM term?
  | _ => none

def head (source : CHR.Head) : Value :=
  node "ChrHead" [.string source.name, .list (source.arguments.map term)]

def head? (source : Value) : Option CHR.Head := do
  let ("ChrHead", [.string name, fields]) ← node? source | none
  pure ⟨name, ← values? term? fields⟩

def operation : CHR.IntOperator → String
  | .add => "ChrAdd" | .subtract => "ChrSubtract" | .multiply => "ChrMultiply"
  | .quotient => "ChrQuotient" | .remainder => "ChrRemainder" | .modulo => "ChrModulo"

def operation? : String → Option CHR.IntOperator
  | "ChrAdd" => some .add | "ChrSubtract" => some .subtract | "ChrMultiply" => some .multiply
  | "ChrQuotient" => some .quotient | "ChrRemainder" => some .remainder | "ChrModulo" => some .modulo
  | _ => none

def expression : CHR.IntExpr → Value
  | .literal number => node "ChrNumber" [.integer number]
  | .index index => node "ChrIntVariable" [.integer index]
  | .operation operator left right => node (operation operator) [expression left, expression right]

def expression? : Value → Option CHR.IntExpr
  | .record [("head", .string "ChrNumber"), ("arguments", .list [number])] => CHR.IntExpr.literal <$> integer? number
  | .record [("head", .string "ChrIntVariable"), ("arguments", .list [index])] => CHR.IntExpr.index <$> natural? index
  | .record [("head", .string name), ("arguments", .list [left, right])] => do
      pure (.operation (← operation? name) (← expression? left) (← expression? right))
  | _ => none

def comparison : CHR.Comparison → Value
  | .equal => node "ChrEqual" [] | .different => node "ChrDifferent" [] | .less => node "ChrLess" []
  | .lessEqual => node "ChrLessEqual" [] | .greater => node "ChrGreater" [] | .greaterEqual => node "ChrGreaterEqual" []

def comparison? (source : Value) : Option CHR.Comparison := do
  match ← node? source with
  | ("ChrEqual", []) => some .equal | ("ChrDifferent", []) => some .different | ("ChrLess", []) => some .less
  | ("ChrLessEqual", []) => some .lessEqual | ("ChrGreater", []) => some .greater | ("ChrGreaterEqual", []) => some .greaterEqual
  | _ => none

def guard : CHR.Guard → Value
  | .identical left right => node "ChrIdentical" [term left, term right]
  | .distinct left right => node "ChrDistinct" [term left, term right]
  | .compare operator left right => node "ChrCompare" [comparison operator, expression left, expression right]

def guard? (source : Value) : Option CHR.Guard := do
  match ← node? source with
  | ("ChrIdentical", [left, right]) => pure (.identical (← term? left) (← term? right))
  | ("ChrDistinct", [left, right]) => pure (.distinct (← term? left) (← term? right))
  | ("ChrCompare", [operator, left, right]) =>
      pure (.compare (← comparison? operator) (← expression? left) (← expression? right))
  | _ => none

def goal : CHR.Goal → Value
  | .tell constraint => node "ChrTell" [head constraint]
  | .assign index source => node "ChrAssign" [.integer index, expression source]
  | .fail => node "ChrFail" []

def goal? (source : Value) : Option CHR.Goal := do
  match ← node? source with
  | ("ChrTell", [constraint]) => CHR.Goal.tell <$> head? constraint
  | ("ChrAssign", [index, source]) => pure (.assign (← natural? index) (← expression? source))
  | ("ChrFail", []) => some .fail
  | _ => none

def rule (source : CHR.Rule) : Value :=
  node "ChrRule" [.string source.name, .list (source.kept.map head), .list (source.removed.map head),
    .list (source.guards.map guard), .list (source.body.map goal)]

def rule? (source : Value) : Option CHR.Rule := do
  let ("ChrRule", [.string name, kept, removed, guards, body]) ← node? source | none
  pure ⟨name, ← values? head? kept, ← values? head? removed, ← values? guard? guards, ← values? goal? body⟩

def declaration (source : CHR.Declaration) : Value :=
  node "ChrDeclare" [.string source.name, .integer source.arity]

def declaration? (source : Value) : Option CHR.Declaration := do
  let ("ChrDeclare", [.string name, arity]) ← node? source | none
  pure ⟨name, ← natural? arity⟩

def program (source : CHR.Program) : Value :=
  node "ChrProgram" [.list (source.declarations.map declaration), .list (source.rules.map rule)]

def program? (source : Value) : Option CHR.Program := do
  let ("ChrProgram", [declarations, rules]) ← node? source | none
  pure ⟨← values? declaration? declarations, ← values? rule? rules⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRProgramCodec
