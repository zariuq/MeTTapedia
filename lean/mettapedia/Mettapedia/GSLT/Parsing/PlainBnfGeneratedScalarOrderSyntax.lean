import Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaDispatch

/-!
# The actual NativeType-selected scalar-order equations

The whole fixture is independently generated from the eight authored sources
and their inferred NativeTypes. Both the raw fallback and admitted family are
read here. Projections retrieve original equations and physical source lines;
shape checks neither replace the bodies nor supply their meaning.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarOrderSyntax

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Match
open GeneratedPeTTaEquationDispatch
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def commandChunks : List (List (Nat × Bool × SExpr)) :=
  metta_sexpr_command_chunks_file% petta "../../../../../../hyperon/cetta-prime-nik-20260811/tests/langdef/bnf/generated/plain_bnf_typed_discovery_v1.metta"

def commands : List (Nat × Bool × SExpr) := commandChunks.flatten

theorem commands_count : commands.length = 492 := by
  rw [commands, List.length_flatten]
  rfl

def programChunks : List (List (Nat × SExpr)) :=
  commandChunks.map fun chunk =>
    chunk.filterMap fun (line, query, term) => if query then none else some (line, term)

/-- Definition inventory only. The sole import command is retained separately
below; its runtime effects and any imported equations are not modeled here. -/
def program : List (Nat × SExpr) :=
  programChunks.flatten

theorem program_eq_commands : program =
    commands.filterMap (fun (line, query, term) => if query then none else some (line, term)) := by
  simp only [program, programChunks, commands, List.filterMap_flatten]

theorem program_count : program.length = 491 := by
  rw [program, List.length_flatten]
  rfl

theorem evaluation_command_retained : commands.filter (fun command => command.2.1) =
    [(2677, true, .list [.atom "let", .atom "$_",
      .list [.atom "import!", .atom "&self", .atom "langdef"], .list [.atom "empty"]])] := by
  rw [commands, List.filter_flatten]
  rfl

def symbol : Bool → String
  | false => "gslt:mode:BNFScalarOrderDiagnosticV1:1110"
  | true => "admitted:gslt:fn:BNFScalarOrderDiagnosticV1:1110"

def selectedRows (name : String) : List (Nat × SExpr) :=
  programChunks.flatMap (equationsFor name)

theorem equationsFor_program (name : String) : equationsFor name program = selectedRows name := by
  simp only [program, equationsFor, selectedRows, List.filter_flatten, List.flatMap_def]
  rfl

def rows (typed : Bool) : List (Nat × SExpr) := selectedRows (symbol typed)

theorem equationsFor_rows (typed : Bool) : equationsFor (symbol typed) program = rows typed :=
  equationsFor_program (symbol typed)

theorem rows_count (typed : Bool) : (rows typed).length = 2 := by cases typed <;> rfl

def row (typed : Bool) (i : Fin 2) : Nat × SExpr :=
  (rows typed)[i.val]'(by rw [rows_count]; exact i.isLt)

theorem exact_rows (typed : Bool) : rows typed = [row typed 0, row typed 1] := by
  cases typed <;> rfl

theorem row_is_equation (typed : Bool) (i : Fin 2) :
    (equation? (row typed i).2).isSome = true := by cases typed <;> fin_cases i <;> rfl

def head (typed : Bool) (i : Fin 2) : SExpr :=
  ((equation? (row typed i).2).get (row_is_equation typed i)).1

def body (typed : Bool) (i : Fin 2) : SExpr :=
  ((equation? (row typed i).2).get (row_is_equation typed i)).2

theorem row_equation (typed : Bool) (i : Fin 2) :
    equation? (row typed i).2 = some (head typed i, body typed i) := by
  cases typed <;> fin_cases i <;> rfl

theorem head_shape (typed : Bool) (i : Fin 2) :
    head typed i = .list [.atom (symbol typed), .atom "$left", .atom "$right", .atom "$origin"] := by
  cases typed <;> fin_cases i <;> rfl

theorem bodies_unchanged (i : Fin 2) : body true i = body false i := by fin_cases i <;> rfl

def tag : String := "gslt:result:BNFScalarOrderDiagnosticV1:1110"

theorem first_body (typed : Bool) : body typed 0 =
    .list [.atom "let", .atom "$_",
      .list [.atom "gslt:ground-integer-less",
        .list [.atom "ground-integer-less", .atom "$left", .atom "$right"]],
      .list [.atom "quote", .list [.atom tag, .atom "BNFDiagnosticsNilV1"]]] := by
  cases typed <;> rfl

theorem second_body (typed : Bool) : body typed 1 =
    .list [.atom "let", .atom "$_",
      .list [.atom "gslt:ground-integer-not-less",
        .list [.atom "ground-integer-not-less", .atom "$left", .atom "$right"]],
      .list [.atom "quote", .list [.atom tag,
        .list [.atom "BNFDiagnosticsConsV1",
          .list [.atom "BNFNonIncreasingLexicalScalarsV1",
            .atom "$left", .atom "$right", .atom "$origin"], .atom "BNFDiagnosticsNilV1"]]]] := by
  cases typed <;> rfl

private def literalChunk (chunk : List (Nat × SExpr)) : Bool :=
  chunk.all (fun entry => PlainBnfGeneratedPeTTaSyntax.hasLiteralEquationHead entry.2)

private theorem literal_first : (programChunks.take 8).all literalChunk = true := by rfl
private theorem literal_second : ((programChunks.drop 8).take 8).all literalChunk = true := by rfl
private theorem literal_third : ((programChunks.drop 16).take 8).all literalChunk = true := by rfl
private theorem literal_fourth : (programChunks.drop 24).all literalChunk = true := by rfl

private theorem chunk_partition : programChunks =
    programChunks.take 8 ++ (programChunks.drop 8).take 8 ++
      (programChunks.drop 16).take 8 ++ programChunks.drop 24 := by rfl

theorem all_literal : program.all (fun entry =>
    PlainBnfGeneratedPeTTaSyntax.hasLiteralEquationHead entry.2) = true := by
  rw [program, List.all_flatten]
  change programChunks.all literalChunk = true
  rw [chunk_partition]
  simp only [List.all_append, literal_first, literal_second, literal_third, literal_fourth]
  rfl

theorem literal_heads : ∀ entry ∈ program, LiteralEquationHead entry.2 := by
  intro entry member lhs rhs parsed
  exact PlainBnfGeneratedPeTTaDispatch.parsed_literal_head entry.2 lhs rhs parsed
    (List.all_eq_true.mp all_literal entry member)

theorem dispatch_filter (env : Bindings) (name : String) (arguments : List SExpr) :
    dispatch env (.list (.atom name :: arguments)) program =
      dispatch env (.list (.atom name :: arguments)) (equationsFor name program) :=
  dispatch_literal_filter env name arguments program literal_heads

theorem physical_lines :
    (rows false).map Prod.fst = [962, 967] ∧
    (rows true).map Prod.fst = [2358, 2363] := by exact ⟨rfl, rfl⟩

def callerRows (typed : Bool) : List (Nat × SExpr) := selectedRows
  (if typed then "admitted:gslt:mode:BNFValidateScalarListV1:110"
    else "gslt:mode:BNFValidateScalarListV1:110")

theorem caller_rows_count (typed : Bool) : (callerRows typed).length = 2 := by
  cases typed <;> rfl

def callerRow (typed : Bool) : Nat × SExpr :=
  (callerRows typed)[1]'(by rw [caller_rows_count]; decide)

private def letParts? : SExpr → Option (SExpr × SExpr × SExpr)
  | .list [.atom "let", schema, value, continuation] => some (schema, value, continuation)
  | _ => none

/-- Retrieve the second let from the actual generated cons-clause body. -/
def callerParts? (typed : Bool) : Option (SExpr × SExpr × SExpr) := do
  let (_, body) ← equation? (callerRow typed).2
  let (_, _, continuation) ← letParts? body
  letParts? continuation

theorem caller_parts_present (typed : Bool) : (callerParts? typed).isSome = true := by
  cases typed <;> rfl

def callerParts (typed : Bool) : SExpr × SExpr × SExpr :=
  (callerParts? typed).get (caller_parts_present typed)

def callerSchema (typed : Bool) : SExpr := (callerParts typed).1
def callerValue (typed : Bool) : SExpr := (callerParts typed).2.1

theorem caller_schema (typed : Bool) : callerSchema typed =
    .list [.atom tag, .atom "$orderDiagnostics"] := by cases typed <;> rfl

theorem raw_caller_value : callerValue false =
    .list [.atom "superpose", .list [.atom "collapse",
      .list [.atom (symbol false), .atom "$head", .atom "$next", .atom "$origin"]]] := rfl

theorem typed_caller_value : callerValue true =
    .list [.atom "once",
      .list [.atom (symbol true), .atom "$head", .atom "$next", .atom "$origin"]] := rfl

theorem caller_physical_lines : (callerRow false).1 = 977 ∧ (callerRow true).1 = 2373 :=
  ⟨rfl, rfl⟩

theorem result_tag_not_callable : equationsFor tag program = [] := by
  rw [equationsFor_program]
  rfl

end Mettapedia.GSLT.Parsing.PlainBnfGeneratedScalarOrderSyntax
