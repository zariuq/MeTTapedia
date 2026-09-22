import Mettapedia.GSLT.Parsing.GeneratedPeTTaResultBinding

/-!
# Literal equation-head dispatch in existing generated source syntax

The extraction and scan retain raw S-expressions, physical row identities,
and every ordered matching occurrence. No equation body is evaluated here.
-/

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaEquationDispatch

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open SourceSExprPatternCodec (encode encodeList)
open GeneratedPeTTaResultBinding (template templates variableToken bindResult)

/-- Extract exactly an equation, retaining its existing source head and body. -/
def equation? : SExpr → Option (SExpr × SExpr)
  | .list [.atom "=", head, body] => some (head, body)
  | _ => none

/-- Extract an application-head atom; literalness is checked separately. -/
def equationSymbol? (source : SExpr) : Option String := do
  let (head, _) ← equation? source
  match head with
  | .list (.atom symbol :: _) => some symbol
  | _ => none

/-- A stable filter of original physical rows, never a set or a keyed map. -/
def equationsFor (symbol : String) (rows : List (Nat × SExpr)) : List (Nat × SExpr) :=
  rows.filter (fun row => equationSymbol? row.2 == some symbol)

def matchEquation (env : Bindings) (call source : SExpr) : List Bindings :=
  match equation? source with
  | some (head, _) => bindResult env head call
  | none => []

/-- Every successful occurrence remains paired with its original row. -/
def dispatch (env : Bindings) (call : SExpr) (rows : List (Nat × SExpr)) :
    List ((Nat × SExpr) × Bindings) :=
  rows.flatMap (fun row => (matchEquation env call row.2).map (fun bindings => (row, bindings)))

theorem equation?_eq_some_iff (source head body : SExpr) :
    equation? source = some (head, body) ↔ source = .list [.atom "=", head, body] := by
  constructor
  · intro parsed
    unfold equation? at parsed
    split at parsed <;> simp_all
  · rintro rfl
    rfl

theorem different_literal_head_does_not_match (symbol other : String)
    (literal : variableToken symbol = false) (different : symbol ≠ other)
    (schemas arguments : List SExpr) :
    matchPattern (template (.list (.atom symbol :: schemas)))
      (encode (.list (.atom other :: arguments))) = [] := by
  simp [template, templates, literal, encode, encodeList, matchPattern, matchArgs, different]

/-- Every extracted equation has a non-variable application-head atom.
Non-equation declarations impose no dispatch condition. -/
def LiteralEquationHead (source : SExpr) : Prop :=
  ∀ head body, equation? source = some (head, body) →
    ∃ symbol schemas, head = .list (.atom symbol :: schemas) ∧ variableToken symbol = false

theorem other_literal_equation_does_not_match (env : Bindings) (symbol : String)
    (arguments : List SExpr) (source : SExpr)
    (literal : LiteralEquationHead source)
    (other : equationSymbol? source ≠ some symbol) :
    matchEquation env (.list (.atom symbol :: arguments)) source = [] := by
  cases parsed : equation? source with
  | none => simp [matchEquation, parsed]
  | some pair =>
      rcases pair with ⟨head, body⟩
      obtain ⟨actual, schemas, rfl, plain⟩ := literal head body parsed
      have different : actual ≠ symbol := by
        simpa [equationSymbol?, parsed] using other
      simp [matchEquation, parsed, bindResult,
        different_literal_head_does_not_match actual symbol plain different schemas arguments]

/-- Under the declared literal-head condition, filtering unrelated equations
before matching preserves the full ordered occurrence-and-binding list. -/
theorem dispatch_literal_filter (env : Bindings) (symbol : String) (arguments : List SExpr)
    (rows : List (Nat × SExpr))
    (literal : ∀ row ∈ rows, LiteralEquationHead row.2) :
    dispatch env (.list (.atom symbol :: arguments)) rows =
      dispatch env (.list (.atom symbol :: arguments)) (equationsFor symbol rows) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      have tail := ih (fun next member => literal next (List.mem_cons_of_mem row member))
      simp only [dispatch, equationsFor] at tail
      by_cases same : equationSymbol? row.2 = some symbol
      · simp [dispatch, equationsFor, same, tail]
      · have noMatch := other_literal_equation_does_not_match env symbol arguments row.2
          (literal row (List.mem_cons_self)) same
        simp [dispatch, equationsFor, same, noMatch, tail]

theorem dispatch_append (env : Bindings) (call : SExpr) (left right : List (Nat × SExpr)) :
    dispatch env call (left ++ right) = dispatch env call left ++ dispatch env call right := by
  simp [dispatch]

/-- Appended declarations are harmless only when their actual matching scan
is empty; this condition cannot be inferred from the original program alone. -/
theorem dispatch_append_of_unmatched (env : Bindings) (call : SExpr)
    (program additional : List (Nat × SExpr))
    (unmatched : ∀ row ∈ additional, matchEquation env call row.2 = []) :
    dispatch env call (program ++ additional) = dispatch env call program := by
  rw [dispatch_append]
  have empty : dispatch env call additional = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro row member
    simp [unmatched row member]
  rw [empty, List.append_nil]

theorem dispatch_append_other_literals (env : Bindings) (symbol : String) (arguments : List SExpr)
    (program additional : List (Nat × SExpr))
    (literal : ∀ row ∈ additional, LiteralEquationHead row.2)
    (other : ∀ row ∈ additional, equationSymbol? row.2 ≠ some symbol) :
    dispatch env (.list (.atom symbol :: arguments)) (program ++ additional) =
      dispatch env (.list (.atom symbol :: arguments)) program :=
  dispatch_append_of_unmatched env _ program additional
    (fun row member => other_literal_equation_does_not_match env symbol arguments row.2
      (literal row member) (other row member))

theorem duplicate_rows_are_not_collapsed (env : Bindings) (call : SExpr) (row : Nat × SExpr) :
    dispatch env call [row, row] = dispatch env call [row] ++ dispatch env call [row] := by
  simp [dispatch]

theorem repeated_matching_equation_has_two_occurrences (value : SExpr) :
    let equation := .list [.atom "=", .list [.atom "f", .atom "$x"],
      .list [.atom "quote", .atom "$x"]]
    dispatch [] (.list [.atom "f", value]) [(10, equation), (10, equation)] =
      [((10, equation), [("$x", encode value)]), ((10, equation), [("$x", encode value)])] := by
  dsimp only
  simp [dispatch, matchEquation, equation?, bindResult, template, templates, variableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem repeated_matching_equation_does_not_license_once (value : SExpr) :
    let equation := .list [.atom "=", .list [.atom "f", .atom "$x"],
      .list [.atom "quote", .atom "$x"]]
    let answers := dispatch [] (.list [.atom "f", value]) [(10, equation), (10, equation)]
    answers ≠ answers.take 1 := by
  dsimp only
  have actual := repeated_matching_equation_has_two_occurrences value
  dsimp only at actual
  rw [actual]
  simp

/-- A broad variable-headed equation does match calls discarded by the
literal-symbol filter. This is the required negative dynamic-extension case. -/
theorem broad_head_breaks_literal_filter (value : SExpr) :
    let equation := .list [.atom "=", .atom "$any", .list [.atom "quote", .atom "extra"]]
    dispatch [] (.list [.atom "f", value]) [(10, equation)] ≠
      dispatch [] (.list [.atom "f", value]) (equationsFor "f" [(10, equation)]) := by
  dsimp only
  simp [dispatch, matchEquation, equation?, equationsFor, equationSymbol?, bindResult,
    template, variableToken, matchPattern, mergeBindings]

theorem variable_application_head_breaks_literal_filter (value : SExpr) :
    let equation := .list [.atom "=", .list [.atom "$head", .atom "$x"],
      .list [.atom "quote", .atom "extra"]]
    dispatch [] (.list [.atom "f", value]) [(10, equation)] ≠
      dispatch [] (.list [.atom "f", value]) (equationsFor "f" [(10, equation)]) := by
  dsimp only
  simp [dispatch, matchEquation, equation?, equationsFor, equationSymbol?, bindResult,
    template, templates, variableToken, encode, encodeList, matchPattern, matchArgs,
    mergeBindings, List.foldlM]

theorem malformed_equation_is_not_extracted (head body extra : SExpr) :
    equation? (.list [.atom "=", head, body, extra]) = none := rfl

theorem non_equation_declaration_is_not_extracted (head body : SExpr) :
    equation? (.list [.atom ":", head, body]) = none := rfl

end Mettapedia.GSLT.Parsing.GeneratedPeTTaEquationDispatch
