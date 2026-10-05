import Algorithms.MeTTa.Simple.Parser
import Mettapedia.GSLT.Parsing.ExactDecimalLexeme
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Lean.Data.Json.Parser

/-!
# PeTTa source atoms and ordered pattern selection

The reader retains the four existing atom constructors. In particular, a bare
symbol is distinct from a nullary expression, and Boolean literals are grounded
values. The source S-expression parser is reused without going through its
symbol-headed Pattern lowering, which loses those distinctions.

The selector below is for constructor patterns, not computations inside a
pattern. Pattern selection threads existing bindings: repeating a variable
tests its captured value. The `cons` pattern exposes the head and tail of an
expression, as in PeTTa's list patterns. Case selection commits to the first
matching row; failure of its body does not authorize a later row.

This is source reading and selection, not yet a recursive evaluator. Raw text
reading is a named boundary until a source-reader correspondence is established.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SourceProgram

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.MORK (Subst matchAtom)
open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.Parsing
open Mettapedia.GSLT.Parsing.ExactDecimalLexeme (parseInteger?)

def readToken (token : String) : Except String Atom :=
  if token.startsWith "$" then
    let name := (token.drop 1).toString
    if name.isEmpty then .error "empty source variable" else .ok (.var name)
  else if token = "True" || token = "true" then .ok (.grounded (.bool true))
  else if token = "False" || token = "false" then .ok (.grounded (.bool false))
  else if token.startsWith "\"" then do
    match ← Lean.Json.parse token with
    | .str value => .ok (.grounded (.string value))
    | _ => .error "expected a quoted string"
  else
    match parseInteger? token with
    | some value => .ok (.grounded (.int value))
    | none => .ok (.symbol token)

mutual
  def readExpression : SExpr → Except String Atom
    | .atom token => readToken token
    | .list items => .expression <$> readExpressions items

  def readExpressions : List SExpr → Except String (List Atom)
    | [] => .ok []
    | item :: items => do
        return (← readExpression item) :: (← readExpressions items)
end

def readSource (source : String) : Except String (List Atom) := do
  let expressions ← (Algorithms.MeTTa.Simple.Parser.parseSExprProgramWithDetailed
    MeTTailCore.MeTTaSyntax.petta source).mapError toString
  readExpressions (expressions.map Prod.snd)

structure Equation where
  head : String
  arguments : List Atom
  body : Atom
  deriving Repr

structure Program where
  equations : List Equation
  declarations : List Atom
  initializers : List Atom := []
  deriving Repr

/-- Equation order is retained. Type declarations remain visible data. -/
def collect : List Atom → Except String Program
  | [] => .ok { equations := [], declarations := [] }
  | form :: rest => do
      let program ← collect rest
      match form with
      | .expression [.symbol "=", .expression (.symbol head :: arguments), body] =>
          .ok { program with equations := ⟨head, arguments, body⟩ :: program.equations }
      | .expression [.symbol ":", _, _] =>
          .ok { program with declarations := form :: program.declarations }
      | _ => .error "expected an equation or type declaration"

def readProgram (source : String) : Except String Program := do
  let forms ← (Algorithms.MeTTa.Simple.Parser.parseSExprCommandsWithDetailed
    MeTTailCore.MeTTaSyntax.petta source).mapError toString
  let decoded ← forms.mapM fun (_, command, expression) => do
    return (command, ← readExpression expression)
  let program ← collect ((decoded.filter (! ·.1)).map Prod.snd)
  return { program with initializers := (decoded.filter Prod.fst).map Prod.snd }

/-- Expression heads occurring in a pattern, including nested patterns. A
symbol by itself is a literal and is not a computation occurrence. -/
def patternHeads : Atom → List String
  | .expression items =>
      (match items with
        | .symbol head :: _ => [head]
        | _ => []) ++ nested items
  | _ => []
termination_by pattern => sizeOf pattern
where
  nested : List Atom → List String
    | [] => []
    | first :: rest => patternHeads first ++ nested rest
  termination_by items => sizeOf items

/-- All `let`, `let*` and `case` patterns in source syntax. This is a structural
inventory, not an evaluator or an analysis of which branches are reachable. -/
def sourcePatterns : Atom → List Atom
  | .expression items =>
      (match items with
        | [.symbol "let", pattern, _, _] => [pattern]
        | [.symbol "let*", .expression pairs, _] => pairs.filterMap fun pair =>
            match pair with
            | .expression [pattern, _] => some pattern
            | _ => none
        | [.symbol "case", _, .expression rows] => rows.filterMap fun row =>
            match row with
            | .expression [pattern, _] => some pattern
            | _ => none
        | _ => []) ++ nested items
  | _ => []
termination_by expression => sizeOf expression
where
  nested : List Atom → List Atom
    | [] => []
    | first :: rest => sourcePatterns first ++ nested rest
  termination_by items => sizeOf items

def programPatterns (program : Program) : List Atom :=
  program.equations.flatMap (fun equation => equation.arguments ++ sourcePatterns equation.body) ++
    program.initializers.flatMap sourcePatterns

/-- Ground-valued pattern selection, including PeTTa's list view. Open cyclic
unification is outside this selector's contract. -/
def matchValue (bindings : Subst) (pattern value : Atom) : Option Subst :=
  match pattern, value with
  | .expression [.symbol "cons", first, rest], .expression (head :: tail) => do
      let bound ← matchValue bindings first head
      matchValue bound rest (.expression tail)
  | .expression [.symbol "cons", _, _], _ => none
  | .expression patterns, .expression values => matchValues bindings patterns values
  | .expression _, _ => none
  | _, _ => matchAtom bindings pattern value
termination_by sizeOf pattern
where
  matchValues (bindings : Subst) : List Atom → List Atom → Option Subst
    | [], [] => some bindings
    | pattern :: patterns, value :: values => do
        let bound ← matchValue bindings pattern value
        matchValues bound patterns values
    | _, _ => none
  termination_by patterns => sizeOf patterns

/-- A closed literal pattern. The special `cons` view is excluded at every
position, so these patterns compare data without binding variables. -/
inductive Literal : Atom → Prop where
  | symbol (name : String) : Literal (.symbol name)
  | grounded (value : MeTTa.OSLFCore.GroundedValue) : Literal (.grounded value)
  | expression (items : List Atom)
      (notCons : ∀ first rest, items ≠ [.symbol "cons", first, rest])
      (members : ∀ item ∈ items, Literal item) : Literal (.expression items)

theorem Literal.constructor (head : String) (arguments : List Atom)
    (ordinary : head ≠ "cons") (members : ∀ item ∈ arguments, Literal item) :
    Literal (.expression (.symbol head :: arguments)) := by
  apply Literal.expression
  · intro first rest same
    exact ordinary (by simpa using (List.cons.inj same).1)
  · intro item member
    rcases List.mem_cons.mp member with same | member
    · subst item; exact Literal.symbol head
    · exact members item member

theorem matchValue_expression_of_not_cons (bindings : Subst) (patterns values : List Atom)
    (notCons : ∀ first rest, patterns ≠ [.symbol "cons", first, rest]) :
    matchValue bindings (.expression patterns) (.expression values) =
      matchValue.matchValues bindings patterns values := by
  unfold matchValue
  split <;> simp_all

/-- Literal selection is structural equality and preserves incoming bindings. -/
theorem matchValue_literal {pattern : Atom} (literal : Literal pattern)
    (bindings : Subst) (value : Atom) :
    matchValue bindings pattern value = if pattern = value then some bindings else none := by
  induction literal generalizing bindings value with
  | symbol name => cases value <;> simp [matchValue, MORK.matchAtom]
  | grounded ground => cases value <;> simp [matchValue, MORK.matchAtom]
  | expression patterns notCons members ih =>
      have lists (values : List Atom) : matchValue.matchValues bindings patterns values =
          if patterns = values then some bindings else none := by
        clear notCons members
        induction patterns generalizing values with
        | nil => cases values <;> simp [matchValue.matchValues]
        | cons first rest tail =>
            cases values with
            | nil => simp [matchValue.matchValues]
            | cons value values =>
                simp only [matchValue.matchValues, ih first List.mem_cons_self bindings value]
                by_cases same : first = value
                · simp only [same, ↓reduceIte, List.cons.injEq, true_and]
                  exact tail (fun item member => ih item (List.mem_cons_of_mem _ member)) values
                · simp [same]
      cases value with
      | expression values =>
          rw [matchValue_expression_of_not_cons bindings patterns values notCons, lists]
          simp
      | var name | symbol name | grounded ground =>
          unfold matchValue
          split <;> simp_all

abbrev Cases := List (Atom × Atom)

def selectCase (bindings : Subst) (value : Atom) : Cases → Option (Subst × Atom)
  | [] => none
  | (pattern, body) :: rest =>
      match matchValue bindings pattern value with
      | some bound => some (bound, body)
      | none => selectCase bindings value rest

/-- An independent finite derivation records each skipped row and the selected
row. No premise refers to the result of `selectCase`. -/
inductive Selected (bindings : Subst) (value : Atom) : Cases → Subst → Atom → Prop where
  | first {pattern body rest bound}
      (matched : matchValue bindings pattern value = some bound) :
      Selected bindings value ((pattern, body) :: rest) bound body
  | later {pattern body rest bound selected}
      (failed : matchValue bindings pattern value = none)
      (tail : Selected bindings value rest bound selected) :
      Selected bindings value ((pattern, body) :: rest) bound selected

theorem selectCase_sound {bindings : Subst} {value : Atom} {cases : Cases}
    {bound : Subst} {body : Atom}
    (selected : selectCase bindings value cases = some (bound, body)) :
    Selected bindings value cases bound body := by
  induction cases with
  | nil => simp [selectCase] at selected
  | cons row rest ih =>
      rcases row with ⟨pattern, candidate⟩
      cases matched : matchValue bindings pattern value with
      | none =>
          exact .later matched (ih (by simpa [selectCase, matched] using selected))
      | some environment =>
          simp only [selectCase, matched, Option.some.injEq, Prod.mk.injEq] at selected
          obtain ⟨rfl, rfl⟩ := selected
          exact .first matched

theorem selectCase_complete {bindings : Subst} {value : Atom} {cases : Cases}
    {bound : Subst} {body : Atom} (selected : Selected bindings value cases bound body) :
    selectCase bindings value cases = some (bound, body) := by
  induction selected with
  | first matched => simp [selectCase, matched]
  | later failed _ tail => simpa [selectCase, failed] using tail

theorem selectCase_iff {bindings : Subst} {value : Atom} {cases : Cases}
    {bound : Subst} {body : Atom} :
    selectCase bindings value cases = some (bound, body) ↔
      Selected bindings value cases bound body :=
  ⟨selectCase_sound, selectCase_complete⟩

theorem selected_unique {bindings : Subst} {value : Atom} {cases : Cases}
    {first second : Subst} {left right : Atom}
    (one : Selected bindings value cases first left)
    (two : Selected bindings value cases second right) : first = second ∧ left = right := by
  have equal := (selectCase_complete one).symm.trans (selectCase_complete two)
  exact Prod.mk.inj (Option.some.inj equal)

theorem selected_body_cannot_fall_through (bindings : Subst) (value pattern body : Atom)
    (rest : Cases) (bound : Subst)
    (matched : matchValue bindings pattern value = some bound) :
    selectCase bindings value ((pattern, body) :: rest) = some (bound, body) := by
  simp [selectCase, matched]

/-! ## Source and selection controls -/

theorem boolean_token_is_grounded : readToken "True" = .ok (.grounded (.bool true)) := by
  simp [readToken]

theorem lowercase_boolean_token_is_grounded :
    readToken "false" = .ok (.grounded (.bool false)) := by
  simp [readToken]

theorem symbol_is_not_a_nullary_expression :
    readExpression (.atom "answer") ≠ readExpression (.list [.atom "answer"]) := by
  simp [readExpression, readExpressions, readToken, parseInteger?,
    ExactDecimalLexeme.parseIntegerChars?, ExactDecimalLexeme.parseUnsignedChars?,
    ExactDecimalLexeme.parseDigits?, ExactDecimalLexeme.decimalDigit?]
  change Except.ok (Atom.symbol "answer") ≠
    (Except.ok (Atom.expression [.symbol "answer"]) : Except String Atom)
  intro equal
  cases equal

theorem cons_pattern_exposes_tail :
    matchValue [] (.expression [.symbol "cons", .var "head", .var "tail"])
      (.expression [.symbol "first", .symbol "second"]) =
      some [("tail", .expression [.symbol "second"]), ("head", .symbol "first")] := by
  simp [matchValue, matchAtom, MORK.Subst.lookup]

theorem repeated_variable_requires_same_value :
    matchValue [] (.expression [.var "item", .var "item"])
      (.expression [.symbol "first", .symbol "second"]) = none := by
  simp [matchValue, matchValue.matchValues, matchAtom, MORK.Subst.lookup]

theorem first_match_retains_order :
    selectCase [] (.symbol "value")
      [(.var "item", .symbol "first"), (.var "item", .symbol "second")] =
      some ([("item", .symbol "value")], .symbol "first") := by
  simp [selectCase, matchValue, matchAtom, MORK.Subst.lookup]

end Mettapedia.Languages.MeTTa.PeTTa.SourceProgram
