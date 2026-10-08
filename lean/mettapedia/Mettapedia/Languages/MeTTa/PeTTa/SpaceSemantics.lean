import Algorithms.MeTTa.Simple.Parser
import Mettapedia.GSLT.Parsing.ExactDecimalLexeme
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Lean.Data.Json.Parser

/-!
# PeTTa source atoms, programs and ordered selection

Programs are read into the four-constructor `OSLFCore.Atom`. A bare symbol
differs from a nullary expression, and numbers, strings and Booleans are
grounded values; `True` and `true` read to the same value, as in PeTTa's
reader. Equations keep their source order and declarations keep their arrow
types. `matchValue` threads existing bindings, so a repeated variable tests
its captured value, and the `cons` pattern exposes the head and tail of an
expression. `selectCase` commits to the first matching row. `query`
instantiates a template for every matching stored row, keeping order and
multiplicity.

The text reader is a named boundary until a byte-level reader correspondence
is proved. The selected-rewrite view of atomspaces over `Pattern` is in `PatternRewrite.Space`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa

/-- Literal `Atom` domains retain the supplied syntax. The declaration is
inspected before any binding, so a formal variable is not a raw domain. -/
@[simp] def formalArgumentIsRaw (formal : OSLFCore.Atom) : Bool :=
  formal == .symbol "Atom"

/-- A missing domain cannot request raw syntax. -/
@[simp] theorem optional_formalArgumentIsRaw (formal : Option OSLFCore.Atom) :
    formal.any formalArgumentIsRaw = (formal == some (.symbol "Atom")) := by
  cases formal <;> simp

end Mettapedia.Languages.MeTTa.PeTTa

namespace Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.MORK (Subst matchAtom)
open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.Parsing
open Mettapedia.GSLT.Parsing.ExactDecimalLexeme (parseInteger?)

/-- Printable ASCII characters whose spelling needs no string escape. -/
def plainStringCharacter (character : Char) : Bool :=
  0x20 ≤ character.toNat && character.toNat < 0x7f &&
    character != '"' && character != '\\'

/-- The total plain-string fragment of the shared reader. Escaped or non-ASCII
tokens continue through the existing general string reader. -/
@[simp] def readPlainString (token : String) : Option String :=
  match token.toList with
  | '"' :: rest =>
      if rest.getLast? == some '"' && rest.dropLast.all plainStringCharacter then
        some (String.ofList rest.dropLast)
      else none
  | _ => none

/-- A plain quoted token retains every character, including number-like and
Boolean-like identifier spellings. -/
theorem readPlainString_quoted (body : List Char)
    (plain : body.all plainStringCharacter = true) :
    readPlainString (String.ofList ('"' :: (body ++ ['"']))) =
      some (String.ofList body) := by
  simp [readPlainString, plain]

def readToken (token : String) : Except String Atom :=
  match readPlainString token with
  | some value => .ok (.grounded (.string value))
  | none =>
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

theorem readToken_plain_string (body : List Char)
    (plain : body.all plainStringCharacter = true) :
    readToken (String.ofList ('"' :: (body ++ ['"']))) =
      .ok (.grounded (.string (String.ofList body))) := by
  unfold readToken
  rw [readPlainString_quoted body plain]

theorem plain_reader_keeps_identifier_distinctions :
    readToken "\"01\"" = .ok (.grounded (.string "01")) ∧
      readToken "\"1\"" = .ok (.grounded (.string "1")) ∧
      readToken "\"True\"" = .ok (.grounded (.string "True")) := by
  decide +kernel

theorem plain_reader_rejects_unsafe_tokens :
    readPlainString "\"a\\b\"" = none ∧
      readPlainString "\"a\x00b\"" = none ∧
      readPlainString "\"a\"suffix" = none := by decide +kernel

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

/-- The kind of a loaded top-level form, in source order. -/
inductive FormKind where
  | equation
  | declaration
  | fact
  deriving DecidableEq, Repr

/-- A loaded program. Equations and type declarations are indexed for
evaluation; `facts` holds every other loaded form. `layout` records the source
order of all three kinds, so the loaded atoms are recovered exactly. -/
structure Program where
  equations : List Equation
  declarations : List Atom
  initializers : List Atom := []
  facts : List Atom := []
  layout : List FormKind := []
  deriving Repr

/-- The stored atom of an equation, as loading adds it to `&self`. -/
def Equation.toAtom (equation : Equation) : Atom :=
  .expression [.symbol "=", .expression (.symbol equation.head :: equation.arguments),
    equation.body]

/-- Every top-level form is classified; none is rejected. Equation, declaration
and fact order are retained, and `layout` records how they interleave. -/
def collect : List Atom → Except String Program
  | [] => .ok { equations := [], declarations := [] }
  | form :: rest => do
      let program ← collect rest
      match form with
      | .expression [.symbol "=", .expression (.symbol head :: arguments), body] =>
          .ok { program with equations := ⟨head, arguments, body⟩ :: program.equations
                             layout := .equation :: program.layout }
      | .expression [.symbol ":", _, _] =>
          .ok { program with declarations := form :: program.declarations
                             layout := .declaration :: program.layout }
      | _ =>
          .ok { program with facts := form :: program.facts
                             layout := .fact :: program.layout }

/-- The atoms that loading a program adds to `&self`, in source order. PeTTa
adds every non-request form, equations included, so `match` and `get-atoms`
on `&self` see them. -/
def loadedAtoms (program : Program) : List Atom :=
  go program.layout program.equations program.declarations program.facts
where
  go : List FormKind → List Equation → List Atom → List Atom → List Atom
    | .equation :: kinds, equation :: equations, declarations, facts =>
        equation.toAtom :: go kinds equations declarations facts
    | .declaration :: kinds, equations, declaration :: declarations, facts =>
        declaration :: go kinds equations declarations facts
    | .fact :: kinds, equations, declarations, fact :: facts =>
        fact :: go kinds equations declarations facts
    | _, _, _, _ => []

/-- Loading recovers the source forms exactly: the indexed program loses no
form and no order. -/
theorem loadedAtoms_collect {forms : List Atom} {program : Program}
    (collected : collect forms = .ok program) : loadedAtoms program = forms := by
  induction forms generalizing program with
  | nil =>
      simp only [collect, Except.ok.injEq] at collected
      subst collected
      simp [loadedAtoms, loadedAtoms.go]
  | cons form rest ih =>
      simp only [collect, bind, Except.bind] at collected
      cases restCollected : collect rest with
      | error message => simp [restCollected] at collected
      | ok restProgram =>
          simp only [restCollected] at collected
          have restAtoms := ih restCollected
          split at collected <;> (simp only [Except.ok.injEq] at collected; subst collected)
          all_goals
            simp only [loadedAtoms, loadedAtoms.go, Equation.toAtom] at restAtoms ⊢
            rw [restAtoms]

/-- A program's layout accounts for exactly its equations, declarations and
facts. -/
def Balanced (program : Program) : Prop :=
  program.layout.count .equation = program.equations.length ∧
    program.layout.count .declaration = program.declarations.length ∧
    program.layout.count .fact = program.facts.length

theorem balanced_collect {forms : List Atom} {program : Program}
    (collected : collect forms = .ok program) : Balanced program := by
  induction forms generalizing program with
  | nil =>
      simp only [collect, Except.ok.injEq] at collected
      subst collected
      simp [Balanced]
  | cons form rest ih =>
      simp only [collect, bind, Except.bind] at collected
      cases restCollected : collect rest with
      | error message => simp [restCollected] at collected
      | ok restProgram =>
          simp only [restCollected] at collected
          obtain ⟨equations, declarations, facts⟩ := ih restCollected
          split at collected <;> (simp only [Except.ok.injEq] at collected; subst collected)
          all_goals simp_all [Balanced]

/-- Loading files one after another. -/
def Program.append (first second : Program) : Program where
  equations := first.equations ++ second.equations
  declarations := first.declarations ++ second.declarations
  initializers := first.initializers ++ second.initializers
  facts := first.facts ++ second.facts
  layout := first.layout ++ second.layout

theorem loadedAtoms_go_append :
    ∀ (kinds : List FormKind) (equations : List Equation) (declarations facts : List Atom)
      (laterKinds : List FormKind) (laterEquations : List Equation)
      (laterDeclarations laterFacts : List Atom),
      kinds.count .equation = equations.length →
      kinds.count .declaration = declarations.length →
      kinds.count .fact = facts.length →
      loadedAtoms.go (kinds ++ laterKinds) (equations ++ laterEquations)
          (declarations ++ laterDeclarations) (facts ++ laterFacts) =
        loadedAtoms.go kinds equations declarations facts ++
          loadedAtoms.go laterKinds laterEquations laterDeclarations laterFacts
  | [], equations, declarations, facts, laterKinds, laterEquations, laterDeclarations,
      laterFacts, equationCount, declarationCount, factCount => by
      have : equations = [] := List.eq_nil_of_length_eq_zero (by simpa using equationCount.symm)
      have : declarations = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using declarationCount.symm)
      have : facts = [] := List.eq_nil_of_length_eq_zero (by simpa using factCount.symm)
      subst_vars
      simp [loadedAtoms.go]
  | .equation :: kinds, [], declarations, facts, _, _, _, _, equationCount, _, _ => by
      simp at equationCount
  | .equation :: kinds, equation :: equations, declarations, facts, laterKinds, laterEquations,
      laterDeclarations, laterFacts, equationCount, declarationCount, factCount => by
      simp only [List.cons_append, loadedAtoms.go]
      rw [loadedAtoms_go_append kinds equations declarations facts laterKinds laterEquations
        laterDeclarations laterFacts (by simpa using equationCount)
        (by simpa using declarationCount) (by simpa using factCount)]
  | .declaration :: kinds, equations, [], facts, _, _, _, _, _, declarationCount, _ => by
      simp at declarationCount
  | .declaration :: kinds, equations, declaration :: declarations, facts, laterKinds,
      laterEquations, laterDeclarations, laterFacts, equationCount, declarationCount,
      factCount => by
      simp only [List.cons_append, loadedAtoms.go]
      rw [loadedAtoms_go_append kinds equations declarations facts laterKinds laterEquations
        laterDeclarations laterFacts (by simpa using equationCount)
        (by simpa using declarationCount) (by simpa using factCount)]
  | .fact :: kinds, equations, declarations, [], _, _, _, _, _, _, factCount => by
      simp at factCount
  | .fact :: kinds, equations, declarations, fact :: facts, laterKinds, laterEquations,
      laterDeclarations, laterFacts, equationCount, declarationCount, factCount => by
      simp only [List.cons_append, loadedAtoms.go]
      rw [loadedAtoms_go_append kinds equations declarations facts laterKinds laterEquations
        laterDeclarations laterFacts (by simpa using equationCount)
        (by simpa using declarationCount) (by simpa using factCount)]

/-- Loading a balanced program and then another adds the first program's atoms
and then the second's. -/
theorem loadedAtoms_append {first second : Program} (balanced : Balanced first) :
    loadedAtoms (first.append second) = loadedAtoms first ++ loadedAtoms second := by
  obtain ⟨equations, declarations, facts⟩ := balanced
  exact loadedAtoms_go_append _ _ _ _ _ _ _ _ equations declarations facts

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

/-- A quoted binding pattern denotes literal constructor syntax. Ordinary
patterns retain the evaluator's list view. Matching the quoted syntax uses
the shared structural matcher, so raw `cons` data cannot match a native list. -/
def matchBinding (bindings : Subst) (pattern value : Atom) : Option Subst :=
  match pattern with
  | .expression [.symbol "quote", literal] => matchAtom bindings literal value
  | _ => matchValue bindings pattern value

@[simp] theorem matchBinding_var (bindings : Subst) (name : String) (value : Atom) :
    matchBinding bindings (.var name) value = matchValue bindings (.var name) value := rfl

@[simp] theorem matchBinding_quote (bindings : Subst) (literal value : Atom) :
    matchBinding bindings (.expression [.symbol "quote", literal]) value =
      matchAtom bindings literal value := rfl

theorem matchBinding_ordinary (bindings : Subst) (pattern value : Atom)
    (unquoted : ∀ literal, pattern ≠ .expression [.symbol "quote", literal]) :
    matchBinding bindings pattern value = matchValue bindings pattern value := by
  unfold matchBinding
  split
  · exfalso
    apply unquoted _
    rfl
  · rfl

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

/-- Ordinary expression matching has no list-view interpretation of `cons`.
On literal terms it still agrees with structural equality. -/
theorem matchAtom_literal {pattern : Atom} (literal : Literal pattern)
    (bindings : Subst) (value : Atom) :
    MORK.matchAtom bindings pattern value = if pattern = value then some bindings else none := by
  induction literal generalizing bindings value with
  | symbol name => cases value <;> simp [MORK.matchAtom]
  | grounded ground => cases value <;> simp [MORK.matchAtom]
  | expression patterns notCons members ih =>
      have lists (values : List Atom) : MORK.matchAtom.matchAtomList bindings patterns values =
          if patterns = values then some bindings else none := by
        clear notCons members
        induction patterns generalizing values with
        | nil => cases values <;> simp [MORK.matchAtom.matchAtomList]
        | cons first rest tail =>
            cases values with
            | nil => simp [MORK.matchAtom.matchAtomList]
            | cons value values =>
                simp only [MORK.matchAtom.matchAtomList, ih first List.mem_cons_self bindings value]
                by_cases same : first = value
                · simp only [same, ↓reduceIte, List.cons.injEq, true_and]
                  exact tail (fun item member => ih item (List.mem_cons_of_mem _ member)) values
                · simp [same]
      cases value <;> simp [MORK.matchAtom, lists]

private def SelfBindings (bindings : Subst) : Prop :=
  ∀ name, bindings.lookup name = none ∨ bindings.lookup name = some (.var name)

private theorem matchAtom_self_extends (atom : Atom) (bindings : Subst)
    (selfBindings : SelfBindings bindings) :
    ∃ bound, MORK.matchAtom bindings atom atom = some bound ∧ SelfBindings bound := by
  match atom with
  | .var name =>
      rcases selfBindings name with absent | present
      · refine ⟨(name, .var name) :: bindings, by simp [MORK.matchAtom, absent], ?_⟩
        intro other
        by_cases same : other = name
        · subst other; exact .inr (by simp [Subst.lookup])
        · simpa [Subst.lookup, Ne.symm same] using selfBindings other
      · exact ⟨bindings, by simp [MORK.matchAtom, present], selfBindings⟩
  | .symbol name => exact ⟨bindings, by simp [MORK.matchAtom], selfBindings⟩
  | .grounded value => exact ⟨bindings, by simp [MORK.matchAtom], selfBindings⟩
  | .expression atoms => exact lists atoms bindings selfBindings
where
  lists (atoms : List Atom) (bindings : Subst) (selfBindings : SelfBindings bindings) :
      ∃ bound, MORK.matchAtom.matchAtomList bindings atoms atoms = some bound ∧ SelfBindings bound := by
    match atoms with
    | [] => exact ⟨bindings, rfl, selfBindings⟩
    | first :: rest =>
        obtain ⟨middle, matched, middleSelf⟩ := matchAtom_self_extends first bindings selfBindings
        obtain ⟨bound, matchedRest, boundSelf⟩ := lists rest middle middleSelf
        exact ⟨bound, by simp [MORK.matchAtom.matchAtomList, matched, matchedRest], boundSelf⟩

/-- Even a repeated pattern variable can match its own occurrence consistently.
This is ordinary matching, not a claim that two separately scoped terms alias. -/
theorem matchAtom_self (atom : Atom) : (MORK.matchAtom [] atom atom).isSome = true := by
  obtain ⟨bound, matched, _⟩ := matchAtom_self_extends atom [] (fun _ => .inl rfl)
  simp [matched]

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

end Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

namespace Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (applySubst)

def query (rows : List Atom) (pattern template : Atom) : List Atom :=
  rows.filterMap fun row =>
    (SpaceSemantics.matchValue [] pattern row).map fun bindings => applySubst bindings template

@[simp] theorem query_append (first second : List Atom) (pattern template : Atom) :
    query (first ++ second) pattern template =
      query first pattern template ++ query second pattern template := by
  simp [query]

theorem query_sound {rows : List Atom} {pattern template answer : Atom}
    (found : answer ∈ query rows pattern template) :
    ∃ row ∈ rows, ∃ bindings,
      SpaceSemantics.matchValue [] pattern row = some bindings ∧
        applySubst bindings template = answer := by
  rw [query, List.mem_filterMap] at found
  obtain ⟨row, member, matched⟩ := found
  cases bound : SpaceSemantics.matchValue [] pattern row with
  | none => simp [bound] at matched
  | some bindings =>
      exact ⟨row, member, bindings, bound, by simpa [bound] using matched⟩

theorem query_complete {rows : List Atom} {pattern template row : Atom}
    {bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst}
    (member : row ∈ rows)
    (matched : SpaceSemantics.matchValue [] pattern row = some bindings) :
    applySubst bindings template ∈ query rows pattern template := by
  rw [query, List.mem_filterMap]
  exact ⟨row, member, by simp [matched]⟩

end Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
