import Algorithms.MeTTa.Simple.Parser
import Mettapedia.GSLT.Parsing.ExactDecimalLexeme
import Mettapedia.Data.FreshString
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Lean.Data.Json.Parser
import Mettapedia.Languages.MeTTa.PeTTa.StringLiteral

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

/-- Unicode characters whose spelling needs no string escape. -/
def plainStringCharacter (character : Char) : Bool :=
  0x20 ≤ character.toNat && character.toNat != 0x7f &&
    character != '"' && character != '\\'

/-- The plain-string fragment of the shared reader, read character for
character. Other quoted tokens are decoded by `readQuoted?`. -/
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

/-- A quoted token's string, as CeTTa's reader decodes its body
(`StringLiteral.decodeBody`). -/
def readQuoted? (token : String) : Option String :=
  match token.toList with
  | '"' :: rest => if rest.getLast? == some '"' then StringLiteral.decodeBody rest.dropLast else none
  | _ => none

def readToken (token : String) : Except String Atom :=
  match readPlainString token with
  | some value => .ok (.grounded (.string value))
  | none =>
      if token.startsWith "$" then
        let name := (token.drop 1).toString
        if name.isEmpty then .error "empty source variable" else .ok (.var name)
      else if token = "True" || token = "true" then .ok (.grounded (.bool true))
      else if token = "False" || token = "false" then .ok (.grounded (.bool false))
      else if token.startsWith "\"" then
        match readQuoted? token with
        | some value => .ok (.grounded (.string value))
        | none => .error "expected a quoted string"
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

namespace Anonymous

/- The anonymous source marker denotes a new variable occurrence. Named
variables retain their identity; the support includes the whole authored
syntax before any occurrence is expanded. -/
mutual
  def expand (used : Finset String) : Atom → Finset String × Atom
    | .var name =>
        if name = "_" then
          let fresh := FreshString.fresh used
          (insert fresh used,.var fresh)
        else (used,.var name)
    | .symbol name => (used,.symbol name)
    | .grounded value => (used,.grounded value)
    | .expression items =>
        let result := expandList used items
        (result.1,.expression result.2)

  def expandList (used : Finset String) : List Atom → Finset String × List Atom
    | [] => (used,[])
    | head :: tail =>
        let first := expand used head
        let rest := expandList first.1 tail
        (rest.1,first.2 :: rest.2)
end

/- The source binding condition is independent of the chosen fresh spelling.
Each anonymous occurrence extends the used support, while each named
occurrence and each data constructor is retained. -/
mutual
  inductive Expansion : Finset String → Atom → Finset String → Atom → Prop where
    | anonymous (used : Finset String) (name : String) (fresh : name ∉ used) :
        Expansion used (.var "_") (insert name used) (.var name)
    | named (used : Finset String) (name : String) (ordinary : name ≠ "_") :
        Expansion used (.var name) used (.var name)
    | symbol (used : Finset String) (name : String) :
        Expansion used (.symbol name) used (.symbol name)
    | grounded (used : Finset String) (value : OSLFCore.GroundedValue) :
        Expansion used (.grounded value) used (.grounded value)
    | expression {used next : Finset String} {before after : List Atom} :
        Expansions used before next after →
        Expansion used (.expression before) next (.expression after)

  inductive Expansions : Finset String → List Atom → Finset String → List Atom → Prop where
    | nil (used : Finset String) : Expansions used [] used []
    | cons {used middle next : Finset String} {head value : Atom} {tail values : List Atom} :
        Expansion used head middle value → Expansions middle tail next values →
        Expansions used (head :: tail) next (value :: values)
end

mutual
  theorem expand_sound (used : Finset String) (atom : Atom) :
      Expansion used atom (expand used atom).1 (expand used atom).2 := by
    cases atom with
    | var name =>
        by_cases anonymous : name = "_"
        · subst name
          simpa only [expand,↓reduceIte] using
            Expansion.anonymous used (FreshString.fresh used) (FreshString.fresh_not_mem used)
        · simpa only [expand,anonymous,↓reduceIte] using Expansion.named used name anonymous
    | symbol name => exact .symbol used name
    | grounded value => exact .grounded used value
    | expression items => exact .expression (expandList_sound used items)

  theorem expandList_sound (used : Finset String) (atoms : List Atom) :
      Expansions used atoms (expandList used atoms).1 (expandList used atoms).2 := by
    cases atoms with
    | nil => exact .nil used
    | cons head tail => exact .cons (expand_sound used head) (expandList_sound _ tail)
end

mutual
  theorem Expansion.extends {used next : Finset String} {before after : Atom}
      (source : Expansion used before next after) : used ⊆ next := by
    cases source with
    | anonymous => exact Finset.subset_insert _ _
    | named | symbol | grounded => exact Finset.Subset.refl _
    | expression items => exact items.extends

  theorem Expansions.extends {used next : Finset String} {before after : List Atom}
      (source : Expansions used before next after) : used ⊆ next := by
    cases source with
    | nil => exact Finset.Subset.refl _
    | cons head tail => exact head.extends.trans tail.extends
end

/- Every anonymous occurrence allocates one distinct name outside the
initial support, even when several occurrences have the same token. -/
mutual
  theorem Expansion.card {used next : Finset String} {before after : Atom}
      (source : Expansion used before next after) :
      next.card = used.card + (MORK.atomFreeVars before).count "_" := by
    cases source with
    | anonymous used name fresh => simp [MORK.atomFreeVars,Finset.card_insert_of_notMem fresh]
    | named used name ordinary => simp [MORK.atomFreeVars,ordinary]
    | symbol | grounded => simp [MORK.atomFreeVars]
    | expression items => exact items.card

  theorem Expansions.card {used next : Finset String} {before after : List Atom}
      (source : Expansions used before next after) :
      next.card = used.card + (MORK.atomFreeVars (.expression before)).count "_" := by
    cases source with
    | nil => simp [MORK.atomFreeVars,MORK.atomFreeVars.atomFreeVarsList]
    | cons head tail =>
        have first := head.card
        have rest := tail.card
        simp only [MORK.atomFreeVars] at rest
        simp only [MORK.atomFreeVars,MORK.atomFreeVars.atomFreeVarsList,List.count_append]
        omega
end

mutual
  theorem Expansion.no_marker {used next : Finset String} {before after : Atom}
      (source : Expansion used before next after) (reserved : "_" ∈ used) :
      "_" ∉ MORK.atomFreeVars after := by
    cases source with
    | anonymous used name fresh =>
        intro occurs
        have same : "_" = name := by simpa only [MORK.atomFreeVars,List.mem_singleton] using occurs
        exact fresh (same ▸ reserved)
    | named used name ordinary => simpa only [MORK.atomFreeVars,List.mem_singleton] using ordinary.symm
    | symbol | grounded => simp [MORK.atomFreeVars]
    | expression items => exact items.no_marker reserved

  theorem Expansions.no_marker {used next : Finset String} {before after : List Atom}
      (source : Expansions used before next after) (reserved : "_" ∈ used) :
      "_" ∉ MORK.atomFreeVars (.expression after) := by
    cases source with
    | nil => simp [MORK.atomFreeVars,MORK.atomFreeVars.atomFreeVarsList]
    | cons head tail =>
        have first := head.no_marker reserved
        have rest := tail.no_marker (head.extends reserved)
        simpa only [MORK.atomFreeVars,MORK.atomFreeVars.atomFreeVarsList,List.mem_append,not_or]
          using And.intro first rest
end

mutual
  theorem expand_of_named (used : Finset String) (atom : Atom)
      (named : "_" ∉ MORK.atomFreeVars atom) : expand used atom = (used,atom) := by
    cases atom with
    | var name =>
        have ordinary : name ≠ "_" := by
          intro same
          subst name
          exact named (by simp [MORK.atomFreeVars])
        simp [expand,ordinary]
    | symbol | grounded => rfl
    | expression items => simp only [expand,expandList_of_named used items named]

  theorem expandList_of_named (used : Finset String) (atoms : List Atom)
      (named : "_" ∉ MORK.atomFreeVars (.expression atoms)) :
      expandList used atoms = (used,atoms) := by
    cases atoms with
    | nil => rfl
    | cons head tail =>
        have parts : "_" ∉ MORK.atomFreeVars head ∧ "_" ∉ MORK.atomFreeVars (.expression tail) := by
          simpa only [MORK.atomFreeVars,MORK.atomFreeVars.atomFreeVarsList,List.mem_append,not_or] using named
        simp only [expandList,expand_of_named used head parts.1,expandList_of_named used tail parts.2]
end

/-- One expression uses one support containing all its authored names. -/
def resolve (atom : Atom) : Atom :=
  (expand (insert "_" (MORK.atomFreeVars atom).toFinset) atom).2

/-- Reading several forms reserves names in the complete source packet. -/
def resolveList (atoms : List Atom) : List Atom :=
  (expandList (insert "_" (MORK.atomFreeVars (.expression atoms)).toFinset) atoms).2

theorem resolve_no_marker (atom : Atom) : "_" ∉ MORK.atomFreeVars (resolve atom) :=
  (expand_sound _ atom).no_marker (by simp)

theorem resolveList_no_marker (atoms : List Atom) :
    "_" ∉ MORK.atomFreeVars (.expression (resolveList atoms)) :=
  (expandList_sound _ atoms).no_marker (by simp)

theorem resolve_of_named (atom : Atom) (named : "_" ∉ MORK.atomFreeVars atom) : resolve atom = atom := by
  simp only [resolve,expand_of_named _ atom named]

theorem resolveList_of_named (atoms : List Atom)
    (named : "_" ∉ MORK.atomFreeVars (.expression atoms)) : resolveList atoms = atoms := by
  simp only [resolveList,expandList_of_named _ atoms named]

end Anonymous

mutual
  def readRawExpression : SExpr → Except String Atom
    | .atom token => readToken token
    | .list items => .expression <$> readRawExpressions items

  def readRawExpressions : List SExpr → Except String (List Atom)
    | [] => .ok []
    | item :: items => do
        return (← readRawExpression item) :: (← readRawExpressions items)
end

/-- Bind anonymous occurrences only after all authored variable spellings in
the expression are available. Token conversion itself remains lexical. -/
def readExpression (expression : SExpr) : Except String Atom :=
  (readRawExpression expression).map Anonymous.resolve

def readExpressions (expressions : List SExpr) : Except String (List Atom) :=
  (readRawExpressions expressions).map Anonymous.resolveList

theorem readExpression_named {expression : SExpr} {atom : Atom}
    (read : readRawExpression expression = .ok atom)
    (named : "_" ∉ MORK.atomFreeVars atom) : readExpression expression = .ok atom := by
  simp only [readExpression,read,Except.map,Anonymous.resolve_of_named atom named]

/-- Every successful scoped read has expanded all anonymous markers. -/
theorem readExpression_no_marker {expression : SExpr} {atom : Atom}
    (read : readExpression expression = .ok atom) : "_" ∉ MORK.atomFreeVars atom := by
  unfold readExpression at read
  cases rawRead : readRawExpression expression with
  | error reason => simp only [rawRead,Except.map] at read; cases read
  | ok raw =>
      simp only [rawRead,Except.map] at read
      cases Except.ok.inj read
      exact Anonymous.resolve_no_marker raw

theorem readExpressions_no_marker {expressions : List SExpr} {atoms : List Atom}
    (read : readExpressions expressions = .ok atoms) : "_" ∉ MORK.atomFreeVars (.expression atoms) := by
  unfold readExpressions at read
  cases rawRead : readRawExpressions expressions with
  | error reason => simp only [rawRead,Except.map] at read; cases read
  | ok raw =>
      simp only [rawRead,Except.map] at read
      cases Except.ok.inj read
      exact Anonymous.resolveList_no_marker raw

/-- The scoped reader earns the independent occurrence-binding relation and
its exact allocation count from the lexical result. -/
theorem readExpression_expansion {expression : SExpr} {atom : Atom}
    (read : readExpression expression = .ok atom) :
    ∃ raw used, readRawExpression expression = .ok raw ∧
      Anonymous.Expansion (insert "_" (MORK.atomFreeVars raw).toFinset) raw used atom ∧
      used.card = (insert "_" (MORK.atomFreeVars raw).toFinset).card +
        (MORK.atomFreeVars raw).count "_" := by
  unfold readExpression at read
  cases rawRead : readRawExpression expression with
  | error reason => simp only [rawRead,Except.map] at read; cases read
  | ok raw =>
      simp only [rawRead,Except.map] at read
      cases Except.ok.inj read
      exact ⟨raw,_,rfl,Anonymous.expand_sound _ raw,(Anonymous.expand_sound _ raw).card⟩

theorem reader_anonymous_occurrences_distinct :
    readExpression (.list [.atom "Pair",.atom "$_",.atom "$_"]) =
      .ok (.expression [.symbol "Pair",.var "__",.var "___"]) := by decide +kernel

theorem reader_named_occurrences_correlated :
    readExpression (.list [.atom "Pair",.atom "$x",.atom "$x"]) =
      .ok (.expression [.symbol "Pair",.var "x",.var "x"]) := by decide +kernel

theorem reader_anonymous_avoids_later_named :
    readExpression (.list [.atom "Pair",.atom "$_",.atom "$__"]) =
      .ok (.expression [.symbol "Pair",.var "___",.var "__"]) := by decide +kernel

theorem reader_quoted_marker_is_data :
    readExpression (.list [.atom "Pair",.atom "\"$_\"",.atom "$_"]) =
      .ok (.expression [.symbol "Pair",.grounded (.string "$_"),.var "__"]) := by decide +kernel

theorem reader_anonymous_across_forms_distinct :
    readExpressions [.atom "$_",.atom "$_"] =
      .ok [.var "__",.var "___"] := by decide +kernel

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
    readExpression (.atom "answer") ≠ readExpression (.list [.atom "answer"]) := by decide +kernel

/-- The fresh occurrences are consumed by the actual finite matcher, rather
than merely asserted to have different printed names. -/
theorem anonymous_source_matches_distinct_values :
    (readExpression (.list [.atom "foo",.atom "$_",.atom "$_"])).map
      (fun pattern => (matchValue [] pattern
        (.expression [.symbol "foo",.grounded (.int 1),.grounded (.int 2)])).isSome) =
      .ok true := by decide +kernel

theorem named_source_rejects_distinct_values :
    (readExpression (.list [.atom "foo",.atom "$x",.atom "$x"])).map
      (fun pattern => (matchValue [] pattern
        (.expression [.symbol "foo",.grounded (.int 1),.grounded (.int 2)])).isSome) =
      .ok false := by decide +kernel

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


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Source declaration indexing retains every source occurrence. Equations
supply alternatives in their stored order; declarations and ordinary facts
retain their own order and the common layout records interleaving. -/
inductive Indexes : List Atom → Program → Prop where
  | nil : Indexes [] {equations := [], declarations := []}
  | equation (head : String) (arguments : List Atom) (body : Atom)
      {forms : List Atom} {program : Program} (tail : Indexes forms program) :
      Indexes (.expression [.symbol "=", .expression (.symbol head :: arguments), body] :: forms)
        {program with
          equations := ⟨head, arguments, body⟩ :: program.equations
          layout := .equation :: program.layout}
  | declaration (subject type : Atom) {forms : List Atom} {program : Program}
      (tail : Indexes forms program) :
      Indexes (.expression [.symbol ":", subject, type] :: forms)
        {program with
          declarations := .expression [.symbol ":", subject, type] :: program.declarations
          layout := .declaration :: program.layout}
  | fact (form : Atom) {forms : List Atom} {program : Program}
      (notEquation : ∀ head arguments body,
        form ≠ .expression [.symbol "=", .expression (.symbol head :: arguments), body])
      (notDeclaration : ∀ subject type, form ≠ .expression [.symbol ":", subject, type])
      (tail : Indexes forms program) :
      Indexes (form :: forms)
        {program with
          facts := form :: program.facts
          layout := .fact :: program.layout}

theorem Indexes.collected {forms : List Atom} {program : Program}
    (indexed : Indexes forms program) : collect forms = .ok program := by
  induction indexed with
  | nil => rfl
  | equation head arguments body tail ih => simp [collect, ih, bind, Except.bind]
  | declaration subject type tail ih => simp [collect, ih, bind, Except.bind]
  | fact form notEquation notDeclaration tail ih =>
      simp only [collect, ih, bind, Except.bind]

theorem collect_indexed {forms : List Atom} {program : Program}
    (collected : collect forms = .ok program) : Indexes forms program := by
  induction forms generalizing program with
  | nil =>
      simp only [collect, Except.ok.injEq] at collected
      subst collected
      exact .nil
  | cons form rest ih =>
      simp only [collect, bind, Except.bind] at collected
      cases remaining : collect rest with
      | error reason => simp [remaining] at collected
      | ok tail =>
          simp only [remaining] at collected
          split at collected
          · simp only [Except.ok.injEq] at collected
            subst collected
            exact .equation _ _ _ (ih remaining)
          · simp only [Except.ok.injEq] at collected
            subst collected
            exact .declaration _ _ (ih remaining)
          · rename_i notEquation notDeclaration
            simp only [Except.ok.injEq] at collected
            subst collected
            exact .fact form notEquation notDeclaration (ih remaining)

theorem collect_exact (forms : List Atom) (program : Program) :
    collect forms = .ok program ↔ Indexes forms program :=
  ⟨collect_indexed, Indexes.collected⟩

/-- The original classifier is total, including unknown source forms. -/
theorem collect_succeeds (forms : List Atom) : ∃ program, collect forms = .ok program := by
  induction forms with
  | nil => exact ⟨_, rfl⟩
  | cons form rest ih =>
      obtain ⟨tail, collected⟩ := ih
      simp only [collect, collected, bind, Except.bind]
      split <;> exact ⟨_, rfl⟩

/-- Native indexing reuses the original loader. Its error branch is unreachable
by collect_succeeds, rather than an alternative meaning for unknown syntax. -/
def index (forms : List Atom) : Program :=
  match collect forms with
  | .ok program => program
  | .error _ => {equations := [], declarations := []}

theorem index_collected (forms : List Atom) : collect forms = .ok (index forms) := by
  obtain ⟨program, collected⟩ := collect_succeeds forms
  simp [index, collected]

theorem index_exact (forms : List Atom) : Indexes forms (index forms) :=
  collect_indexed (index_collected forms)

theorem Indexes.unique {forms : List Atom} {first second : Program}
    (left : Indexes forms first) (right : Indexes forms second) : first = second := by
  have same := left.collected.symm.trans right.collected
  exact Except.ok.inj same

theorem Indexes.sourceOccurrences {forms : List Atom} {program : Program}
    (indexed : Indexes forms program) : loadedAtoms program = forms :=
  loadedAtoms_collect indexed.collected

theorem Indexes.sourceMultiplicity {forms : List Atom} {program : Program}
    (indexed : Indexes forms program) (form : Atom) :
    (loadedAtoms program).count form = forms.count form := by
  rw [indexed.sourceOccurrences]

theorem Indexes.balanced {forms : List Atom} {program : Program}
    (indexed : Indexes forms program) : Balanced program :=
  balanced_collect indexed.collected

end Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics



set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst MatchAtomRel)

mutual
  /-- Source matching includes the evaluator's expression-list view for
  `cons`, while all atomic patterns use the independent structural judgment. -/
  inductive ValueMatch : Subst → Atom → Atom → Subst → Prop where
    | cons {initial middle final : Subst} {first rest head : Atom} {tail : List Atom}
        (firstMatch : ValueMatch initial first head middle)
        (restMatch : ValueMatch middle rest (.expression tail) final) :
        ValueMatch initial (.expression [.symbol "cons", first, rest])
          (.expression (head :: tail)) final
    | expression {initial final : Subst} {patterns values : List Atom}
        (ordinary : ∀ first rest, patterns ≠ [.symbol "cons", first, rest])
        (matched : ValueMatches initial patterns values final) :
        ValueMatch initial (.expression patterns) (.expression values) final
    | atomic {initial final : Subst} {pattern value : Atom}
        (atomic : ∀ fields, pattern ≠ .expression fields)
        (matched : MatchAtomRel initial pattern value final) :
        ValueMatch initial pattern value final

  /-- Ordered argument matching threads every actual incoming binding. -/
  inductive ValueMatches : Subst → List Atom → List Atom → Subst → Prop where
    | nil (initial : Subst) : ValueMatches initial [] [] initial
    | cons {initial middle final : Subst} {pattern value : Atom} {patterns values : List Atom}
        (first : ValueMatch initial pattern value middle)
        (remaining : ValueMatches middle patterns values final) :
        ValueMatches initial (pattern :: patterns) (value :: values) final
end

private theorem matchValue_expression (initial : Subst) (patterns values : List Atom)
    (ordinary : ∀ first rest, patterns ≠ [.symbol "cons", first, rest]) :
    matchValue initial (.expression patterns) (.expression values) =
      matchValue.matchValues initial patterns values := by
  rw [matchValue]
  · intro first rest _ _ same _
    exact ordinary first rest same
  · exact ordinary

private theorem matchValue_atomic (initial : Subst) (pattern value : Atom)
    (atomic : ∀ fields, pattern ≠ .expression fields) :
    matchValue initial pattern value =
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom initial pattern value := by
  cases pattern with
  | var _ | symbol _ | grounded _ => simp only [matchValue]
  | expression fields => exact (atomic fields rfl).elim

mutual
  theorem matchValue_sound {initial final : Subst} {pattern value : Atom}
      (computed : matchValue initial pattern value = some final) :
      ValueMatch initial pattern value final := by
    by_cases consView : ∃ first rest, pattern = .expression [.symbol "cons", first, rest]
    · obtain ⟨first, rest, rfl⟩ := consView
      cases value with
      | expression values =>
          cases values with
          | nil => simp only [matchValue] at computed; contradiction
          | cons head tail =>
              cases headMatch : matchValue initial first head with
              | none => simp only [matchValue, headMatch, bind, Option.bind] at computed; contradiction
              | some middle =>
                  have restMatch : matchValue middle rest (.expression tail) = some final := by
                    simpa only [matchValue, headMatch, bind, Option.bind] using computed
                  exact .cons (matchValue_sound headMatch) (matchValue_sound restMatch)
      | var _ | symbol _ | grounded _ => simp only [matchValue] at computed; contradiction
    · cases pattern with
      | var name =>
          have checked : Mettapedia.Languages.ProcessCalculi.MORK.matchAtom initial
              (.var name) value = some final := by simpa only [matchValue] using computed
          exact .atomic (by intro fields impossible; cases impossible)
            (Mettapedia.Languages.ProcessCalculi.MORK.matchAtom_sound checked)
      | symbol name =>
          have checked : Mettapedia.Languages.ProcessCalculi.MORK.matchAtom initial
              (.symbol name) value = some final := by simpa only [matchValue] using computed
          exact .atomic (by intro fields impossible; cases impossible)
            (Mettapedia.Languages.ProcessCalculi.MORK.matchAtom_sound checked)
      | grounded ground =>
          have checked : Mettapedia.Languages.ProcessCalculi.MORK.matchAtom initial
              (.grounded ground) value = some final := by simpa only [matchValue] using computed
          exact .atomic (by intro fields impossible; cases impossible)
            (Mettapedia.Languages.ProcessCalculi.MORK.matchAtom_sound checked)
      | expression patterns =>
          have ordinary : ∀ first rest, patterns ≠ [.symbol "cons", first, rest] := by
            intro first rest same
            exact consView ⟨first, rest, congrArg Atom.expression same⟩
          cases value with
          | expression values =>
              exact .expression ordinary
                (matchValues_sound ((matchValue_expression _ _ _ ordinary).symm ▸ computed))
          | var _ | symbol _ | grounded _ =>
              simp only [matchValue] at computed
              contradiction
    termination_by sizeOf pattern

  theorem matchValues_sound {initial final : Subst} {patterns values : List Atom}
      (computed : matchValue.matchValues initial patterns values = some final) :
      ValueMatches initial patterns values final := by
    cases patterns with
    | nil =>
        cases values with
        | nil => simp only [matchValue.matchValues, Option.some.injEq] at computed; subst final; exact .nil _
        | cons _ _ => simp only [matchValue.matchValues] at computed; contradiction
    | cons pattern patterns =>
        cases values with
        | nil => simp only [matchValue.matchValues] at computed; contradiction
        | cons value values =>
            cases headMatch : matchValue initial pattern value with
            | none => simp only [matchValue.matchValues, headMatch, bind, Option.bind] at computed; contradiction
            | some middle =>
                have restMatch : matchValue.matchValues middle patterns values = some final := by
                  simpa only [matchValue.matchValues, headMatch, bind, Option.bind] using computed
                exact .cons (matchValue_sound headMatch) (matchValues_sound restMatch)
    termination_by sizeOf patterns
end

mutual
  theorem matchValue_complete {initial final : Subst} {pattern value : Atom}
      (source : ValueMatch initial pattern value final) :
      matchValue initial pattern value = some final := by
    cases source with
    | cons first rest =>
        simp only [matchValue, matchValue_complete first, matchValue_complete rest, bind, Option.bind]
    | expression ordinary matched =>
        rw [matchValue_expression _ _ _ ordinary]
        exact matchValues_complete matched
    | atomic atomic matched =>
        rw [matchValue_atomic _ _ _ atomic]
        exact Mettapedia.Languages.ProcessCalculi.MORK.matchAtom_complete matched
    termination_by sizeOf pattern

  theorem matchValues_complete {initial final : Subst} {patterns values : List Atom}
      (source : ValueMatches initial patterns values final) :
      matchValue.matchValues initial patterns values = some final := by
    cases source with
    | nil => simp only [matchValue.matchValues]
    | cons first rest =>
        simp only [matchValue.matchValues, matchValue_complete first,
          matchValues_complete rest, bind, Option.bind]
    termination_by sizeOf patterns
end

@[simp] theorem matchValue_exact (initial : Subst) (pattern value : Atom) (final : Subst) :
    matchValue initial pattern value = some final ↔ ValueMatch initial pattern value final :=
  ⟨matchValue_sound, matchValue_complete⟩

@[simp] theorem matchValues_exact (initial : Subst) (patterns values : List Atom) (final : Subst) :
    matchValue.matchValues initial patterns values = some final ↔ ValueMatches initial patterns values final :=
  ⟨matchValues_sound, matchValues_complete⟩

/-- Binding patterns preserve the original quoted-constructor distinction.
Quotation changes the matching interpretation, not the original Atom syntax. -/
inductive BindingMatch : Subst → Atom → Atom → Subst → Prop where
  | quoted {initial final : Subst} {literal value : Atom}
      (matched : MatchAtomRel initial literal value final) :
      BindingMatch initial (.expression [.symbol "quote", literal]) value final
  | ordinary {initial final : Subst} {pattern value : Atom}
      (unquoted : ∀ literal, pattern ≠ .expression [.symbol "quote", literal])
      (matched : ValueMatch initial pattern value final) :
      BindingMatch initial pattern value final

theorem matchBinding_sound {initial final : Subst} {pattern value : Atom}
    (computed : matchBinding initial pattern value = some final) :
    BindingMatch initial pattern value final := by
  by_cases quoted : ∃ literal, pattern = .expression [.symbol "quote", literal]
  · obtain ⟨literal, rfl⟩ := quoted
    exact .quoted (Mettapedia.Languages.ProcessCalculi.MORK.matchAtom_sound computed)
  · have unquoted : ∀ literal, pattern ≠ .expression [.symbol "quote", literal] := by
      intro literal same
      exact quoted ⟨literal, same⟩
    rw [matchBinding_ordinary _ _ _ unquoted] at computed
    exact .ordinary unquoted (matchValue_sound computed)

theorem matchBinding_complete {initial final : Subst} {pattern value : Atom}
    (source : BindingMatch initial pattern value final) :
    matchBinding initial pattern value = some final := by
  cases source with
  | quoted matched => exact Mettapedia.Languages.ProcessCalculi.MORK.matchAtom_complete matched
  | ordinary unquoted matched =>
      rw [matchBinding_ordinary _ _ _ unquoted]
      exact matchValue_complete matched

@[simp] theorem matchBinding_exact (initial : Subst) (pattern value : Atom) (final : Subst) :
    matchBinding initial pattern value = some final ↔ BindingMatch initial pattern value final :=
  ⟨matchBinding_sound, matchBinding_complete⟩


end Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
