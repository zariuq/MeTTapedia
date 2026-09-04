import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueOrder
import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-!
# Ordinary MM2 surface programs

MORK executes ordinary S-expressions, but not every abstract MeTTa atom has a
faithful spelling in that format.  In particular, host-grounded values are not
MM2 symbols, an unescaped delimiter changes the parse, and the compact MORK
representation bounds symbol byte length and expression arity.

This target-owned module makes that boundary explicit.  A source compiler
emits abstract MM2 atoms and then asks this renderer for an ordinary `.mm2`
program.  Unsupported output is refused instead of being silently printed as
a different atom.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

private def classAcceptsChar (className : String) (character : Char) : Bool :=
  (mm2ParserProfile.classAccepts? className character.toNat).getD false

def isWhitespace (character : Char) : Bool :=
  classAcceptsChar "MM2WhitespaceClass" character

/-- Characters that terminate or redirect the ordinary MM2 byte parser. -/
def isBareSymbolDelimiter (character : Char) : Bool :=
  !classAcceptsChar "MM2BareCharClass" character

def hasNoBareDelimiters (value : String) : Bool :=
  value.toList.all fun character => !isBareSymbolDelimiter character

/-- Exact first-character class used by the ordinary MM2 syntax grammar. -/
def isBareSymbolHead (character : Char) : Bool :=
  classAcceptsChar "MM2BareHeadClass" character

/-- Exact continuation-character class used by the ordinary MM2 syntax
grammar. -/
def isBareSymbolChar (character : Char) : Bool :=
  classAcceptsChar "MM2BareCharClass" character

/-- Exact variable-name character class used after the leading `$`. -/
def isVariableChar (character : Char) : Bool :=
  classAcceptsChar "MM2VariableCharClass" character

private theorem optionBool_getD_false_eq_true_iff (value : Option Bool) :
    value.getD false = true ↔ value = some true := by
  cases value with
  | none => simp
  | some result => cases result <;> simp

theorem isWhitespace_eq_true_iff_class (character : Char) :
    isWhitespace character = true ↔
      mm2ParserProfile.classAccepts? "MM2WhitespaceClass"
        character.toNat = some true := by
  simpa [isWhitespace, classAcceptsChar] using
    optionBool_getD_false_eq_true_iff
      (mm2ParserProfile.classAccepts? "MM2WhitespaceClass"
        character.toNat)

theorem isBareSymbolHead_eq_true_iff_class (character : Char) :
    isBareSymbolHead character = true ↔
      mm2ParserProfile.classAccepts? "MM2BareHeadClass"
        character.toNat = some true := by
  simpa [isBareSymbolHead, classAcceptsChar] using
    optionBool_getD_false_eq_true_iff
      (mm2ParserProfile.classAccepts? "MM2BareHeadClass"
        character.toNat)

theorem isBareSymbolChar_eq_true_iff_class (character : Char) :
    isBareSymbolChar character = true ↔
      mm2ParserProfile.classAccepts? "MM2BareCharClass"
        character.toNat = some true := by
  simpa [isBareSymbolChar, classAcceptsChar] using
    optionBool_getD_false_eq_true_iff
      (mm2ParserProfile.classAccepts? "MM2BareCharClass"
        character.toNat)

theorem isVariableChar_eq_true_iff_class (character : Char) :
    isVariableChar character = true ↔
      mm2ParserProfile.classAccepts? "MM2VariableCharClass"
        character.toNat = some true := by
  simpa [isVariableChar, classAcceptsChar] using
    optionBool_getD_false_eq_true_iff
      (mm2ParserProfile.classAccepts? "MM2VariableCharClass"
        character.toNat)

/-- A literal symbol that the MORK reader consumes as exactly one compact
symbol.  Quoted tokens are excluded because the current reader retains their
quote bytes instead of defining a string-literal denotation. -/
def bareSymbolSafe (value : String) : Bool :=
  match value.toList with
  | [] => false
  | head :: tail =>
      (morkUtf8Bytes value).length < 64 &&
        isBareSymbolHead head && tail.all isBareSymbolChar

/-- A variable name follows a leading `$`.  The empty body is the ordinary
bare-dollar variable accepted by the MORK reader. -/
def variableNameSafe (value : String) : Bool :=
  value.toList.all isVariableChar

mutual
  /-- Exact syntactic domain of the ordinary target renderer. -/
  def atomSafe : Atom → Bool
    | .symbol value => bareSymbolSafe value
    | .var name => variableNameSafe name
    | .grounded _ => false
    | .expression children =>
        children.length < 64 && atomsSafe children

  def atomsSafe : List Atom → Bool
    | [] => true
    | atom :: atoms => atomSafe atom && atomsSafe atoms
end

mutual
  /-- Variable names occurring in one rendered atom, in source order and
  with multiplicity.  MORK assigns compact variable slots across the whole
  reader context, not independently per expression. -/
  def atomVariableNames : Atom → List String
    | .symbol _ | .grounded _ => []
    | .var name => [name]
    | .expression children => atomsVariableNames children

  def atomsVariableNames : List Atom → List String
    | [] => []
    | atom :: atoms => atomVariableNames atom ++ atomsVariableNames atoms
end

/-- Exact compact-reader invariant for one top-level form: at most sixty-four
distinct variable spellings may be allocated in its reader context. -/
def atomVariableBudget (atom : Atom) : Bool :=
  (atomVariableNames atom).eraseDups.length ≤ 64

/-- MORK clears the compact-variable table after every top-level form. -/
def programVariableBudget (program : List Atom) : Bool :=
  program.all atomVariableBudget

/-- Canonical ordinary-MM2 renderer domain, including both recursive atom
safety and the reader's file-wide variable table bound. -/
def programSafe (program : List Atom) : Bool :=
  program.all atomSafe && programVariableBudget program

/-- Transparent canonical spelling for the ordinary MM2 atom fragment.
Unlike the generic diagnostic printer, this target-owned renderer is
structurally recursive and can therefore participate in parser-correspondence
theorems. -/
def ordinaryAtomString : Atom → String
  | .symbol value => value
  | .var name => "$" ++ name
  | .grounded value => value.toString
  | .expression atoms => "(" ++ renderAtoms atoms ++ ")"
where
  renderAtoms : List Atom → String
    | [] => ""
    | [atom] => ordinaryAtomString atom
    | atom :: rest => ordinaryAtomString atom ++ " " ++ renderAtoms rest

/-- Render one atom only when the ordinary MM2 parser can represent its
constructors without a dialect extension. -/
def renderAtom? (atom : Atom) : Option String :=
  if atomSafe atom then some (ordinaryAtomString atom) else none

/-- Canonical line-oriented spelling of an ordinary MM2 program. -/
def ordinaryProgramString : List Atom → String
  | [] => ""
  | atom :: rest =>
      ordinaryAtomString atom ++ "\n" ++ ordinaryProgramString rest

/-- Render a sequence of top-level facts and executable directives as one
ordinary `.mm2` file. -/
def renderProgram? (program : List Atom) : Option String :=
  if programSafe program then some (ordinaryProgramString program) else none

theorem renderProgram?_eq_some_iff (program : List Atom) (rendered : String) :
    renderProgram? program = some rendered ↔
      programSafe program = true ∧ rendered = ordinaryProgramString program := by
  by_cases safe : programSafe program = true <;>
    simp [renderProgram?, safe, eq_comm]

theorem programSafe_of_renderProgram?_eq_some
    {program : List Atom} {rendered : String}
    (exact : renderProgram? program = some rendered) :
    programSafe program = true :=
  (renderProgram?_eq_some_iff program rendered).mp exact |>.1

/-! ## Boundary controls -/

theorem ordinary_fact_safe :
    atomSafe (.expression [.symbol "fact", .symbol "a"]) = true := by
  decide +kernel

theorem whitespace_symbol_rejected :
    renderAtom? (.symbol "two tokens") = none := by
  decide +kernel

theorem source_variable_spelling_rejected_as_symbol :
    renderAtom? (.symbol "$x") = none := by
  decide +kernel

theorem grounded_value_rejected :
    renderAtom? (.grounded (.int 7)) = none := by
  decide +kernel

theorem over_arity_expression_rejected :
    renderAtom? (.expression (List.replicate 64 (.symbol "a"))) = none := by
  decide +kernel

theorem two_fact_program_renders :
    ∃ output,
      renderProgram?
        [.expression [.symbol "p", .symbol "a"],
         .expression [.symbol "q", .symbol "b"]] = some output := by
  have pSafe : bareSymbolSafe "p" = true := by decide +kernel
  have aSafe : bareSymbolSafe "a" = true := by decide +kernel
  have qSafe : bareSymbolSafe "q" = true := by decide +kernel
  have bSafe : bareSymbolSafe "b" = true := by decide +kernel
  let first : Atom := .expression [.symbol "p", .symbol "a"]
  let second : Atom := .expression [.symbol "q", .symbol "b"]
  refine ⟨ordinaryProgramString [first, second], ?_⟩
  simp [renderProgram?, programSafe, programVariableBudget,
    atomVariableBudget, atomVariableNames, atomsVariableNames,
    atomSafe, atomsSafe,
    pSafe, aSafe, qSafe, bSafe, first, second]

private def sixtyFiveVariablesAcrossForms : List Atom :=
  (List.range 65).map fun index => .var s!"v{index}"

/-- Distinct names in separate top-level forms do not share a reader context. -/
theorem sixty_five_distinct_variables_across_forms_fit_the_budget :
    programVariableBudget sixtyFiveVariablesAcrossForms = true := by
  decide +kernel

private def sixtyFiveVariablesInOneForm : Atom :=
  .expression [
    .expression ((List.range 33).map fun index => .var s!"v{index}"),
    .expression ((List.range 32).map fun index => .var s!"v{index + 33}")]

/-- Negative control for the per-form compact-variable bound.  Nesting keeps
every expression below the independent sixty-four-child arity limit. -/
theorem sixty_five_distinct_variables_in_one_form_are_rejected :
    renderProgram? [sixtyFiveVariablesInOneForm] = none := by
  decide +kernel

#print axioms ordinary_fact_safe
#print axioms isBareSymbolHead_eq_true_iff_class
#print axioms isBareSymbolChar_eq_true_iff_class
#print axioms isVariableChar_eq_true_iff_class
#print axioms whitespace_symbol_rejected
#print axioms source_variable_spelling_rejected_as_symbol
#print axioms grounded_value_rejected
#print axioms over_arity_expression_rejected
#print axioms renderProgram?_eq_some_iff
#print axioms programSafe_of_renderProgram?_eq_some
#print axioms two_fact_program_renders
#print axioms sixty_five_distinct_variables_across_forms_fit_the_budget
#print axioms sixty_five_distinct_variables_in_one_form_are_rejected

end Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
