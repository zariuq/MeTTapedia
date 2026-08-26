import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueOrder

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

def isWhitespace : Char → Bool
  | ' ' | '\t' | '\n' => true
  | _ => false

/-- Characters that terminate or redirect the ordinary MM2 byte parser. -/
def isBareSymbolDelimiter (character : Char) : Bool :=
  isWhitespace character || character = '(' || character = ')'

def hasNoBareDelimiters (value : String) : Bool :=
  value.toList.all fun character => !isBareSymbolDelimiter character

/-- A literal symbol that the MORK reader consumes as exactly one compact
symbol.  Quoted tokens are excluded because the current reader retains their
quote bytes instead of defining a string-literal denotation. -/
def bareSymbolSafe (value : String) : Bool :=
  !value.isEmpty &&
    (morkUtf8Bytes value).length < 64 &&
    hasNoBareDelimiters value &&
    !value.startsWith "$" &&
    !value.startsWith ";" &&
    !value.startsWith "\""

/-- A variable name follows a leading `$`; its body must be one nonempty
reader token. -/
def variableNameSafe (value : String) : Bool :=
  !value.isEmpty && hasNoBareDelimiters value

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

/-- Render one atom only when the ordinary MM2 parser can represent its
constructors without a dialect extension. -/
def renderAtom? (atom : Atom) : Option String :=
  if atomSafe atom then some atom.toString else none

/-- Render a sequence of top-level facts and executable directives as one
ordinary `.mm2` file. -/
def renderProgram? (program : List Atom) : Option String := do
  let lines ← program.mapM renderAtom?
  pure ("\n".intercalate lines ++ if lines.isEmpty then "" else "\n")

/-! ## Boundary controls -/

theorem ordinary_fact_safe :
    atomSafe (.expression [.symbol "fact", .symbol "a"]) = true := by
  simp [atomSafe, atomsSafe, bareSymbolSafe,
    hasNoBareDelimiters, isBareSymbolDelimiter, isWhitespace, morkUtf8Bytes,
    Char.utf8Size]

theorem whitespace_symbol_rejected :
    renderAtom? (.symbol "two tokens") = none := by
  simp [renderAtom?, atomSafe, bareSymbolSafe, hasNoBareDelimiters,
    isBareSymbolDelimiter, isWhitespace]

theorem source_variable_spelling_rejected_as_symbol :
    renderAtom? (.symbol "$x") = none := by
  simp [renderAtom?, atomSafe, bareSymbolSafe]

theorem grounded_value_rejected :
    renderAtom? (.grounded (.int 7)) = none := by
  simp [renderAtom?, atomSafe]

theorem over_arity_expression_rejected :
    renderAtom? (.expression (List.replicate 64 (.symbol "a"))) = none := by
  simp [renderAtom?, atomSafe]

theorem two_fact_program_renders :
    ∃ output,
      renderProgram?
        [.expression [.symbol "p", .symbol "a"],
         .expression [.symbol "q", .symbol "b"]] = some output := by
  let first : Atom := .expression [.symbol "p", .symbol "a"]
  let second : Atom := .expression [.symbol "q", .symbol "b"]
  refine ⟨"\n".intercalate [first.toString, second.toString] ++ "\n", ?_⟩
  simp [renderProgram?, renderAtom?, atomSafe, atomsSafe, bareSymbolSafe,
    hasNoBareDelimiters, isBareSymbolDelimiter, isWhitespace, morkUtf8Bytes,
    Char.utf8Size, first, second]

#print axioms ordinary_fact_safe
#print axioms whitespace_symbol_rejected
#print axioms source_variable_spelling_rejected_as_symbol
#print axioms grounded_value_rejected
#print axioms over_arity_expression_rejected
#print axioms two_fact_program_renders

end Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
