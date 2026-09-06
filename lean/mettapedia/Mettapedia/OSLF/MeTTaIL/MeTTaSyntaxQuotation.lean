import Algorithms.MeTTa.Simple.Parser
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mathlib.Data.Multiset.Defs

/-!
# Compile-time quotations for MeTTa expressions

This module connects the executable MeTTa parser to Mettapedia's richer
locally-nameless `Pattern` type.  A quotation such as

```lean
metta% petta "(request $channel (payload $value))"
```

is parsed while Lean elaborates the containing file and expands to an
ordinary `Mettapedia.OSLF.MeTTaIL.Syntax.Pattern` constructor tree.  The
kernel subsequently checks that tree like any handwritten Lean term; no
parser result or string remains in the theorem term.

The dialect is mandatory.  `petta` and `he` select the corresponding pinned
`MeTTailCore.MeTTaSyntax.SyntaxSpec`; there is no implicit default whose
meaning could drift.

Scope:

* the current executable expression parser recognizes atoms, `$`-variables,
  and S-expressions;
* it does not elaborate a raw expression into an intrinsically typed MeTTa
  Native term;
* parser correctness is a separate obligation from kernel checking of the
  expanded term.  The positive and negative computations below exercise the
  actual parser, while `metta%` turns parser failure into an elaboration
  error.
-/

namespace Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

open Lean

abbrev CoreCollType := MeTTailCore.MeTTaIL.Syntax.CollType
abbrev CorePattern := MeTTailCore.MeTTaIL.Syntax.Pattern
abbrev Pattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
abbrev ParseError := Algorithms.MeTTa.Simple.Parser.ParseError
abbrev SyntaxSpec := MeTTailCore.MeTTaSyntax.SyntaxSpec

/-- The core executable AST embeds into the richer specification AST.
Core binders have no retained display names, so their metadata is set to
`none`/`[]`; the binding structure and every other constructor are retained. -/
def coreCollTypeToPatternCollType :
    CoreCollType → Mettapedia.OSLF.MeTTaIL.Syntax.CollType
  | .vec => .vec
  | .hashBag => .hashBag
  | .hashSet => .hashSet

mutual
  /-- Structural embedding of the executable parser's AST into Mettapedia's
  specification AST. -/
  def corePatternToPattern : CorePattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        .apply constructor (corePatternsToPatterns arguments)
    | .lambda body => .lambda none (corePatternToPattern body)
    | .multiLambda count body =>
        .multiLambda count [] (corePatternToPattern body)
    | .subst body replacement =>
        .subst (corePatternToPattern body) (corePatternToPattern replacement)
    | .collection collectionType elements rest =>
        .collection (coreCollTypeToPatternCollType collectionType)
          (corePatternsToPatterns elements) rest

  def corePatternsToPatterns : List CorePattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        corePatternToPattern pattern :: corePatternsToPatterns patterns
end

/-- Runtime form of the same boundary used by `metta%`. -/
def parsePatternWith (spec : SyntaxSpec) (source : String) :
    Except ParseError Pattern :=
  (Algorithms.MeTTa.Simple.Parser.parseExprWithDetailed spec source).map
    corePatternToPattern

/-- Parse one PeTTa expression into the Mettapedia pattern carrier. -/
def parsePeTTaPattern (source : String) : Except ParseError Pattern :=
  parsePatternWith MeTTailCore.MeTTaSyntax.petta source

/-- Parse one HE expression into the Mettapedia pattern carrier. -/
def parseHEPattern (source : String) : Except ParseError Pattern :=
  parsePatternWith MeTTailCore.MeTTaSyntax.he source

private def mkStringTerm (value : String) : TSyntax `term :=
  ⟨Syntax.mkStrLit value⟩

private def mkTermList : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => `([])
  | term :: terms => do
      let tail ← mkTermList terms
      `($term :: $tail)

private def quoteCollType : CoreCollType → MacroM (TSyntax `term)
  | .vec =>
      `(Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec)
  | .hashBag =>
      `(Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag)
  | .hashSet =>
      `(Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashSet)

private partial def quoteCorePattern : CorePattern → MacroM (TSyntax `term)
  | .bvar index =>
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.bvar $(quote index))
  | .fvar name =>
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar $(mkStringTerm name))
  | .apply constructor arguments => do
      let quotedArguments ← arguments.mapM quoteCorePattern
      let argumentList ← mkTermList quotedArguments
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply
          $(mkStringTerm constructor) $argumentList)
  | .lambda body => do
      let quotedBody ← quoteCorePattern body
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.lambda none $quotedBody)
  | .multiLambda count body => do
      let quotedBody ← quoteCorePattern body
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.multiLambda
          $(quote count) [] $quotedBody)
  | .subst body replacement => do
      let quotedBody ← quoteCorePattern body
      let quotedReplacement ← quoteCorePattern replacement
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.subst
          $quotedBody $quotedReplacement)
  | .collection collectionType elements rest => do
      let quotedCollectionType ← quoteCollType collectionType
      let quotedElements ← elements.mapM quoteCorePattern
      let elementList ← mkTermList quotedElements
      let quotedRest ← match rest with
        | none => `(none)
        | some name => `(some $(mkStringTerm name))
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.collection
          $quotedCollectionType $elementList $quotedRest)

private def expandQuotation (spec : SyntaxSpec) (source : TSyntax `str) :
    MacroM (TSyntax `term) := do
  match Algorithms.MeTTa.Simple.Parser.parseExprWithDetailed spec source.getString with
  | .ok pattern => quoteCorePattern pattern
  | .error error =>
      Macro.throwErrorAt source
        s!"MeTTa expression parse failed: {error.render}"

scoped syntax (name := mettaPatternQuotation)
  "metta% " (&"petta" <|> &"he") str : term

scoped macro_rules
  | `(metta% petta $source:str) =>
      expandQuotation MeTTailCore.MeTTaSyntax.petta source
  | `(metta% he $source:str) =>
      expandQuotation MeTTailCore.MeTTaSyntax.he source

/-! ## Complete authored programs -/

/-- A MeTTa source command whose embedded expressions live in `Atom`.

The parameter is important: program-level elaborators can replace each raw
pattern with a proof-carrying plan without losing whether it occurred in a
fact, equation, rule premise, type declaration, effect, or directive. -/
inductive ProgramCommand (Atom : Type) where
  | empty
  | eval (term : Atom)
  | fact (term : Atom)
  | defineEq (left right : Atom)
  | defineRule (left right : Atom) (premises : List Atom)
  | defineType (term type : Atom)
  | relationFact (relation : String) (arguments : List Atom)
  | builtinFact (relation : String) (arguments : List Atom)
  | setFuel (fuel : Nat)
  | import (module name : Atom)
  | newSpace (name : String)
  | addAtom (space term : Atom)
  | removeAtom (space term : Atom)
  | directive (name : String) (arguments : List Atom)
deriving Repr, DecidableEq

namespace ProgramCommand

/-- Map a list while exposing stable coordinates beginning at `start`.
Keeping the offset explicit makes command-local source coordinates available
without depending on the implementation details of `List.mapIdx`. -/
def mapIdxFrom (start : Nat) (f : Nat → α → β) : List α → List β
  | [] => []
  | value :: values =>
      f start value :: mapIdxFrom (start + 1) f values

@[simp] theorem map_mapIdxFrom_of_leftInverse (start : Nat)
    (f : Nat → α → β) (g : β → α)
    (leftInverse : ∀ index value, g (f index value) = value)
    (values : List α) :
    (mapIdxFrom start f values).map g = values := by
  induction values generalizing start with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [mapIdxFrom, leftInverse, inductionHypothesis]

/-- Map every embedded expression while retaining the exact command shape. -/
def map (f : α → β) : ProgramCommand α → ProgramCommand β
  | .empty => .empty
  | .eval term => .eval (f term)
  | .fact term => .fact (f term)
  | .defineEq left right => .defineEq (f left) (f right)
  | .defineRule left right premises =>
      .defineRule (f left) (f right) (premises.map f)
  | .defineType term type => .defineType (f term) (f type)
  | .relationFact relation arguments =>
      .relationFact relation (arguments.map f)
  | .builtinFact relation arguments =>
      .builtinFact relation (arguments.map f)
  | .setFuel fuel => .setFuel fuel
  | .import module name => .import (f module) (f name)
  | .newSpace name => .newSpace name
  | .addAtom space term => .addAtom (f space) (f term)
  | .removeAtom space term => .removeAtom (f space) (f term)
  | .directive name arguments => .directive name (arguments.map f)

/-- Map embedded expressions with their command-local coordinate.  Coordinates
are stable under the map and enumerate a rule as left, right, then premises. -/
def mapIdx (f : Nat → α → β) : ProgramCommand α → ProgramCommand β
  | .empty => .empty
  | .eval term => .eval (f 0 term)
  | .fact term => .fact (f 0 term)
  | .defineEq left right => .defineEq (f 0 left) (f 1 right)
  | .defineRule left right premises =>
      .defineRule (f 0 left) (f 1 right)
        (mapIdxFrom 2 f premises)
  | .defineType term type => .defineType (f 0 term) (f 1 type)
  | .relationFact relation arguments =>
      .relationFact relation (mapIdxFrom 0 f arguments)
  | .builtinFact relation arguments =>
      .builtinFact relation (mapIdxFrom 0 f arguments)
  | .setFuel fuel => .setFuel fuel
  | .import module name => .import (f 0 module) (f 1 name)
  | .newSpace name => .newSpace name
  | .addAtom space term => .addAtom (f 0 space) (f 1 term)
  | .removeAtom space term => .removeAtom (f 0 space) (f 1 term)
  | .directive name arguments => .directive name (mapIdxFrom 0 f arguments)

@[simp] theorem map_id (command : ProgramCommand α) :
    command.map id = command := by
  cases command <;> simp [map]

@[simp] theorem map_map (g : β → γ) (f : α → β)
    (command : ProgramCommand α) :
    (command.map f).map g = command.map (g ∘ f) := by
  cases command <;> simp [map, Function.comp_def]

@[simp] theorem map_mapIdx_of_leftInverse (f : Nat → α → β)
    (g : β → α) (leftInverse : ∀ index value, g (f index value) = value)
    (command : ProgramCommand α) :
    (command.mapIdx f).map g = command := by
  cases command <;>
    simp [map, mapIdx, leftInverse, map_mapIdxFrom_of_leftInverse]

end ProgramCommand

/-- One source line and its parsed command. Empty/comment-only lines are
retained when the executable parser reports them. -/
abbrev Program (Atom : Type) := List (Nat × ProgramCommand Atom)

/-- The equation declarations of a program, discarding source locations and
all non-equation commands while preserving multiplicity. -/
def equationOccurrences (program : Program Atom) : List (Atom × Atom) :=
  program.filterMap fun row =>
    match row.2 with
    | .defineEq left right => some (left, right)
    | _ => none

/-- Equations have bag semantics at the program-package boundary: source
order is forgotten, but duplicate declarations remain observable. -/
def equationBag (program : Program Atom) : Multiset (Atom × Atom) :=
  equationOccurrences program

/-- The authored declarations that define a program's reusable semantics,
discarding source locations, empty rows, and top-level observation commands.

This is intentionally narrower than a whole-dialect semantics: PeTTa `test`
and HE `assertEqual` commands are observations of the shared declarations, not
declarations themselves.  Their exclusion lets paired curriculum files state
precisely which constructor-level program is common without claiming a global
dialect translation theorem. -/
def semanticDeclarations (program : Program Atom) : List (ProgramCommand Atom) :=
  program.filterMap fun row =>
    match row.2 with
    | .empty | .eval _ | .directive _ _ => none
    | command => some command

/-- Source-line changes and observation commands do not affect the semantic
declaration projection. -/
@[simp] theorem semanticDeclarations_cons_eval (line : Nat) (term : Atom)
    (program : Program Atom) :
    semanticDeclarations ((line, .eval term) :: program) =
      semanticDeclarations program := by
  rfl

/-- Reordering declarations cannot change the equation bag.  This is
deliberately not a theorem about nominal declarations, whose first source
occurrence is semantically authoritative. -/
theorem equationBag_eq_of_perm {first second : Program Atom}
    (permutation : first.Perm second) :
    equationBag first = equationBag second := by
  rw [equationBag, equationBag, Multiset.coe_eq_coe]
  exact permutation.filterMap _

abbrev CoreProgramCommand := MeTTailCore.MeTTaSyntax.SyntaxCommand

/-- Structural embedding of a parser command into the specification carrier. -/
def coreProgramCommandToProgramCommand :
    CoreProgramCommand → ProgramCommand Pattern
  | .empty => .empty
  | .eval term => .eval (corePatternToPattern term)
  | .fact term => .fact (corePatternToPattern term)
  | .defineEq left right =>
      .defineEq (corePatternToPattern left) (corePatternToPattern right)
  | .defineRule left right premises =>
      .defineRule (corePatternToPattern left) (corePatternToPattern right)
        (corePatternsToPatterns premises)
  | .defineType term type =>
      .defineType (corePatternToPattern term) (corePatternToPattern type)
  | .relationFact relation arguments =>
      .relationFact relation (corePatternsToPatterns arguments)
  | .builtinFact relation arguments =>
      .builtinFact relation (corePatternsToPatterns arguments)
  | .setFuel fuel => .setFuel fuel
  | .import module name =>
      .import (corePatternToPattern module) (corePatternToPattern name)
  | .newSpace name => .newSpace name
  | .addAtom space term =>
      .addAtom (corePatternToPattern space) (corePatternToPattern term)
  | .removeAtom space term =>
      .removeAtom (corePatternToPattern space) (corePatternToPattern term)
  | .directive name arguments =>
      .directive name (corePatternsToPatterns arguments)

/-- Parse a complete source string, retaining line numbers and command forms. -/
def parseProgramWith (spec : SyntaxSpec) (source : String) :
    Except String (Program Pattern) :=
  (Algorithms.MeTTa.Simple.Parser.parseProgramWith spec source).map fun rows =>
    rows.map fun row => (row.1, coreProgramCommandToProgramCommand row.2)

def parsePeTTaProgram (source : String) : Except String (Program Pattern) :=
  parseProgramWith MeTTailCore.MeTTaSyntax.petta source

def parseHEProgram (source : String) : Except String (Program Pattern) :=
  parseProgramWith MeTTailCore.MeTTaSyntax.he source

private def quoteProgramCommand :
    CoreProgramCommand → MacroM (TSyntax `term)
  | .empty =>
      `(ProgramCommand.empty)
  | .eval term => do
      let quoted ← quoteCorePattern term
      `(ProgramCommand.eval $quoted)
  | .fact term => do
      let quoted ← quoteCorePattern term
      `(ProgramCommand.fact $quoted)
  | .defineEq left right => do
      let quotedLeft ← quoteCorePattern left
      let quotedRight ← quoteCorePattern right
      `(ProgramCommand.defineEq $quotedLeft $quotedRight)
  | .defineRule left right premises => do
      let quotedLeft ← quoteCorePattern left
      let quotedRight ← quoteCorePattern right
      let quotedPremises ← premises.mapM quoteCorePattern >>= mkTermList
      `(ProgramCommand.defineRule $quotedLeft $quotedRight $quotedPremises)
  | .defineType term type => do
      let quotedTerm ← quoteCorePattern term
      let quotedType ← quoteCorePattern type
      `(ProgramCommand.defineType $quotedTerm $quotedType)
  | .relationFact relation arguments => do
      let quotedArguments ← arguments.mapM quoteCorePattern >>= mkTermList
      `(ProgramCommand.relationFact $(mkStringTerm relation) $quotedArguments)
  | .builtinFact relation arguments => do
      let quotedArguments ← arguments.mapM quoteCorePattern >>= mkTermList
      `(ProgramCommand.builtinFact $(mkStringTerm relation) $quotedArguments)
  | .setFuel fuel =>
      let quotedFuel : TSyntax `term := ⟨Syntax.mkNumLit (toString fuel)⟩
      `(ProgramCommand.setFuel $quotedFuel)
  | .import module name => do
      let quotedModule ← quoteCorePattern module
      let quotedName ← quoteCorePattern name
      `(ProgramCommand.import $quotedModule $quotedName)
  | .newSpace name =>
      `(ProgramCommand.newSpace $(mkStringTerm name))
  | .addAtom space term => do
      let quotedSpace ← quoteCorePattern space
      let quotedTerm ← quoteCorePattern term
      `(ProgramCommand.addAtom $quotedSpace $quotedTerm)
  | .removeAtom space term => do
      let quotedSpace ← quoteCorePattern space
      let quotedTerm ← quoteCorePattern term
      `(ProgramCommand.removeAtom $quotedSpace $quotedTerm)
  | .directive name arguments => do
      let quotedArguments ← arguments.mapM quoteCorePattern >>= mkTermList
      `(ProgramCommand.directive $(mkStringTerm name) $quotedArguments)

private def expandProgramSource (spec : SyntaxSpec) (contents : String)
    (origin : Syntax) : MacroM (TSyntax `term) := do
  match Algorithms.MeTTa.Simple.Parser.parseProgramWith spec contents with
  | .error error =>
      Macro.throwErrorAt origin s!"MeTTa program parse failed: {error}"
  | .ok rows =>
      let quotedRows ← rows.mapM fun row => do
        let quotedLine : TSyntax `term :=
          ⟨Syntax.mkNumLit (toString row.1)⟩
        let quotedCommand ← quoteProgramCommand row.2
        `(($quotedLine, $quotedCommand))
      mkTermList quotedRows

private def expandProgramQuotation (spec : SyntaxSpec)
    (source : TSyntax `str) : MacroM (TSyntax `term) :=
  expandProgramSource spec source.getString source

scoped syntax (name := mettaProgramQuotation)
  "metta_program% " (&"petta" <|> &"he") str : term

scoped macro_rules
  | `(metta_program% petta $source:str) =>
      expandProgramQuotation MeTTailCore.MeTTaSyntax.petta source
  | `(metta_program% he $source:str) =>
      expandProgramQuotation MeTTailCore.MeTTaSyntax.he source

scoped syntax (name := mettaProgramFileQuotation)
  "metta_program_file% " (&"petta" <|> &"he") str : term

open Lean.Elab Term

/-- Read and expand a complete authored program relative to the Lean file that
quotes it.  Expansion emits only `ProgramCommand` and `Pattern` constructors;
neither file I/O nor the parser remains in the resulting theorem term. -/
private def elaborateProgramFile (spec : SyntaxSpec) (path : TSyntax `str)
    (expectedType : Expr) : TermElabM Expr := do
  let context ← readThe Lean.Core.Context
  let currentFile := System.FilePath.mk context.fileName
  let some parent := currentFile.parent
    | throwErrorAt path "cannot determine the quoting file's parent directory"
  let sourcePath := parent / path.getString
  let contents ← IO.FS.readFile sourcePath
  let quoted ← liftMacroM <| expandProgramSource spec contents path
  elabTerm quoted expectedType

elab_rules : term <= expectedType
  | `(metta_program_file% petta $path:str) =>
      elaborateProgramFile MeTTailCore.MeTTaSyntax.petta path expectedType
  | `(metta_program_file% he $path:str) =>
      elaborateProgramFile MeTTailCore.MeTTaSyntax.he path expectedType

/-! ## Source S-expressions before pattern lowering -/

private partial def quoteSExpr :
    Algorithms.MeTTa.Simple.Parser.SExpr → MacroM (TSyntax `term)
  | .atom token =>
      `(Algorithms.MeTTa.Simple.Parser.SExpr.atom $(mkStringTerm token))
  | .list elements => do
      let elements ← elements.mapM quoteSExpr >>= mkTermList
      `(Algorithms.MeTTa.Simple.Parser.SExpr.list $elements)

private def expandSExprSource (spec : SyntaxSpec) (contents : String)
    (origin : Syntax) : MacroM (TSyntax `term) := do
  match Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed spec contents with
  | .ok expression => quoteSExpr expression
  | .error error =>
      Macro.throwErrorAt origin s!"MeTTa S-expression parse failed: {error.render}"

/-- Quote the existing reader's S-expression without erasing list structure.
Unlike pattern quotation, `name` and `(name)` remain distinguishable. -/
scoped syntax "metta_sexpr% " (&"petta" <|> &"he") str : term

scoped macro_rules
  | `(metta_sexpr% petta $source:str) =>
      expandSExprSource MeTTailCore.MeTTaSyntax.petta source.getString source
  | `(metta_sexpr% he $source:str) =>
      expandSExprSource MeTTailCore.MeTTaSyntax.he source.getString source

scoped syntax "metta_sexpr_file% " (&"petta" <|> &"he") str : term

private def elaborateSExprFile (spec : SyntaxSpec) (path : TSyntax `str)
    (expectedType : Expr) : TermElabM Expr := do
  let context ← readThe Lean.Core.Context
  let currentFile := System.FilePath.mk context.fileName
  let some parent := currentFile.parent
    | throwErrorAt path "cannot determine the quoting file's parent directory"
  let contents ← IO.FS.readFile (parent / path.getString)
  let quoted ← liftMacroM <| expandSExprSource spec contents path
  elabTerm quoted expectedType

elab_rules : term <= expectedType
  | `(metta_sexpr_file% petta $path:str) =>
      elaborateSExprFile MeTTailCore.MeTTaSyntax.petta path expectedType
  | `(metta_sexpr_file% he $path:str) =>
      elaborateSExprFile MeTTailCore.MeTTaSyntax.he path expectedType

/-- Read a line-oriented sequence through the existing single-expression
reader. Blank lines are skipped; each other line must contain exactly one
complete expression. Neither list structure nor repeated rows are erased.
The first malformed row fails the entire read with its physical line number. -/
def parseSExprLinesWithDetailed (spec : SyntaxSpec) (contents : String) :
    Except ParseError (List Algorithms.MeTTa.Simple.Parser.SExpr) := do
  let rows := (contents.splitOn "\n").zipIdx 1
  let rows := rows.filter fun row => !row.1.trimAscii.isEmpty
  rows.mapM fun (line, number) =>
    (Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed spec line).mapError
      fun error => { error with line := some number }

/-- Qualification quotation for a line-oriented structured answer stream.
This reuses the existing dialect reader; it does not define a new production
grammar or assert correctness of that reader's byte-level implementation. -/
scoped syntax "metta_sexpr_lines_file% " (&"petta" <|> &"he") str : term

private def expandSExprLinesSource (spec : SyntaxSpec) (contents : String)
    (origin : Syntax) : MacroM (TSyntax `term) := do
  match parseSExprLinesWithDetailed spec contents with
  | .ok rows => rows.mapM quoteSExpr >>= mkTermList
  | .error error =>
      Macro.throwErrorAt origin s!"MeTTa S-expression stream parse failed: {error.render}"

scoped syntax "metta_sexpr_lines% " (&"petta" <|> &"he") str : term

scoped macro_rules
  | `(metta_sexpr_lines% petta $source:str) =>
      expandSExprLinesSource MeTTailCore.MeTTaSyntax.petta source.getString source
  | `(metta_sexpr_lines% he $source:str) =>
      expandSExprLinesSource MeTTailCore.MeTTaSyntax.he source.getString source

private def elaborateSExprLinesFile (spec : SyntaxSpec) (path : TSyntax `str)
    (expectedType : Expr) : TermElabM Expr := do
  let context ← readThe Lean.Core.Context
  let currentFile := System.FilePath.mk context.fileName
  let some parent := currentFile.parent
    | throwErrorAt path "cannot determine the quoting file's parent directory"
  let contents ← IO.FS.readFile (parent / path.getString)
  let quoted ← liftMacroM <| expandSExprLinesSource spec contents path
  elabTerm quoted expectedType

elab_rules : term <= expectedType
  | `(metta_sexpr_lines_file% petta $path:str) =>
      elaborateSExprLinesFile MeTTailCore.MeTTaSyntax.petta path expectedType
  | `(metta_sexpr_lines_file% he $path:str) =>
      elaborateSExprLinesFile MeTTailCore.MeTTaSyntax.he path expectedType

/-! ## Executable and elaborated controls -/

open scoped MeTTaSyntaxQuotation

/-- The quoted constructor sequence retains order, duplicate rows, and the
atom/nullary-list distinction. The byte-reader remains the existing executable
qualification boundary, as for the single-expression quotation. -/
theorem source_lines_preserve_order_multiplicity_and_nullary_structure :
    (metta_sexpr_lines% petta "a\n(a)\n\na\n") =
      [Algorithms.MeTTa.Simple.Parser.SExpr.atom "a", .list [.atom "a"], .atom "a"] := rfl

theorem source_lines_he_preserve_nullary_structure :
    (metta_sexpr_lines% he "a\n(a)\n") =
      [Algorithms.MeTTa.Simple.Parser.SExpr.atom "a", .list [.atom "a"]] := rfl

-- Executable reader controls, not proofs of byte-level parser correctness.
#guard (parseSExprLinesWithDetailed MeTTailCore.MeTTaSyntax.petta "a\n(b\nc\n").isOk = false
#guard (parseSExprLinesWithDetailed MeTTailCore.MeTTaSyntax.he "a b\n").isOk = false
#guard match parseSExprLinesWithDetailed MeTTailCore.MeTTaSyntax.petta "\n a\n(b\n" with
  | .error error => error.line == some 3
  | .ok _ => false

theorem source_atom_and_nullary_call_are_distinct :
    (metta_sexpr% petta "bnf-v1:suffix-start") ≠
      (metta_sexpr% petta "(bnf-v1:suffix-start)") := by
  intro equality
  cases equality

/-- Pattern lowering is a lossy view of source S-expressions. -/
theorem pattern_lowering_identifies_atom_and_nullary_call :
    (metta% petta "bnf-v1:suffix-start") =
      (metta% petta "(bnf-v1:suffix-start)") := rfl

theorem no_pattern_decoder_recovers_both_source_forms
    (decode : Pattern → Algorithms.MeTTa.Simple.Parser.SExpr) :
    ¬ (decode (metta% petta "bnf-v1:suffix-start") =
          (metta_sexpr% petta "bnf-v1:suffix-start") ∧
       decode (metta% petta "(bnf-v1:suffix-start)") =
          (metta_sexpr% petta "(bnf-v1:suffix-start)")) := by
  rintro ⟨atom, call⟩
  rw [← pattern_lowering_identifies_atom_and_nullary_call, atom] at call
  cases call

theorem source_comments_separate_tokens :
    (metta_sexpr% petta "; prelude\n(f a; comment\nb)") =
      Algorithms.MeTTa.Simple.Parser.SExpr.list
        [.atom "f", .atom "a", .atom "b"] := rfl

theorem source_quoted_comment_character_is_retained :
    (metta_sexpr% petta "(f \";\")") =
      Algorithms.MeTTa.Simple.Parser.SExpr.list [.atom "f", .atom "\";\""] := rfl

/-- Positive: authored PeTTa syntax expands to the exact specification AST. -/
example :
    metta% petta "(request $channel (payload $value))" =
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply "request"
        [ Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar "channel"
        , Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply "payload"
            [Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar "value"] ] :=
  rfl

/-- Positive: the HE selector reaches the same expression parser with an
explicitly different dialect specification. -/
example :
    metta% he "(answer ticket-7 ok)" =
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply "answer"
        [ Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply "ticket-7" []
        , Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply "ok" [] ] :=
  rfl

/-- Negative executable fixture: malformed MeTTa is rejected by the runtime
parser boundary.  Concrete string parsing remains an executable boundary, so
this is a `Bool` fixture rather than a theorem about kernel reduction.  The
corresponding `metta%` form fails during elaboration. -/
def malformedPeTTaRejected : Bool :=
  !(parsePeTTaPattern "(request $channel").isOk

end Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
