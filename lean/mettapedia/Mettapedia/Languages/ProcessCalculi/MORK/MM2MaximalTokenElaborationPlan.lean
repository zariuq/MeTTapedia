import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics

/-!
# Finite elaboration plan for generated MM2 syntax trees

The parser grammar determines the possible labelled CST nodes.  This module
assigns each such constructor one operation from a small, serializable fold
algebra.  The resulting compiler is therefore driven by finite authored data,
while the independent structural elaborator remains the correctness oracle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan

open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSyntax
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
open Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-- Closed instruction set for the CST fold.  No instruction contains an
arbitrary host callback. -/
inductive Instruction where
  | lexicalScalar
  | programEmpty
  | programDropScalar
  | programDropUnit
  | programCons
  | programFromUnit
  | atomsEmpty
  | atomsDropScalar
  | atomsDropUnit
  | atomsCons
  | atomExpression
  | atomIdentity
  | atomSymbolHeadTail
  | atomSymbolCodepoints
  | atomVariableCodepoints
  | commentLine
  | commentEOF
  | codepointsEmpty
  | codepointsCons
  | codepointsIdentity
  | codepointsQuote
  | codepointsEscape
  deriving Repr, DecidableEq

/-- One constructor-local instruction.  Arity is explicit so a malformed CST
cannot select an operation merely by reusing a valid label. -/
structure PlanRow where
  label : String
  arity : Nat
  instruction : Instruction
  deriving Repr, DecidableEq

private def row (label : String) (arity : Nat)
    (instruction : Instruction) : PlanRow :=
  { label, arity, instruction }

/-- The complete lexical and structural plan, in source inventory order. -/
def rows : List PlanRow := [
  row "mm2:lex-whitespace" 1 .lexicalScalar,
  row "mm2:lex-bare-head" 1 .lexicalScalar,
  row "mm2:lex-bare-char" 1 .lexicalScalar,
  row "mm2:lex-variable-char" 1 .lexicalScalar,
  row "mm2:lex-comment-char" 1 .lexicalScalar,
  row "mm2:lex-quoted-char" 1 .lexicalScalar,
  row "mm2:lex-escaped-char" 1 .lexicalScalar,
  row "mm2:lex-line-feed" 1 .lexicalScalar,

  row "mm2:program-empty" 0 .programEmpty,
  row "mm2:program-whitespace" 2 .programDropScalar,
  row "mm2:program-line-comment" 2 .programDropUnit,
  row "mm2:program-eof-comment" 1 .programFromUnit,
  row "mm2:program-closed" 2 .programCons,
  row "mm2:program-open" 2 .programCons,
  row "mm2:program-after-open-end" 0 .programEmpty,
  row "mm2:program-after-open-whitespace" 2 .programDropScalar,
  row "mm2:program-after-open-expression" 2 .programCons,

  row "mm2:expression" 1 .atomExpression,
  row "mm2:atoms-empty" 0 .atomsEmpty,
  row "mm2:atoms-whitespace" 2 .atomsDropScalar,
  row "mm2:atoms-line-comment" 2 .atomsDropUnit,
  row "mm2:atoms-closed" 2 .atomsCons,
  row "mm2:atoms-open" 2 .atomsCons,
  row "mm2:atoms-after-open-end" 0 .atomsEmpty,
  row "mm2:atoms-after-open-whitespace" 2 .atomsDropScalar,
  row "mm2:atoms-after-open-expression" 2 .atomsCons,

  row "mm2:closed-atom-quoted" 1 .atomSymbolCodepoints,
  row "mm2:closed-atom-expression" 1 .atomIdentity,
  row "mm2:open-atom-bare" 2 .atomSymbolHeadTail,
  row "mm2:open-atom-variable" 1 .atomVariableCodepoints,

  row "mm2:line-comment" 2 .commentLine,
  row "mm2:eof-comment" 1 .commentEOF,
  row "mm2:comment-tail-empty" 0 .codepointsEmpty,
  row "mm2:comment-tail-cons" 2 .codepointsCons,
  row "mm2:bare-tail-empty" 0 .codepointsEmpty,
  row "mm2:bare-tail-cons" 2 .codepointsCons,
  row "mm2:variable" 1 .codepointsIdentity,
  row "mm2:variable-chars-empty" 0 .codepointsEmpty,
  row "mm2:variable-chars-cons" 2 .codepointsCons,
  row "mm2:quoted-symbol" 1 .codepointsQuote,
  row "mm2:quoted-chars-empty" 0 .codepointsEmpty,
  row "mm2:quoted-chars-plain" 2 .codepointsCons,
  row "mm2:quoted-chars-escaped" 2 .codepointsEscape
]

def PlanRow.key (planRow : PlanRow) : String × Nat :=
  (planRow.label, planRow.arity)

/-- The source constructors are read from the actual syntax and lexical
definitions, rather than repeated as a second expected-key list. -/
def sourceKeys : List (String × Nat) :=
  mm2ParserProfile.states.map (fun state => (state.ruleLabel, 1)) ++
    language.terms.map (fun term => (term.label, term.params.length))

theorem rows_cover_source_exactly : rows.map PlanRow.key = sourceKeys := by
  decide +kernel

theorem row_keys_nodup : (rows.map PlanRow.key).Nodup := by
  decide +kernel

theorem row_inventory : rows.length = 43 := by
  decide

/-- Interpret one closed fold instruction.  Every constructor checks the
exact attribute kinds it consumes. -/
def execute : Instruction -> List Attribute -> Option Attribute
  | .lexicalScalar, [.terminal [codepoint]] => some (.scalar codepoint)
  | .programEmpty, [] => some (.program [])
  | .programDropScalar, [.scalar _, .program rest] => some (.program rest)
  | .programDropUnit, [.unit, .program rest] => some (.program rest)
  | .programCons, [.atom head, .program rest] => some (.program (head :: rest))
  | .programFromUnit, [.unit] => some (.program [])
  | .atomsEmpty, [] => some (.atoms [])
  | .atomsDropScalar, [.scalar _, .atoms rest] => some (.atoms rest)
  | .atomsDropUnit, [.unit, .atoms rest] => some (.atoms rest)
  | .atomsCons, [.atom head, .atoms rest] => some (.atoms (head :: rest))
  | .atomExpression, [.atoms atoms] => some (.atom (.expression atoms))
  | .atomIdentity, [.atom atom] => some (.atom atom)
  | .atomSymbolHeadTail, [.scalar head, .codepoints tail] =>
      some (.atom (.symbol (codepointsToString (head :: tail))))
  | .atomSymbolCodepoints, [.codepoints codepoints] =>
      some (.atom (.symbol (codepointsToString codepoints)))
  | .atomVariableCodepoints, [.codepoints codepoints] =>
      some (.atom (.var (codepointsToString codepoints)))
  | .commentLine, [.codepoints _, .scalar 10] => some .unit
  | .commentEOF, [.codepoints _] => some .unit
  | .codepointsEmpty, [] => some (.codepoints [])
  | .codepointsCons, [.scalar head, .codepoints tail] =>
      some (.codepoints (head :: tail))
  | .codepointsIdentity, [.codepoints codepoints] => some (.codepoints codepoints)
  | .codepointsQuote, [.codepoints codepoints] =>
      some (.codepoints (34 :: codepoints ++ [34]))
  | .codepointsEscape, [.scalar head, .codepoints tail] =>
      some (.codepoints (92 :: head :: tail))
  | _, _ => none

def lookup? (label : String) (arity : Nat) : Option PlanRow :=
  rows.find? fun planRow => planRow.label == label && planRow.arity == arity

def compileNode (label : String) (children : List Attribute) :
    Except ElaborationError Attribute :=
  match lookup? label children.length with
  | some planRow =>
      match execute planRow.instruction children with
      | some result => .ok result
      | none => .error .malformedCST
  | none => .error .malformedCST

private theorem lookup_programOpen (arity : Nat) :
    lookup? "mm2:program-open" arity =
      if arity = 2 then
        some (row "mm2:program-open" 2 .programCons)
      else none := by
  by_cases equal : arity = 2
  · subst arity
    simp [lookup?, rows, row, List.find?]
  · have reverse : 2 ≠ arity := Ne.symm equal
    have boolean : (2 == arity) = false := beq_eq_false_iff_ne.mpr reverse
    simp [lookup?, rows, row, List.find?, equal, boolean]

private theorem programOpen_not_lexical (children : List Attribute) :
    elaborateLexicalNode? "mm2:program-open" children = none := by
  rfl

private theorem programOpen_semantics (children : List Attribute) :
    elaborateNode "mm2:program-open" children =
      match execute .programCons children with
      | some result => .ok result
      | none => .error .malformedCST := by
  unfold elaborateNode
  rw [programOpen_not_lexical]
  rcases children with _ | ⟨head, rest⟩
  · rfl
  · rcases rest with _ | ⟨tail, rest⟩
    · cases head <;> rfl
    · rcases rest with _ | ⟨third, rest⟩
      · cases head <;> cases tail <;> rfl
      · cases head <;> cases tail <;> rfl

private theorem compileNode_programOpen
    (children : List Attribute) :
    compileNode "mm2:program-open" children =
      elaborateNode "mm2:program-open" children := by
  rw [compileNode, lookup_programOpen, programOpen_semantics]
  by_cases arity : children.length = 2
  · rw [if_pos arity]
    rfl
  · rw [if_neg arity]
    rcases children with _ | ⟨head, rest⟩
    · rfl
    · rcases rest with _ | ⟨tail, rest⟩
      · cases head <;> rfl
      · rcases rest with _ | ⟨third, rest⟩
        · simp at arity
        · cases head <;> cases tail <;> rfl

private theorem compileNode_programOpen_exact
    (head : Atom) (tail : List Atom) :
    compileNode "mm2:program-open" [.atom head, .program tail] =
      .ok (.program (head :: tail)) := by
  rfl

mutual
  def compileTrees : List CST -> Except ElaborationError (List Attribute)
    | [] => .ok []
    | tree :: trees =>
        match compileTree tree with
        | .error error => .error error
        | .ok head =>
            match compileTrees trees with
            | .error error => .error error
            | .ok tail => .ok (head :: tail)

  def compileTree : CST -> Except ElaborationError Attribute
    | .terminal codepoints _ _ => .ok (.terminal codepoints)
    | .node label _ _ children =>
        match compileTrees children with
        | .error error => .error error
        | .ok attributes => compileNode label attributes
end

def compileRoot (tree : CST) : ElaborationOutcome :=
  finishElaboration (compileTree tree)

/-! ## Exactness on the canonical renderer image -/

private theorem compileLexical_bareHead (character : Char) :
    compileNode "mm2:lex-bare-head" [.terminal [character.toNat]] =
      .ok (.scalar character.toNat) := by
  rfl

private theorem compileLexical_bareChar (character : Char) :
    compileNode "mm2:lex-bare-char" [.terminal [character.toNat]] =
      .ok (.scalar character.toNat) := by
  rfl

private theorem compileLexical_variableChar (character : Char) :
    compileNode "mm2:lex-variable-char" [.terminal [character.toNat]] =
      .ok (.scalar character.toNat) := by
  rfl

private theorem compileLexical_space :
    compileNode "mm2:lex-whitespace" [.terminal [32]] =
      .ok (.scalar 32) := by
  rfl

private theorem compileLexical_lineFeed :
    compileNode "mm2:lex-whitespace" [.terminal [10]] =
      .ok (.scalar 10) := by
  rfl

private theorem compileNode_bareTailEmpty :
    compileNode "mm2:bare-tail-empty" [] = .ok (.codepoints []) := by
  rfl

private theorem compileNode_bareTailCons (head : Nat) (tail : List Nat) :
    compileNode "mm2:bare-tail-cons" [.scalar head, .codepoints tail] =
      .ok (.codepoints (head :: tail)) := by
  rfl

private theorem compileNode_variableCharsEmpty :
    compileNode "mm2:variable-chars-empty" [] =
      .ok (.codepoints []) := by
  rfl

private theorem compileNode_variableCharsCons
    (head : Nat) (tail : List Nat) :
    compileNode "mm2:variable-chars-cons" [.scalar head, .codepoints tail] =
      .ok (.codepoints (head :: tail)) := by
  rfl

private theorem compileNode_variable (values : List Nat) :
    compileNode "mm2:variable" [.codepoints values] =
      .ok (.codepoints values) := by
  rfl

private theorem compileNode_openBare (head : Nat) (tail : List Nat) :
    compileNode "mm2:open-atom-bare" [.scalar head, .codepoints tail] =
      .ok (.atom (.symbol (codepointsToString (head :: tail)))) := by
  rfl

private theorem compileNode_openVariable (values : List Nat) :
    compileNode "mm2:open-atom-variable" [.codepoints values] =
      .ok (.atom (.var (codepointsToString values))) := by
  rfl

private theorem compileNode_expression (values : List Atom) :
    compileNode "mm2:expression" [.atoms values] =
      .ok (.atom (.expression values)) := by
  rfl

private theorem compileNode_closedExpression (value : Atom) :
    compileNode "mm2:closed-atom-expression" [.atom value] =
      .ok (.atom value) := by
  rfl

private theorem compileNode_atomsEmpty :
    compileNode "mm2:atoms-empty" [] = .ok (.atoms []) := by
  rfl

private theorem compileNode_atomsOpen (head : Atom) (tail : List Atom) :
    compileNode "mm2:atoms-open" [.atom head, .atoms tail] =
      .ok (.atoms (head :: tail)) := by
  rfl

private theorem compileNode_atomsClosed (head : Atom) (tail : List Atom) :
    compileNode "mm2:atoms-closed" [.atom head, .atoms tail] =
      .ok (.atoms (head :: tail)) := by
  rfl

private theorem compileNode_atomsAfterOpenEnd :
    compileNode "mm2:atoms-after-open-end" [] = .ok (.atoms []) := by
  rfl

private theorem compileNode_atomsAfterOpenWhitespace
    (head : Nat) (tail : List Atom) :
    compileNode "mm2:atoms-after-open-whitespace"
      [.scalar head, .atoms tail] = .ok (.atoms tail) := by
  rfl

private theorem compileNode_atomsWhitespace
    (head : Nat) (tail : List Atom) :
    compileNode "mm2:atoms-whitespace" [.scalar head, .atoms tail] =
      .ok (.atoms tail) := by
  rfl

private theorem compileNode_programEmpty :
    compileNode "mm2:program-empty" [] = .ok (.program []) := by
  rfl

private theorem compileNode_programClosed
    (head : Atom) (tail : List Atom) :
    compileNode "mm2:program-closed" [.atom head, .program tail] =
      .ok (.program (head :: tail)) := by
  rfl

private theorem compileNode_programAfterOpenWhitespace
    (head : Nat) (tail : List Atom) :
    compileNode "mm2:program-after-open-whitespace"
      [.scalar head, .program tail] = .ok (.program tail) := by
  rfl

private theorem compileNode_programWhitespace
    (head : Nat) (tail : List Atom) :
    compileNode "mm2:program-whitespace" [.scalar head, .program tail] =
      .ok (.program tail) := by
  rfl

private theorem compileBareTail :
    forall characters cursor,
      compileTree (canonicalBareTail characters cursor) =
        .ok (.codepoints (characters.map Char.toNat))
  | [], _ => by rfl
  | character :: rest, cursor => by
      simp [canonicalBareTail, lexical, node, compileTree, compileTrees,
        compileNode_bareTailCons,
        compileLexical_bareChar character,
        compileBareTail rest (cursor + 1)]

private theorem compileVariableChars :
    forall characters cursor,
      compileTree (canonicalVariableChars characters cursor) =
        .ok (.codepoints (characters.map Char.toNat))
  | [], _ => by rfl
  | character :: rest, cursor => by
      simp [canonicalVariableChars, lexical, node, compileTree, compileTrees,
        compileNode_variableCharsCons,
        compileLexical_variableChar character,
        compileVariableChars rest (cursor + 1)]

private theorem compileCanonicalSymbol
    (value : String) (cursor : Nat)
    (safe : atomSafe (.symbol value) = true) :
    compileTree (canonicalOpenAtom (.symbol value) cursor) =
      .ok (.atom (.symbol value)) := by
  simp only [atomSafe] at safe
  cases characters : value.toList with
  | nil => simp [bareSymbolSafe, characters] at safe
  | cons head tail =>
      simp only [bareSymbolSafe, characters, Bool.and_eq_true] at safe
      have decoded :
          codepointsToString ((head :: tail).map Char.toNat) = value := by
        calc
          codepointsToString ((head :: tail).map Char.toNat) =
              codepointsToString (stringScalars value) := by
            congr 1
            simp [stringScalars, characters]
          _ = value := codepointsToString_stringScalars value
      simp [canonicalOpenAtom, characters, lexical, node, compileTree,
        compileTrees, compileNode_openBare,
        compileLexical_bareHead head,
        compileBareTail tail (cursor + 1)]
      simpa using decoded

private theorem compileCanonicalVariable
    (name : String) (cursor : Nat) :
    compileTree (canonicalOpenAtom (.var name) cursor) =
      .ok (.atom (.var name)) := by
  simp [canonicalOpenAtom, node, compileTree, compileTrees,
    compileNode_variable, compileNode_openVariable,
    compileVariableChars name.toList (cursor + 1)]
  simpa [stringScalars] using codepointsToString_stringScalars name

mutual
  private theorem compileCanonicalExpression
      (atoms : List Atom) (cursor : Nat)
      (safe : atomSafe (.expression atoms) = true) :
      compileTree (canonicalClosedAtom (.expression atoms) cursor) =
        .ok (.atom (.expression atoms)) := by
    simp only [atomSafe, Bool.and_eq_true] at safe
    simp [canonicalClosedAtom, node, compileTree, compileTrees,
      compileNode_expression, compileNode_closedExpression,
      compileCanonicalAtoms atoms (cursor + 1) safe.2]

  private theorem compileCanonicalAtoms
      (atoms : List Atom) (cursor : Nat) (safe : atomsSafe atoms = true) :
      compileTree (canonicalAtoms atoms cursor) = .ok (.atoms atoms) := by
    cases atoms with
    | nil => rfl
    | cons atom rest =>
        simp only [atomsSafe, Bool.and_eq_true] at safe
        cases atom with
        | symbol value =>
            cases rest with
            | nil =>
                rw [canonicalAtoms]
                simp [node, compileTree, compileTrees,
                  compileNode_atomsAfterOpenEnd, compileNode_atomsOpen,
                  compileCanonicalSymbol value cursor safe.1]
            | cons next tail =>
                have tailExact := compileCanonicalAtoms (next :: tail)
                  (cursor + (canonicalAtomScalars (.symbol value)).length + 1)
                  safe.2
                rw [canonicalAtoms]
                simp [lexical, node, compileTree, compileTrees,
                  compileNode_atomsAfterOpenWhitespace,
                  compileNode_atomsOpen, compileLexical_space, tailExact,
                  compileCanonicalSymbol value cursor safe.1]
        | var name =>
            cases rest with
            | nil =>
                rw [canonicalAtoms]
                simp [node, compileTree, compileTrees,
                  compileNode_atomsAfterOpenEnd, compileNode_atomsOpen,
                  compileCanonicalVariable name cursor]
            | cons next tail =>
                have tailExact := compileCanonicalAtoms (next :: tail)
                  (cursor + (canonicalAtomScalars (.var name)).length + 1)
                  safe.2
                rw [canonicalAtoms]
                simp [lexical, node, compileTree, compileTrees,
                  compileNode_atomsAfterOpenWhitespace,
                  compileNode_atomsOpen, compileLexical_space, tailExact,
                  compileCanonicalVariable name cursor]
        | grounded value => simp [atomSafe] at safe
        | expression children =>
            cases rest with
            | nil =>
                rw [canonicalAtoms]
                simp [node, compileTree, compileTrees,
                  compileNode_atomsEmpty, compileNode_atomsClosed,
                  compileCanonicalExpression children cursor safe.1]
            | cons next tail =>
                have tailExact := compileCanonicalAtoms (next :: tail)
                  (cursor +
                    (canonicalAtomScalars (.expression children)).length + 1)
                  safe.2
                rw [canonicalAtoms]
                simp [lexical, node, compileTree, compileTrees,
                  compileNode_atomsWhitespace, compileNode_atomsClosed,
                  compileLexical_space, tailExact,
                  compileCanonicalExpression children cursor safe.1]
end

private theorem programAtomsSafe (program : List Atom)
    (safe : programSafe program = true) : program.all atomSafe = true := by
  simp only [programSafe, Bool.and_eq_true] at safe
  exact safe.1

private theorem compileCanonicalProgramTree :
    forall program cursor,
      program.all atomSafe = true ->
        compileTree (canonicalProgramCST program cursor) =
          .ok (.program program)
  | [], _, _ => by rfl
  | atom :: rest, cursor, safe => by
      simp only [List.all_cons, Bool.and_eq_true] at safe
      have tailExact := compileCanonicalProgramTree rest
        (cursor + (canonicalAtomScalars atom).length + 1) safe.2
      cases atom with
      | symbol value =>
          rw [canonicalProgramCST]
          simp [lexical, node, compileTree, compileTrees,
            compileNode_programAfterOpenWhitespace,
            compileNode_programOpen_exact, compileLexical_lineFeed, tailExact,
            compileCanonicalSymbol value cursor safe.1]
      | var name =>
          rw [canonicalProgramCST]
          simp [lexical, node, compileTree, compileTrees,
            compileNode_programAfterOpenWhitespace,
            compileNode_programOpen_exact, compileLexical_lineFeed, tailExact,
            compileCanonicalVariable name cursor]
      | grounded value => simp [atomSafe] at safe
      | expression atoms =>
          rw [canonicalProgramCST]
          simp [lexical, node, compileTree, compileTrees,
            compileNode_programWhitespace, compileNode_programClosed,
            compileLexical_lineFeed, tailExact,
            compileCanonicalExpression atoms cursor safe.1]

/-- The finite plan exactly lowers every program in the canonical renderer
image.  This is the source-to-target bridge used by the MM-to-MM2 exporter. -/
theorem compileCanonicalProgram
    (program : List Atom) (cursor : Nat) (safe : programSafe program = true) :
    compileRoot (canonicalProgramCST program cursor) = .program program := by
  have atomsSafe := programAtomsSafe program safe
  simp [compileRoot, finishElaboration,
    compileCanonicalProgramTree program cursor atomsSafe,
    finishAttribute]

/-- One generated parse whose independent elaboration and finite-plan
elaboration agree on the exact ordered atom program. -/
structure PlannedProgram (input : List Nat) extends ParsedProgram input where
  compiledLowering : compileRoot tree = .program atoms

/-- Every successfully rendered MM2 program has a generated parse accepted by
both the independent elaborator and the finite source-derived plan. -/
theorem successful_render_has_planned_parser_square
    {program : List Atom} {rendered : String}
    (renderedExact : renderProgram? program = some rendered) :
    ∃ parsed : PlannedProgram (stringScalars rendered),
      parsed.atoms = program := by
  rcases (renderProgram?_eq_some_iff program rendered).mp renderedExact with
    ⟨safe, rfl⟩
  have safeParts :
      program.all atomSafe = true ∧ programVariableBudget program = true := by
    simpa only [programSafe, Bool.and_eq_true] using safe
  have recursiveSafe : atomsSafe program = true := by
    rw [atomsSafe_eq_all]
    exact safeParts.1
  obtain ⟨derivation⟩ := canonical_program_has_parser_derivation program safe
  rw [canonicalProgramScalars_eq_rendererScalars
    program recursiveSafe] at derivation
  exact ⟨{
    tree := canonicalProgramCST program 0
    atoms := program
    derivation := derivation
    lowering := elaborateCanonicalProgram program 0 safe
    compiledLowering := compileCanonicalProgram program 0 safe }, rfl⟩

/-! ## Source coverage and behavioral controls -/

theorem lexical_row_is_source_owned :
    ("mm2:lex-bare-head", 1) ∈ sourceKeys := by
  decide

theorem invented_row_is_not_source_owned :
    ("mm2:invented-exec", 2) ∉ sourceKeys := by
  decide

private def emptyTree : CST :=
  .node "mm2:program-empty" 0 0 []

private def malformedTree : CST :=
  .node "mm2:program-open" 0 1 []

theorem compiled_empty_tree : compileRoot emptyTree = .program [] := by
  decide +kernel

theorem compiled_malformed_tree : compileRoot malformedTree = .malformedCST := by
  decide +kernel

#print axioms rows_cover_source_exactly
#print axioms row_keys_nodup
#print axioms lexical_row_is_source_owned
#print axioms invented_row_is_not_source_owned
#print axioms compiled_empty_tree
#print axioms compiled_malformed_tree
#print axioms compileCanonicalProgram
#print axioms successful_render_has_planned_parser_square

end Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan
