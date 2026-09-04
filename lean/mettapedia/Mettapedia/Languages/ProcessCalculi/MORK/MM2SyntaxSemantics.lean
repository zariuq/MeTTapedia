import Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes
import Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxHeightBound
import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-!
# MM2 CST to canonical atom semantics

The generated ParserPack returns occurrence-preserving CSTs.  This module
lowers those trees to the `Atom` carrier consumed by the existing MORK
semantics.  The lowering is independent of parser execution and fails closed
on malformed CSTs or values outside the compact ordinary-MM2 representation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxSemantics

open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
open Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxHeightBound
open Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-- The exact semantic results of MM2 syntax lowering.  Syntax rejection is
represented by absence of a parser derivation and is therefore distinct from
both outcomes below. -/
inductive ElaborationOutcome where
  | program (atoms : List Atom)
  | unsupportedRepresentation
  | malformedCST
  deriving Repr, DecidableEq

private inductive ElaborationError where
  | malformedCST
  deriving Repr, DecidableEq

private inductive Attribute where
  | terminal (codepoints : List Nat)
  | unit
  | scalar (codepoint : Nat)
  | codepoints (values : List Nat)
  | atom (value : Atom)
  | atoms (values : List Atom)
  | program (values : List Atom)
  deriving Repr

def codepointsToString (codepoints : List Nat) : String :=
  String.ofList (codepoints.map Char.ofNat)

private theorem codepointsToString_112 :
    codepointsToString [112] = "p" := by
  apply String.toList_injective
  simp [codepointsToString]

private theorem codepointsToString_120 :
    codepointsToString [120] = "x" := by
  apply String.toList_injective
  simp [codepointsToString]

private def lexicalScalar? (className : String)
    (children : List Attribute) : Option Nat :=
  match children with
  | [.terminal [codepoint]] =>
      if mm2ParserProfile.classAccepts? className codepoint = some true then
        some codepoint
      else
        none
  | _ => none

private def elaborateLexicalNode? (label : String)
    (children : List Attribute) : Option Attribute :=
  let className? :=
    match label with
    | "mm2:lex-whitespace" => some "MM2WhitespaceClass"
    | "mm2:lex-bare-head" => some "MM2BareHeadClass"
    | "mm2:lex-bare-char" => some "MM2BareCharClass"
    | "mm2:lex-variable-char" => some "MM2VariableCharClass"
    | "mm2:lex-comment-char" => some "MM2CommentCharClass"
    | "mm2:lex-quoted-char" => some "MM2QuotedCharClass"
    | "mm2:lex-escaped-char" => some "MM2EscapedCharClass"
    | "mm2:lex-line-feed" => some "MM2LineFeedClass"
    | _ => none
  match className? with
  | none => none
  | some className => (lexicalScalar? className children).map .scalar

private def elaborateNode (label : String)
    (children : List Attribute) : Except ElaborationError Attribute :=
  match elaborateLexicalNode? label children with
  | some lexical => .ok lexical
  | none =>
    match label, children with
    | "mm2:program-empty", [.unit] => .ok (.program [])
    | "mm2:program-cons", [.unit, .atom atom, .program rest] =>
        .ok (.program (atom :: rest))

    | "mm2:atom-symbol", [.codepoints codepoints] =>
        .ok (.atom (.symbol (codepointsToString codepoints)))
    | "mm2:atom-variable", [.codepoints codepoints] =>
        .ok (.atom (.var (codepointsToString codepoints)))
    | "mm2:atom-expression", [.atom expression] => .ok (.atom expression)
    | "mm2:expression", [.unit, .atoms atoms] =>
        .ok (.atom (.expression atoms))
    | "mm2:atoms-empty", [] => .ok (.atoms [])
    | "mm2:atoms-cons", [.atom atom, .unit, .atoms rest] =>
        .ok (.atoms (atom :: rest))

    | "mm2:gap-empty", [] => .ok .unit
    | "mm2:gap-cons", [.unit, .unit] => .ok .unit
    | "mm2:gap-whitespace", [.scalar _] => .ok .unit
    | "mm2:gap-comment", [.unit] => .ok .unit
    | "mm2:final-gap-regular", [.unit] => .ok .unit
    | "mm2:final-gap-comment", [.unit, .unit] => .ok .unit
    | "mm2:line-comment", [.codepoints _, .scalar 10] => .ok .unit
    | "mm2:eof-comment", [.codepoints _] => .ok .unit
    | "mm2:comment-tail-empty", [] => .ok (.codepoints [])
    | "mm2:comment-tail-cons", [.scalar head, .codepoints tail] =>
        .ok (.codepoints (head :: tail))

    | "mm2:symbol-bare", [.scalar head, .codepoints tail] =>
        .ok (.codepoints (head :: tail))
    | "mm2:symbol-quoted", [.codepoints codepoints] =>
        .ok (.codepoints codepoints)
    | "mm2:bare-tail-empty", [] => .ok (.codepoints [])
    | "mm2:bare-tail-cons", [.scalar head, .codepoints tail] =>
        .ok (.codepoints (head :: tail))

    | "mm2:variable", [.codepoints codepoints] =>
        .ok (.codepoints codepoints)
    | "mm2:variable-chars-empty", [] => .ok (.codepoints [])
    | "mm2:variable-chars-cons", [.scalar head, .codepoints tail] =>
        .ok (.codepoints (head :: tail))

    | "mm2:quoted-symbol", [.codepoints codepoints] =>
        .ok (.codepoints (34 :: codepoints ++ [34]))
    | "mm2:quoted-chars-empty", [] => .ok (.codepoints [])
    | "mm2:quoted-chars-plain", [.scalar head, .codepoints tail] =>
        .ok (.codepoints (head :: tail))
    | "mm2:quoted-chars-escaped", [.scalar head, .codepoints tail] =>
        .ok (.codepoints (92 :: head :: tail))
    | _, _ => .error .malformedCST

mutual
  private def elaborateTrees :
      List CST → Except ElaborationError (List Attribute)
    | [] => .ok []
    | tree :: trees =>
        match elaborateTree tree with
        | .error error => .error error
        | .ok head =>
            match elaborateTrees trees with
            | .error error => .error error
            | .ok tail => .ok (head :: tail)

  private def elaborateTree : CST → Except ElaborationError Attribute
    | .terminal codepoints _ _ => .ok (.terminal codepoints)
    | .node label _ _ children =>
        match elaborateTrees children with
        | .error error => .error error
        | .ok attributes => elaborateNode label attributes
end

private def finishAttribute : Attribute → ElaborationOutcome
  | .program atoms =>
      if programSafe atoms then .program atoms else .unsupportedRepresentation
  | _ => .malformedCST

private def finishElaboration :
    Except ElaborationError Attribute → ElaborationOutcome
  | .ok result => finishAttribute result
  | .error _ => .malformedCST

/-- Pure lowering of one complete MM2 CST.  The final compact-domain check is
the same source of truth used by the ordinary renderer. -/
def elaborateRootCST (tree : CST) : ElaborationOutcome :=
  finishElaboration (elaborateTree tree)

def elaborateBranches (trees : List CST) : List ElaborationOutcome :=
  trees.map elaborateRootCST

def ElaborationOutcome.program? : ElaborationOutcome → Option (List Atom)
  | .program atoms => some atoms
  | .unsupportedRepresentation | .malformedCST => none

/-- Semantic ambiguity is decided only after retaining and independently
lowering every physical CST branch. -/
inductive ProgramResolution where
  | noRepresentableProgram
  | unique (program : List Atom)
  | ambiguous (programs : List (List Atom))
  deriving Repr, DecidableEq

def representedPrograms (trees : List CST) : List (List Atom) :=
  (elaborateBranches trees).filterMap ElaborationOutcome.program?

/-- Explicit target-level ambiguity policy.  Duplicate syntax branches with
the same atom program remain visible in `elaborateBranches`, while only
distinct target programs count as semantic ambiguity. -/
def resolvePrograms (trees : List CST) : ProgramResolution :=
  match (representedPrograms trees).eraseDups with
  | [] => .noRepresentableProgram
  | [program] => .unique program
  | programs => .ambiguous programs

/-! ## Canonical scalar and CST construction -/

/-- Unicode-scalar view consumed by the generated ParserPack. -/
def stringScalars (value : String) : List Nat :=
  value.toList.map Char.toNat

mutual
  /-- Canonical scalar spelling of one representable atom.  Grounded values
  have no ordinary MM2 spelling and therefore contribute no canonical
  fragment; all public correspondence theorems require `atomSafe`. -/
  def canonicalAtomScalars : Atom → List Nat
    | .symbol value => stringScalars value
    | .var name => 36 :: stringScalars name
    | .grounded _ => []
    | .expression atoms => 40 :: canonicalAtomsScalars atoms ++ [41]

  /-- Canonical scalar spelling of an expression body, with one space
  between adjacent atom occurrences. -/
  def canonicalAtomsScalars : List Atom → List Nat
    | [] => []
    | atom :: rest =>
        canonicalAtomScalars atom ++
          match rest with
          | [] => []
          | _ :: _ => 32 :: canonicalAtomsScalars rest
end

/-- Canonical whole-file spelling.  Every top-level occurrence is followed
by one line feed, matching `renderProgram?`. -/
def canonicalProgramScalars : List Atom → List Nat
  | [] => []
  | atom :: rest => canonicalAtomScalars atom ++ 10 ::
      canonicalProgramScalars rest

private def canonicalNode (label : String) (start stop : Nat)
    (children : List CST := []) : CST :=
  .node label start stop children

private def canonicalLexical (label : String) (character : Char)
    (start : Nat) : CST :=
  canonicalNode label start (start + 1)
    [.terminal [character.toNat] start (start + 1)]

private def canonicalGapEmpty (cursor : Nat) : CST :=
  canonicalNode "mm2:gap-empty" cursor cursor

private def canonicalFinalGapEmpty (cursor : Nat) : CST :=
  canonicalNode "mm2:final-gap-regular" cursor cursor
    [canonicalGapEmpty cursor]

private def canonicalWhitespaceGap (character : Char)
    (cursor : Nat) : CST :=
  canonicalNode "mm2:gap-cons" cursor (cursor + 1)
    [canonicalNode "mm2:gap-whitespace" cursor (cursor + 1)
      [canonicalLexical "mm2:lex-whitespace" character cursor],
     canonicalGapEmpty (cursor + 1)]

private def canonicalFinalLineFeedGap (cursor : Nat) : CST :=
  canonicalNode "mm2:final-gap-regular" cursor (cursor + 1)
    [canonicalWhitespaceGap '\n' cursor]

private def canonicalBareTailCST : List Char → Nat → CST
  | [], cursor => canonicalNode "mm2:bare-tail-empty" cursor cursor
  | character :: rest, cursor =>
      canonicalNode "mm2:bare-tail-cons" cursor
        (cursor + (character :: rest).length)
        [canonicalLexical "mm2:lex-bare-char" character cursor,
         canonicalBareTailCST rest (cursor + 1)]

private def canonicalVariableCharsCST : List Char → Nat → CST
  | [], cursor => canonicalNode "mm2:variable-chars-empty" cursor cursor
  | character :: rest, cursor =>
      canonicalNode "mm2:variable-chars-cons" cursor
        (cursor + (character :: rest).length)
        [canonicalLexical "mm2:lex-variable-char" character cursor,
         canonicalVariableCharsCST rest (cursor + 1)]

mutual
  /-- Occurrence-preserving CST selected by the canonical renderer for one
  atom.  Its span starts at the supplied cursor. -/
  def canonicalAtomCST : Atom → Nat → CST
    | .symbol value, cursor =>
        match value.toList with
        | [] =>
            canonicalNode "mm2:atom-symbol" cursor cursor
              [canonicalNode "mm2:symbol-bare" cursor cursor]
        | head :: tail =>
            let stop := cursor + (head :: tail).length
            canonicalNode "mm2:atom-symbol" cursor stop
              [canonicalNode "mm2:symbol-bare" cursor stop
                [canonicalLexical "mm2:lex-bare-head" head cursor,
                 canonicalBareTailCST tail (cursor + 1)]]
    | .var name, cursor =>
        let characters := name.toList
        let stop := cursor + 1 + characters.length
        canonicalNode "mm2:atom-variable" cursor stop
          [canonicalNode "mm2:variable" cursor stop
            [canonicalVariableCharsCST characters (cursor + 1)]]
    | .grounded _, cursor =>
        canonicalNode "mm2:unsupported-grounded" cursor cursor
    | .expression atoms, cursor =>
        let stop := cursor + (canonicalAtomsScalars atoms).length + 2
        canonicalNode "mm2:atom-expression" cursor stop
          [canonicalNode "mm2:expression" cursor stop
            [canonicalGapEmpty (cursor + 1),
             canonicalAtomsCST atoms (cursor + 1)]]

  /-- Occurrence-preserving CST for the space-separated body of one
  expression. -/
  def canonicalAtomsCST : List Atom → Nat → CST
    | [], cursor => canonicalNode "mm2:atoms-empty" cursor cursor
    | atom :: rest, cursor =>
        let atomStop := cursor + (canonicalAtomScalars atom).length
        match rest with
        | [] =>
            canonicalNode "mm2:atoms-cons" cursor atomStop
              [canonicalAtomCST atom cursor,
               canonicalGapEmpty atomStop,
               canonicalNode "mm2:atoms-empty" atomStop atomStop]
        | _ :: _ =>
            let stop := cursor +
              (canonicalAtomsScalars (atom :: rest)).length
            canonicalNode "mm2:atoms-cons" cursor stop
              [canonicalAtomCST atom cursor,
               canonicalWhitespaceGap ' ' atomStop,
               canonicalAtomsCST rest (atomStop + 1)]
end

private def canonicalProgramTailCST : List Atom → Nat → CST
  | [], cursor =>
      canonicalNode "mm2:program-empty" cursor (cursor + 1)
        [canonicalFinalLineFeedGap cursor]
  | atom :: rest, cursor =>
      let atomStart := cursor + 1
      let atomStop := atomStart + (canonicalAtomScalars atom).length
      let stop := cursor + 1 +
        (canonicalProgramScalars (atom :: rest)).length
      canonicalNode "mm2:program-cons" cursor stop
        [canonicalWhitespaceGap '\n' cursor,
         canonicalAtomCST atom atomStart,
         canonicalProgramTailCST rest atomStop]

/-- Canonical root CST whose spans are computed from the same scalar
construction consumed by the ParserPack. -/
def canonicalProgramCST : List Atom → Nat → CST
  | [], cursor =>
      canonicalNode "mm2:program-empty" cursor cursor
        [canonicalFinalGapEmpty cursor]
  | atom :: rest, cursor =>
      let atomStop := cursor + (canonicalAtomScalars atom).length
      let stop := cursor +
        (canonicalProgramScalars (atom :: rest)).length
      canonicalNode "mm2:program-cons" cursor stop
        [canonicalGapEmpty cursor,
         canonicalAtomCST atom cursor,
         canonicalProgramTailCST rest atomStop]

theorem codepointsToString_stringScalars (value : String) :
    codepointsToString (stringScalars value) = value := by
  apply String.toList_injective
  simp [codepointsToString, stringScalars, Function.comp_def,
    Char.ofNat_toNat]

private theorem elaborate_canonical_gap_empty (cursor : Nat) :
    elaborateTree (canonicalGapEmpty cursor) = .ok .unit := by
  rfl

private theorem elaborate_canonical_space_gap (cursor : Nat) :
    elaborateTree (canonicalWhitespaceGap ' ' cursor) = .ok .unit := by
  rfl

private theorem elaborate_canonical_line_feed_gap (cursor : Nat) :
    elaborateTree (canonicalWhitespaceGap '\n' cursor) = .ok .unit := by
  rfl

private theorem elaborate_canonical_final_gap_empty (cursor : Nat) :
    elaborateTree (canonicalFinalGapEmpty cursor) = .ok .unit := by
  rfl

private theorem elaborate_canonical_final_line_feed_gap (cursor : Nat) :
    elaborateTree (canonicalFinalLineFeedGap cursor) = .ok .unit := by
  rfl

private theorem elaborate_canonical_bare_head
    (character : Char) (cursor : Nat)
    (safe : isBareSymbolHead character = true) :
    elaborateTree
        (canonicalLexical "mm2:lex-bare-head" character cursor) =
      .ok (.scalar character.toNat) := by
  have admitted :=
    (isBareSymbolHead_eq_true_iff_class character).mp safe
  simp [canonicalLexical, canonicalNode, elaborateTree, elaborateTrees,
    elaborateNode, elaborateLexicalNode?, lexicalScalar?,
    admitted]

private theorem elaborate_canonical_bare_char
    (character : Char) (cursor : Nat)
    (safe : isBareSymbolChar character = true) :
    elaborateTree
        (canonicalLexical "mm2:lex-bare-char" character cursor) =
      .ok (.scalar character.toNat) := by
  have admitted :=
    (isBareSymbolChar_eq_true_iff_class character).mp safe
  simp [canonicalLexical, canonicalNode, elaborateTree, elaborateTrees,
    elaborateNode, elaborateLexicalNode?, lexicalScalar?,
    admitted]

private theorem elaborate_canonical_variable_char
    (character : Char) (cursor : Nat)
    (safe : isVariableChar character = true) :
    elaborateTree
        (canonicalLexical "mm2:lex-variable-char" character cursor) =
      .ok (.scalar character.toNat) := by
  have admitted :=
    (isVariableChar_eq_true_iff_class character).mp safe
  simp [canonicalLexical, canonicalNode, elaborateTree, elaborateTrees,
    elaborateNode, elaborateLexicalNode?, lexicalScalar?,
    admitted]

private theorem elaborate_canonical_bare_tail :
    ∀ (characters : List Char) (cursor : Nat),
      characters.all isBareSymbolChar = true →
        elaborateTree (canonicalBareTailCST characters cursor) =
          .ok (.codepoints (characters.map Char.toNat))
  | [], _, _ => by rfl
  | character :: rest, cursor, safe => by
      simp only [List.all_cons, Bool.and_eq_true] at safe
      simp [canonicalBareTailCST, canonicalNode, elaborateTree,
        elaborateTrees, elaborateNode, elaborateLexicalNode?,
        elaborate_canonical_bare_char character cursor safe.1,
        elaborate_canonical_bare_tail rest (cursor + 1) safe.2]

private theorem elaborate_canonical_variable_chars :
    ∀ (characters : List Char) (cursor : Nat),
      characters.all isVariableChar = true →
        elaborateTree (canonicalVariableCharsCST characters cursor) =
          .ok (.codepoints (characters.map Char.toNat))
  | [], _, _ => by rfl
  | character :: rest, cursor, safe => by
      simp only [List.all_cons, Bool.and_eq_true] at safe
      simp [canonicalVariableCharsCST, canonicalNode, elaborateTree,
        elaborateTrees, elaborateNode, elaborateLexicalNode?,
        elaborate_canonical_variable_char character cursor safe.1,
        elaborate_canonical_variable_chars rest (cursor + 1) safe.2]

mutual
  private theorem elaborate_canonical_atom
      (atom : Atom) (cursor : Nat)
      (safe : atomSafe atom = true) :
      elaborateTree (canonicalAtomCST atom cursor) = .ok (.atom atom) := by
    cases atom with
    | symbol value =>
        simp only [atomSafe] at safe
        cases characters : value.toList with
        | nil =>
            simp [bareSymbolSafe, characters] at safe
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
            simp [canonicalAtomCST, characters, canonicalNode, elaborateTree,
              elaborateTrees, elaborateNode, elaborateLexicalNode?,
              elaborate_canonical_bare_head head cursor safe.1.2,
              elaborate_canonical_bare_tail tail (cursor + 1) safe.2]
            simpa using decoded
    | var name =>
        simp only [atomSafe, variableNameSafe] at safe
        simp [canonicalAtomCST, canonicalNode, elaborateTree, elaborateTrees,
          elaborateNode, elaborateLexicalNode?,
          elaborate_canonical_variable_chars name.toList (cursor + 1) safe]
        simpa [stringScalars] using codepointsToString_stringScalars name
    | grounded value =>
        simp [atomSafe] at safe
    | expression atoms =>
        simp only [atomSafe, Bool.and_eq_true] at safe
        simp [canonicalAtomCST, canonicalNode, elaborateTree, elaborateTrees,
          elaborateNode, elaborateLexicalNode?,
          elaborate_canonical_gap_empty,
          elaborate_canonical_atoms atoms (cursor + 1) safe.2]

  private theorem elaborate_canonical_atoms
      (atoms : List Atom) (cursor : Nat)
      (safe : atomsSafe atoms = true) :
      elaborateTree (canonicalAtomsCST atoms cursor) = .ok (.atoms atoms) := by
    cases atoms with
    | nil => rfl
    | cons atom rest =>
        simp only [atomsSafe, Bool.and_eq_true] at safe
        cases rest with
        | nil =>
            simp [canonicalAtomsCST, canonicalNode, elaborateTree,
              elaborateTrees, elaborateNode, elaborateLexicalNode?,
              elaborate_canonical_atom atom cursor safe.1,
              elaborate_canonical_gap_empty]
        | cons next tail =>
            rw [canonicalAtomsCST]
            simp [canonicalNode, elaborateTree,
              elaborateTrees, elaborateNode, elaborateLexicalNode?,
              elaborate_canonical_atom atom cursor safe.1,
              elaborate_canonical_space_gap,
              elaborate_canonical_atoms (next :: tail)
                (cursor + (canonicalAtomScalars atom).length + 1) safe.2]
end

private theorem atomsSafe_eq_all (atoms : List Atom) :
    atomsSafe atoms = atoms.all atomSafe := by
  induction atoms with
  | nil => rfl
  | cons atom rest induction =>
      simp [atomsSafe, induction]

private theorem elaborate_canonical_program_tail :
    ∀ (atoms : List Atom) (cursor : Nat),
      atomsSafe atoms = true →
        elaborateTree (canonicalProgramTailCST atoms cursor) =
          .ok (.program atoms)
  | [], _, _ => by rfl
  | atom :: rest, cursor, safe => by
      simp only [atomsSafe, Bool.and_eq_true] at safe
      rw [canonicalProgramTailCST]
      simp [canonicalNode, elaborateTree, elaborateTrees, elaborateNode,
        elaborateLexicalNode?, elaborate_canonical_line_feed_gap,
        elaborate_canonical_atom atom (cursor + 1) safe.1,
        elaborate_canonical_program_tail rest
          (cursor + 1 + (canonicalAtomScalars atom).length) safe.2]

private theorem elaborate_canonical_program_tree
    (program : List Atom) (cursor : Nat)
    (safe : atomsSafe program = true) :
    elaborateTree (canonicalProgramCST program cursor) =
      .ok (.program program) := by
  cases program with
  | nil => rfl
  | cons atom rest =>
      simp only [atomsSafe, Bool.and_eq_true] at safe
      rw [canonicalProgramCST]
      simp [canonicalNode, elaborateTree, elaborateTrees, elaborateNode,
        elaborateLexicalNode?, elaborate_canonical_gap_empty,
        elaborate_canonical_atom atom cursor safe.1,
        elaborate_canonical_program_tail rest
          (cursor + (canonicalAtomScalars atom).length) safe.2]

/-- Canonical lowering is exact for every complete program admitted by the
ordinary MM2 representation boundary, not only for closed fixtures. -/
theorem elaborate_canonical_program
    (program : List Atom) (cursor : Nat)
    (safe : programSafe program = true) :
    elaborateRootCST (canonicalProgramCST program cursor) =
      .program program := by
  simp only [programSafe, Bool.and_eq_true] at safe
  have recursiveSafe : atomsSafe program = true := by
    rw [atomsSafe_eq_all]
    exact safe.1
  simp [elaborateRootCST, finishElaboration,
    elaborate_canonical_program_tree program cursor recursiveSafe,
    finishAttribute, programSafe, safe]

mutual
  /-- The canonical parser scalars for one representable atom are exactly
  the Unicode scalars printed by the ordinary MM2 renderer. -/
  theorem canonicalAtomScalars_eq_stringScalars_ordinaryAtomString
      (atom : Atom) (safe : atomSafe atom = true) :
      canonicalAtomScalars atom =
        stringScalars (ordinaryAtomString atom) := by
    cases atom with
    | symbol value =>
        rw [canonicalAtomScalars, ordinaryAtomString.eq_1]
    | var name =>
        rw [canonicalAtomScalars, ordinaryAtomString.eq_2]
        simp [stringScalars,
          String.toList_append]
    | grounded value =>
        simp [atomSafe] at safe
    | expression atoms =>
        simp only [atomSafe, Bool.and_eq_true] at safe
        cases atoms with
        | nil =>
            rw [canonicalAtomScalars, ordinaryAtomString.eq_4,
              ordinaryAtomString.renderAtoms.eq_1]
            simp [stringScalars]
            rfl
        | cons atom rest =>
            rw [canonicalAtomScalars, ordinaryAtomString.eq_4]
            rw [canonicalAtomsScalars_eq_stringScalars_ordinaryAtomsString
              (atom :: rest) safe.2]
            simp [stringScalars, String.toList_append]

  /-- The canonical expression-body scalars agree with the renderer's
  single-space intercalation, preserving order and multiplicity. -/
  theorem canonicalAtomsScalars_eq_stringScalars_ordinaryAtomsString
      (atoms : List Atom) (safe : atomsSafe atoms = true) :
      canonicalAtomsScalars atoms =
        stringScalars (ordinaryAtomString.renderAtoms atoms) := by
    cases atoms with
    | nil =>
        rw [canonicalAtomsScalars,
          ordinaryAtomString.renderAtoms.eq_1]
        simp [stringScalars]
    | cons atom rest =>
        simp only [atomsSafe, Bool.and_eq_true] at safe
        cases rest with
        | nil =>
            rw [canonicalAtomsScalars,
              ordinaryAtomString.renderAtoms.eq_2]
            simpa using
              canonicalAtomScalars_eq_stringScalars_ordinaryAtomString
                atom safe.1
        | cons next tail =>
            rw [canonicalAtomsScalars]
            rw [ordinaryAtomString.renderAtoms.eq_3 atom (next :: tail)
              (by simp)]
            rw [canonicalAtomScalars_eq_stringScalars_ordinaryAtomString
              atom safe.1]
            rw [canonicalAtomsScalars_eq_stringScalars_ordinaryAtomsString
              (next :: tail) safe.2]
            simp [stringScalars, String.toList_append]
end

/-- Canonical parser input for a recursively safe program is exactly the
Unicode-scalar view of the target-owned ordinary MM2 spelling. -/
theorem canonicalProgramScalars_eq_stringScalars_ordinaryProgramString
    (program : List Atom) (safe : atomsSafe program = true) :
    canonicalProgramScalars program =
      stringScalars (ordinaryProgramString program) := by
  induction program with
  | nil =>
      simp [canonicalProgramScalars, ordinaryProgramString, stringScalars]
  | cons atom rest induction =>
      simp only [atomsSafe, Bool.and_eq_true] at safe
      rw [canonicalProgramScalars, ordinaryProgramString]
      rw [canonicalAtomScalars_eq_stringScalars_ordinaryAtomString
        atom safe.1]
      rw [induction safe.2]
      simp [stringScalars, String.toList_append]

/-- Rendering and canonical parser input are one representation, not two
independently maintained spellings. -/
theorem renderProgram?_eq_canonical_scalars
    (program : List Atom) (safe : programSafe program = true) :
    renderProgram? program =
      some (codepointsToString (canonicalProgramScalars program)) := by
  simp only [programSafe, Bool.and_eq_true] at safe
  have recursiveSafe : atomsSafe program = true := by
    rw [atomsSafe_eq_all]
    exact safe.1
  rw [renderProgram?]
  simp [programSafe, safe,
    canonicalProgramScalars_eq_stringScalars_ordinaryProgramString
      program recursiveSafe,
    codepointsToString_stringScalars]

/-! ## Canonical ParserPack derivation -/

private theorem mm2LexicalPositionValid
    (position : Nat) (within : position < 8) :
    position < mm2ParserPackPlan.lexical.productions.length := by
  rw [mm2_parser_pack_inventory.2.1]
  exact within

private theorem mm2StructuralPositionValid
    (position : Nat) (within : position < 29) :
    position < mm2ParserPackPlan.structural.length := by
  rw [mm2_parser_pack_inventory.2.2]
  exact within

private theorem mm2LexicalSignatureAt
    (position : Nat) (within : position < 8)
    (expected : String × String × TerminalMatcher)
    (expectedAt : mm2LexicalSignatures[position]? = some expected) :
    let valid := mm2LexicalPositionValid position within
    let row := mm2ParserPackPlan.lexical.productions.get
      ⟨position, valid⟩
    row.resultSort = expected.1 ∧
      row.label = expected.2.1 ∧ row.matcher = expected.2.2 := by
  have signatures := congrArg (fun rows => rows[position]?)
    mm2_parser_pack_signatures_exact.1
  rw [expectedAt] at signatures
  simp only [List.getElem?_map, Option.map_eq_some_iff] at signatures
  rcases signatures with ⟨row, rowAt, fields⟩
  have valid := mm2LexicalPositionValid position within
  rw [List.getElem?_eq_getElem valid] at rowAt
  have rowExact :
      mm2ParserPackPlan.lexical.productions.get ⟨position, valid⟩ = row :=
    Option.some.inj rowAt
  subst row
  exact ⟨congrArg (fun signature => signature.1) fields,
    congrArg (fun signature => signature.2.1) fields,
    congrArg (fun signature => signature.2.2) fields⟩

private theorem mm2StructuralSignatureAt
    (position : Nat) (within : position < 29)
    (expected : String × String × List PackItem)
    (expectedAt : mm2StructuralSignatures[position]? = some expected) :
    let valid := mm2StructuralPositionValid position within
    let row := mm2ParserPackPlan.structural.get ⟨position, valid⟩
    row.resultSort = expected.1 ∧
      row.label = expected.2.1 ∧ row.items = expected.2.2 := by
  have signatures := congrArg (fun rows => rows[position]?)
    mm2_parser_pack_signatures_exact.2
  rw [expectedAt] at signatures
  simp only [List.getElem?_map, Option.map_eq_some_iff] at signatures
  rcases signatures with ⟨row, rowAt, fields⟩
  have valid := mm2StructuralPositionValid position within
  rw [List.getElem?_eq_getElem valid] at rowAt
  have rowExact :
      mm2ParserPackPlan.structural.get ⟨position, valid⟩ = row :=
    Option.some.inj rowAt
  subst row
  exact ⟨congrArg (fun signature => signature.1) fields,
    congrArg (fun signature => signature.2.1) fields,
    congrArg (fun signature => signature.2.2) fields⟩

private def canonicalBareHeadDerivation
    (before after : List Nat) (character : Char)
    (safe : isBareSymbolHead character = true) :
    ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
      (before ++ character.toNat :: after) "MM2BareHead"
      before.length (before.length + 1)
      (canonicalLexical "mm2:lex-bare-head" character before.length) := by
  have signature := mm2LexicalSignatureAt 1 (by decide)
    ("MM2BareHead", "mm2:lex-bare-head",
      TerminalMatcher.class "MM2BareHeadClass") (by decide)
  refine ParserPackDerivesAt.lexical
    (matcher := .class "MM2BareHeadClass")
    (resultSort := "MM2BareHead") (ruleLabel := "mm2:lex-bare-head")
    (children := [.terminal [character.toNat]
      before.length (before.length + 1)])
    1 (mm2LexicalPositionValid 1 (by decide)) signature.2.2
      signature.1 signature.2.1 ?_
  exact ⟨.classMember (codepoint := character.toNat) (by simp)
    ((isBareSymbolHead_eq_true_iff_class character).mp safe), rfl⟩

private def canonicalBareCharDerivation
    (before after : List Nat) (character : Char)
    (safe : isBareSymbolChar character = true) :
    ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
      (before ++ character.toNat :: after) "MM2BareChar"
      before.length (before.length + 1)
      (canonicalLexical "mm2:lex-bare-char" character before.length) := by
  have signature := mm2LexicalSignatureAt 2 (by decide)
    ("MM2BareChar", "mm2:lex-bare-char",
      TerminalMatcher.class "MM2BareCharClass") (by decide)
  refine ParserPackDerivesAt.lexical
    (matcher := .class "MM2BareCharClass")
    (resultSort := "MM2BareChar") (ruleLabel := "mm2:lex-bare-char")
    (children := [.terminal [character.toNat]
      before.length (before.length + 1)])
    2 (mm2LexicalPositionValid 2 (by decide)) signature.2.2
      signature.1 signature.2.1 ?_
  exact ⟨.classMember (codepoint := character.toNat) (by simp)
    ((isBareSymbolChar_eq_true_iff_class character).mp safe), rfl⟩

private def canonicalVariableCharDerivation
    (before after : List Nat) (character : Char)
    (safe : isVariableChar character = true) :
    ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
      (before ++ character.toNat :: after) "MM2VariableChar"
      before.length (before.length + 1)
      (canonicalLexical "mm2:lex-variable-char" character before.length) := by
  have signature := mm2LexicalSignatureAt 3 (by decide)
    ("MM2VariableChar", "mm2:lex-variable-char",
      TerminalMatcher.class "MM2VariableCharClass") (by decide)
  refine ParserPackDerivesAt.lexical
    (matcher := .class "MM2VariableCharClass")
    (resultSort := "MM2VariableChar")
    (ruleLabel := "mm2:lex-variable-char")
    (children := [.terminal [character.toNat]
      before.length (before.length + 1)])
    3 (mm2LexicalPositionValid 3 (by decide)) signature.2.2
      signature.1 signature.2.1 ?_
  exact ⟨.classMember (codepoint := character.toNat) (by simp)
    ((isVariableChar_eq_true_iff_class character).mp safe), rfl⟩

private def canonicalWhitespaceDerivation
    (before after : List Nat) (character : Char)
    (safe : isWhitespace character = true) :
    ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
      (before ++ character.toNat :: after) "MM2Whitespace"
      before.length (before.length + 1)
      (canonicalLexical "mm2:lex-whitespace" character before.length) := by
  have signature := mm2LexicalSignatureAt 0 (by decide)
    ("MM2Whitespace", "mm2:lex-whitespace",
      TerminalMatcher.class "MM2WhitespaceClass") (by decide)
  refine ParserPackDerivesAt.lexical
    (matcher := .class "MM2WhitespaceClass")
    (resultSort := "MM2Whitespace") (ruleLabel := "mm2:lex-whitespace")
    (children := [.terminal [character.toNat]
      before.length (before.length + 1)])
    0 (mm2LexicalPositionValid 0 (by decide)) signature.2.2
      signature.1 signature.2.1 ?_
  exact ⟨.classMember (codepoint := character.toNat) (by simp)
    ((isWhitespace_eq_true_iff_class character).mp safe), rfl⟩

private def canonicalGapEmptyDerivation
    (input : List Nat) (cursor : Nat) :
    ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan input "MM2Gap"
      cursor cursor (canonicalGapEmpty cursor) := by
  have signature := mm2StructuralSignatureAt 8 (by decide)
    ("MM2Gap", "mm2:gap-empty", []) (by decide)
  refine ParserPackDerivesAt.structural
    (resultSort := "MM2Gap") (ruleLabel := "mm2:gap-empty")
    8 (mm2StructuralPositionValid 8 (by decide)) signature.1
      signature.2.1 ?_
  rw [signature.2.2]
  exact .nil

private def canonicalFinalGapEmptyDerivation
    (input : List Nat) (cursor : Nat) :
    ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan input
      "MM2FinalGap" cursor cursor (canonicalFinalGapEmpty cursor) := by
  have signature := mm2StructuralSignatureAt 12 (by decide)
    ("MM2FinalGap", "mm2:final-gap-regular",
      [.nonterminal "MM2Gap"]) (by decide)
  refine ParserPackDerivesAt.structural
    (resultSort := "MM2FinalGap")
    (ruleLabel := "mm2:final-gap-regular")
    12 (mm2StructuralPositionValid 12 (by decide)) signature.1
      signature.2.1 ?_
  rw [signature.2.2]
  exact .nonterminal (canonicalGapEmptyDerivation input cursor) .nil

private def canonicalWhitespaceUnitDerivation
    (before after : List Nat) (character : Char)
    (safe : isWhitespace character = true) :
    ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
      (before ++ character.toNat :: after) "MM2GapUnit"
      before.length (before.length + 1)
      (canonicalNode "mm2:gap-whitespace" before.length
        (before.length + 1)
        [canonicalLexical "mm2:lex-whitespace" character before.length]) := by
  have signature := mm2StructuralSignatureAt 10 (by decide)
    ("MM2GapUnit", "mm2:gap-whitespace",
      [.nonterminal "MM2Whitespace"]) (by decide)
  refine ParserPackDerivesAt.structural
    (resultSort := "MM2GapUnit")
    (ruleLabel := "mm2:gap-whitespace")
    10 (mm2StructuralPositionValid 10 (by decide)) signature.1
      signature.2.1 ?_
  rw [signature.2.2]
  exact .nonterminal
    (canonicalWhitespaceDerivation before after character safe) .nil

private def canonicalWhitespaceGapDerivation
    (before after : List Nat) (character : Char)
    (safe : isWhitespace character = true) :
    ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
      (before ++ character.toNat :: after) "MM2Gap"
      before.length (before.length + 1)
      (canonicalWhitespaceGap character before.length) := by
  have signature := mm2StructuralSignatureAt 9 (by decide)
    ("MM2Gap", "mm2:gap-cons",
      [.nonterminal "MM2GapUnit", .nonterminal "MM2Gap"]) (by decide)
  refine ParserPackDerivesAt.structural
    (resultSort := "MM2Gap") (ruleLabel := "mm2:gap-cons")
    9 (mm2StructuralPositionValid 9 (by decide)) signature.1
      signature.2.1 ?_
  rw [signature.2.2]
  exact .nonterminal
    (canonicalWhitespaceUnitDerivation before after character safe)
    (.nonterminal
      (canonicalGapEmptyDerivation (before ++ character.toNat :: after)
        (before.length + 1)) .nil)

private def canonicalBareTailDerivation :
    ∀ (before after : List Nat) (characters : List Char),
      characters.all isBareSymbolChar = true →
      ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
        (before ++ characters.map Char.toNat ++ after) "MM2BareTail"
        before.length (before.length + characters.length)
        (canonicalBareTailCST characters before.length)
  | before, after, [], _ => by
      have signature := mm2StructuralSignatureAt 20 (by decide)
        ("MM2BareTail", "mm2:bare-tail-empty", []) (by decide)
      refine ParserPackDerivesAt.structural
        (resultSort := "MM2BareTail")
        (ruleLabel := "mm2:bare-tail-empty")
        20 (mm2StructuralPositionValid 20 (by decide)) signature.1
          signature.2.1 ?_
      rw [signature.2.2]
      exact .nil
  | before, after, character :: rest, safe => by
      simp only [List.all_cons, Bool.and_eq_true] at safe
      have head := canonicalBareCharDerivation before
        (rest.map Char.toNat ++ after) character safe.1
      have tail := canonicalBareTailDerivation
        (before ++ [character.toNat]) after rest safe.2
      have headExact :
          ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
            (before ++ (character :: rest).map Char.toNat ++ after)
            "MM2BareChar" before.length (before.length + 1)
            (canonicalLexical "mm2:lex-bare-char" character
              before.length) := by
        simpa [List.append_assoc] using head
      have tailExact :
          ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
            (before ++ (character :: rest).map Char.toNat ++ after)
            "MM2BareTail" (before.length + 1)
            (before.length + (character :: rest).length)
            (canonicalBareTailCST rest (before.length + 1)) := by
        simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using tail
      have signature := mm2StructuralSignatureAt 21 (by decide)
        ("MM2BareTail", "mm2:bare-tail-cons",
          [.nonterminal "MM2BareChar", .nonterminal "MM2BareTail"])
        (by decide)
      rw [canonicalBareTailCST]
      refine ParserPackDerivesAt.structural
        (resultSort := "MM2BareTail")
        (ruleLabel := "mm2:bare-tail-cons")
        21 (mm2StructuralPositionValid 21 (by decide)) signature.1
          signature.2.1 ?_
      rw [signature.2.2]
      exact .nonterminal headExact (.nonterminal tailExact .nil)

private def canonicalVariableCharsDerivation :
    ∀ (before after : List Nat) (characters : List Char),
      characters.all isVariableChar = true →
      ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
        (before ++ characters.map Char.toNat ++ after) "MM2VariableChars"
        before.length (before.length + characters.length)
        (canonicalVariableCharsCST characters before.length)
  | before, after, [], _ => by
      have signature := mm2StructuralSignatureAt 23 (by decide)
        ("MM2VariableChars", "mm2:variable-chars-empty", []) (by decide)
      refine ParserPackDerivesAt.structural
        (resultSort := "MM2VariableChars")
        (ruleLabel := "mm2:variable-chars-empty")
        23 (mm2StructuralPositionValid 23 (by decide)) signature.1
          signature.2.1 ?_
      rw [signature.2.2]
      exact .nil
  | before, after, character :: rest, safe => by
      simp only [List.all_cons, Bool.and_eq_true] at safe
      have head := canonicalVariableCharDerivation before
        (rest.map Char.toNat ++ after) character safe.1
      have tail := canonicalVariableCharsDerivation
        (before ++ [character.toNat]) after rest safe.2
      have headExact :
          ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
            (before ++ (character :: rest).map Char.toNat ++ after)
            "MM2VariableChar" before.length (before.length + 1)
            (canonicalLexical "mm2:lex-variable-char" character
              before.length) := by
        simpa [List.append_assoc] using head
      have tailExact :
          ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
            (before ++ (character :: rest).map Char.toNat ++ after)
            "MM2VariableChars" (before.length + 1)
            (before.length + (character :: rest).length)
            (canonicalVariableCharsCST rest (before.length + 1)) := by
        simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using tail
      have signature := mm2StructuralSignatureAt 24 (by decide)
        ("MM2VariableChars", "mm2:variable-chars-cons",
          [.nonterminal "MM2VariableChar",
           .nonterminal "MM2VariableChars"]) (by decide)
      rw [canonicalVariableCharsCST]
      refine ParserPackDerivesAt.structural
        (resultSort := "MM2VariableChars")
        (ruleLabel := "mm2:variable-chars-cons")
        24 (mm2StructuralPositionValid 24 (by decide)) signature.1
          signature.2.1 ?_
      rw [signature.2.2]
      exact .nonterminal headExact (.nonterminal tailExact .nil)

private def canonicalCharMatch
    (before after : List Nat) (codepoint : Nat) :
    TerminalMatchesAt mm2ParserProfile (before ++ codepoint :: after)
      (.char codepoint) before.length (before.length + 1) :=
  .char (codepoint := codepoint) (by simp)

mutual
  private def canonicalAtomDerivation
      (before after : List Nat) (atom : Atom)
      (safe : atomSafe atom = true) :
      ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
        (before ++ canonicalAtomScalars atom ++ after) "MM2Atom"
        before.length (before.length + (canonicalAtomScalars atom).length)
        (canonicalAtomCST atom before.length) := by
    cases atom with
    | symbol value =>
        simp only [atomSafe] at safe
        cases characters : value.toList with
        | nil =>
            simp [bareSymbolSafe, characters] at safe
        | cons head tail =>
            simp only [bareSymbolSafe, characters, Bool.and_eq_true] at safe
            have headDerivation := canonicalBareHeadDerivation before
              (tail.map Char.toNat ++ after) head safe.1.2
            have tailDerivation := canonicalBareTailDerivation
              (before ++ [head.toNat]) after tail safe.2
            have headExact :
                ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
                  (before ++ (head :: tail).map Char.toNat ++ after)
                  "MM2BareHead" before.length (before.length + 1)
                  (canonicalLexical "mm2:lex-bare-head" head
                    before.length) := by
              simpa [List.append_assoc] using headDerivation
            have tailExact :
                ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
                  (before ++ (head :: tail).map Char.toNat ++ after)
                  "MM2BareTail" (before.length + 1)
                  (before.length + (head :: tail).length)
                  (canonicalBareTailCST tail (before.length + 1)) := by
              simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using tailDerivation
            have symbolSignature := mm2StructuralSignatureAt 18 (by decide)
              ("MM2Symbol", "mm2:symbol-bare",
                [.nonterminal "MM2BareHead", .nonterminal "MM2BareTail"])
              (by decide)
            have symbolDerivation :
                ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
                  (before ++ (head :: tail).map Char.toNat ++ after)
                  "MM2Symbol" before.length
                  (before.length + (head :: tail).length)
                  (canonicalNode "mm2:symbol-bare" before.length
                    (before.length + (head :: tail).length)
                    [canonicalLexical "mm2:lex-bare-head" head
                      before.length,
                     canonicalBareTailCST tail (before.length + 1)]) := by
              refine ParserPackDerivesAt.structural
                (resultSort := "MM2Symbol")
                (ruleLabel := "mm2:symbol-bare")
                18 (mm2StructuralPositionValid 18 (by decide))
                  symbolSignature.1 symbolSignature.2.1 ?_
              rw [symbolSignature.2.2]
              exact .nonterminal headExact (.nonterminal tailExact .nil)
            have atomSignature := mm2StructuralSignatureAt 2 (by decide)
              ("MM2Atom", "mm2:atom-symbol",
                [.nonterminal "MM2Symbol"]) (by decide)
            have result :
                ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
                  (before ++ (head :: tail).map Char.toNat ++ after)
                  "MM2Atom" before.length
                  (before.length + (head :: tail).length)
                  (canonicalNode "mm2:atom-symbol" before.length
                    (before.length + (head :: tail).length)
                    [canonicalNode "mm2:symbol-bare" before.length
                      (before.length + (head :: tail).length)
                      [canonicalLexical "mm2:lex-bare-head" head
                        before.length,
                       canonicalBareTailCST tail (before.length + 1)]]) := by
              refine ParserPackDerivesAt.structural
                (resultSort := "MM2Atom")
                (ruleLabel := "mm2:atom-symbol")
                2 (mm2StructuralPositionValid 2 (by decide))
                  atomSignature.1 atomSignature.2.1 ?_
              rw [atomSignature.2.2]
              exact .nonterminal symbolDerivation .nil
            simpa [canonicalAtomScalars, stringScalars, characters,
              canonicalAtomCST] using result
    | var name =>
        simp only [atomSafe, variableNameSafe] at safe
        let characters := name.toList
        have charactersDerivation := canonicalVariableCharsDerivation
          (before ++ [36]) after characters safe
        have charactersExact :
            ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
              (before ++ (36 :: characters.map Char.toNat) ++ after)
              "MM2VariableChars" (before.length + 1)
              (before.length + 1 + characters.length)
              (canonicalVariableCharsCST characters
                (before.length + 1)) := by
          simpa [List.append_assoc] using charactersDerivation
        have dollarExact :
            TerminalMatchesAt mm2ParserProfile
              (before ++ (36 :: characters.map Char.toNat) ++ after)
              (.char 36) before.length (before.length + 1) := by
          simpa [List.append_assoc] using canonicalCharMatch before
            (characters.map Char.toNat ++ after) 36
        have variableSignature := mm2StructuralSignatureAt 22 (by decide)
          ("MM2Variable", "mm2:variable",
            [.terminal (.char 36), .nonterminal "MM2VariableChars"])
          (by decide)
        have variableDerivation :
            ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
              (before ++ (36 :: characters.map Char.toNat) ++ after)
              "MM2Variable" before.length
              (before.length + 1 + characters.length)
              (canonicalNode "mm2:variable" before.length
                (before.length + 1 + characters.length)
                [canonicalVariableCharsCST characters
                  (before.length + 1)]) := by
          refine ParserPackDerivesAt.structural
            (resultSort := "MM2Variable")
            (ruleLabel := "mm2:variable")
            22 (mm2StructuralPositionValid 22 (by decide))
              variableSignature.1 variableSignature.2.1 ?_
          rw [variableSignature.2.2]
          exact .terminal dollarExact
            (.nonterminal charactersExact .nil)
        have atomSignature := mm2StructuralSignatureAt 3 (by decide)
          ("MM2Atom", "mm2:atom-variable",
            [.nonterminal "MM2Variable"]) (by decide)
        have result :
            ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
              (before ++ (36 :: characters.map Char.toNat) ++ after)
              "MM2Atom" before.length
              (before.length + 1 + characters.length)
              (canonicalNode "mm2:atom-variable" before.length
                (before.length + 1 + characters.length)
                [canonicalNode "mm2:variable" before.length
                  (before.length + 1 + characters.length)
                  [canonicalVariableCharsCST characters
                    (before.length + 1)]]) := by
          refine ParserPackDerivesAt.structural
            (resultSort := "MM2Atom")
            (ruleLabel := "mm2:atom-variable")
            3 (mm2StructuralPositionValid 3 (by decide)) atomSignature.1
              atomSignature.2.1 ?_
          rw [atomSignature.2.2]
          exact .nonterminal variableDerivation .nil
        simpa [characters, canonicalAtomScalars, stringScalars,
          canonicalAtomCST, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using result
    | grounded value =>
        simp [atomSafe] at safe
    | expression atoms =>
        simp only [atomSafe, Bool.and_eq_true] at safe
        let body := canonicalAtomsScalars atoms
        have leftExact :
            TerminalMatchesAt mm2ParserProfile
              (before ++ (40 :: body ++ 41 :: after)) (.char 40)
              before.length (before.length + 1) := by
          simpa [List.append_assoc] using
            canonicalCharMatch before (body ++ 41 :: after) 40
        have gapExact := canonicalGapEmptyDerivation
          (before ++ (40 :: body ++ 41 :: after)) (before.length + 1)
        have atomsDerivation := canonicalAtomsDerivation
          (before ++ [40]) (41 :: after) atoms safe.2
        have atomsExact :
            ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
              (before ++ (40 :: body ++ 41 :: after)) "MM2Atoms"
              (before.length + 1) (before.length + 1 + body.length)
              (canonicalAtomsCST atoms (before.length + 1)) := by
          simpa [body, List.append_assoc] using atomsDerivation
        have rightExact :
            TerminalMatchesAt mm2ParserProfile
              (before ++ (40 :: body ++ 41 :: after)) (.char 41)
              (before.length + 1 + body.length)
              (before.length + body.length + 2) := by
          have right := canonicalCharMatch
            (before ++ [40] ++ body) after 41
          convert right using 1 <;>
            simp [List.append_assoc] <;> omega
        have expressionSignature := mm2StructuralSignatureAt 5 (by decide)
          ("MM2Expression", "mm2:expression",
            [.terminal (.char 40), .nonterminal "MM2Gap",
             .nonterminal "MM2Atoms", .terminal (.char 41)]) (by decide)
        have expressionDerivation :
            ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
              (before ++ (40 :: body ++ 41 :: after)) "MM2Expression"
              before.length (before.length + body.length + 2)
              (canonicalNode "mm2:expression" before.length
                (before.length + body.length + 2)
                [canonicalGapEmpty (before.length + 1),
                 canonicalAtomsCST atoms (before.length + 1)]) := by
          refine ParserPackDerivesAt.structural
            (resultSort := "MM2Expression")
            (ruleLabel := "mm2:expression")
            5 (mm2StructuralPositionValid 5 (by decide))
              expressionSignature.1 expressionSignature.2.1 ?_
          rw [expressionSignature.2.2]
          exact .terminal leftExact
            (.nonterminal gapExact
              (.nonterminal atomsExact (.terminal rightExact .nil)))
        have atomSignature := mm2StructuralSignatureAt 4 (by decide)
          ("MM2Atom", "mm2:atom-expression",
            [.nonterminal "MM2Expression"]) (by decide)
        have result :
            ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
              (before ++ (40 :: body ++ 41 :: after)) "MM2Atom"
              before.length (before.length + body.length + 2)
              (canonicalNode "mm2:atom-expression" before.length
                (before.length + body.length + 2)
                [canonicalNode "mm2:expression" before.length
                  (before.length + body.length + 2)
                  [canonicalGapEmpty (before.length + 1),
                   canonicalAtomsCST atoms (before.length + 1)]]) := by
          refine ParserPackDerivesAt.structural
            (resultSort := "MM2Atom")
            (ruleLabel := "mm2:atom-expression")
            4 (mm2StructuralPositionValid 4 (by decide)) atomSignature.1
              atomSignature.2.1 ?_
          rw [atomSignature.2.2]
          exact .nonterminal expressionDerivation .nil
        convert result using 1 <;>
          simp [body, canonicalAtomScalars, canonicalAtomCST,
            List.append_assoc]
        all_goals omega

  private def canonicalAtomsDerivation
      (before after : List Nat) (atoms : List Atom)
      (safe : atomsSafe atoms = true) :
      ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
        (before ++ canonicalAtomsScalars atoms ++ after) "MM2Atoms"
        before.length (before.length + (canonicalAtomsScalars atoms).length)
        (canonicalAtomsCST atoms before.length) := by
    cases atoms with
    | nil =>
        have signature := mm2StructuralSignatureAt 6 (by decide)
          ("MM2Atoms", "mm2:atoms-empty", []) (by decide)
        refine ParserPackDerivesAt.structural
          (resultSort := "MM2Atoms") (ruleLabel := "mm2:atoms-empty")
          6 (mm2StructuralPositionValid 6 (by decide)) signature.1
            signature.2.1 ?_
        rw [signature.2.2]
        exact .nil
    | cons atom rest =>
        simp only [atomsSafe, Bool.and_eq_true] at safe
        cases rest with
        | nil =>
            let atomScalars := canonicalAtomScalars atom
            have atomDerivation := canonicalAtomDerivation before after
              atom safe.1
            have gapDerivation := canonicalGapEmptyDerivation
              (before ++ atomScalars ++ after)
              (before.length + atomScalars.length)
            have emptyDerivation := canonicalAtomsDerivation
              (before ++ atomScalars) after [] (by rfl)
            have emptyExact :
                ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
                  (before ++ atomScalars ++ after) "MM2Atoms"
                  (before.length + atomScalars.length)
                  (before.length + atomScalars.length)
                  (canonicalNode "mm2:atoms-empty"
                    (before.length + atomScalars.length)
                    (before.length + atomScalars.length)) := by
              simpa [atomScalars, canonicalAtomsScalars,
                canonicalAtomsCST, canonicalNode, List.append_assoc] using
                emptyDerivation
            have signature := mm2StructuralSignatureAt 7 (by decide)
              ("MM2Atoms", "mm2:atoms-cons",
                [.nonterminal "MM2Atom", .nonterminal "MM2Gap",
                 .nonterminal "MM2Atoms"]) (by decide)
            rw [canonicalAtomsScalars, canonicalAtomsCST]
            simp only [List.append_nil]
            refine ParserPackDerivesAt.structural
              (resultSort := "MM2Atoms") (ruleLabel := "mm2:atoms-cons")
              7 (mm2StructuralPositionValid 7 (by decide)) signature.1
                signature.2.1 ?_
            rw [signature.2.2]
            exact .nonterminal atomDerivation
              (.nonterminal gapDerivation (.nonterminal emptyExact .nil))
        | cons next tail =>
            let atomScalars := canonicalAtomScalars atom
            let restScalars := canonicalAtomsScalars (next :: tail)
            have atomDerivation := canonicalAtomDerivation before
              (32 :: restScalars ++ after) atom safe.1
            have spaceDerivation := canonicalWhitespaceGapDerivation
              (before ++ atomScalars) (restScalars ++ after) ' '
              (by decide)
            have restDerivation := canonicalAtomsDerivation
              (before ++ atomScalars ++ [32]) after (next :: tail) safe.2
            have atomExact :
                ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
                  (before ++ atomScalars ++ 32 :: restScalars ++ after)
                  "MM2Atom" before.length
                  (before.length + atomScalars.length)
                  (canonicalAtomCST atom before.length) := by
              simpa [atomScalars, restScalars, List.append_assoc] using
                atomDerivation
            have spaceExact :
                ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
                  (before ++ atomScalars ++ 32 :: restScalars ++ after)
                  "MM2Gap" (before.length + atomScalars.length)
                  (before.length + atomScalars.length + 1)
                  (canonicalWhitespaceGap ' '
                    (before.length + atomScalars.length)) := by
              simpa [atomScalars, restScalars, List.append_assoc] using
                spaceDerivation
            have restExact :
                ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
                  (before ++ atomScalars ++ 32 :: restScalars ++ after)
                  "MM2Atoms" (before.length + atomScalars.length + 1)
                  (before.length + atomScalars.length + 1 +
                    restScalars.length)
                  (canonicalAtomsCST (next :: tail)
                    (before.length + atomScalars.length + 1)) := by
              simpa [atomScalars, restScalars, List.append_assoc,
                Nat.add_assoc] using restDerivation
            have signature := mm2StructuralSignatureAt 7 (by decide)
              ("MM2Atoms", "mm2:atoms-cons",
                [.nonterminal "MM2Atom", .nonterminal "MM2Gap",
                 .nonterminal "MM2Atoms"]) (by decide)
            dsimp [atomScalars, restScalars] at atomExact spaceExact restExact
            have atomForBody :
                ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
                  (before ++ (canonicalAtomScalars atom ++
                    32 :: canonicalAtomsScalars (next :: tail)) ++ after)
                  "MM2Atom" before.length
                  (before.length + (canonicalAtomScalars atom).length)
                  (canonicalAtomCST atom before.length) := by
              simpa [List.append_assoc] using atomExact
            have spaceForBody :
                ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
                  (before ++ (canonicalAtomScalars atom ++
                    32 :: canonicalAtomsScalars (next :: tail)) ++ after)
                  "MM2Gap" (before.length + (canonicalAtomScalars atom).length)
                  (before.length + (canonicalAtomScalars atom).length + 1)
                  (canonicalWhitespaceGap ' '
                    (before.length + (canonicalAtomScalars atom).length)) := by
              simpa [List.append_assoc] using spaceExact
            have restForBody :
                ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
                  (before ++ (canonicalAtomScalars atom ++
                    32 :: canonicalAtomsScalars (next :: tail)) ++ after)
                  "MM2Atoms"
                  (before.length + (canonicalAtomScalars atom).length + 1)
                  (before.length + (canonicalAtomScalars atom ++
                    32 :: canonicalAtomsScalars (next :: tail)).length)
                  (canonicalAtomsCST (next :: tail)
                    (before.length + (canonicalAtomScalars atom).length + 1)) := by
              convert restExact using 1 <;>
                simp [List.append_assoc]
              all_goals omega
            rw [canonicalAtomsScalars, canonicalAtomsCST]
            refine ParserPackDerivesAt.structural
              (resultSort := "MM2Atoms") (ruleLabel := "mm2:atoms-cons")
              7 (mm2StructuralPositionValid 7 (by decide)) signature.1
                signature.2.1 ?_
            rw [signature.2.2]
            exact .nonterminal atomForBody
              (.nonterminal spaceForBody (.nonterminal restForBody .nil))
end

private def canonicalFinalLineFeedGapDerivation (before : List Nat) :
    ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
      (before ++ [10]) "MM2FinalGap" before.length (before.length + 1)
      (canonicalFinalLineFeedGap before.length) := by
  have gap := canonicalWhitespaceGapDerivation before [] '\n' (by decide)
  have signature := mm2StructuralSignatureAt 12 (by decide)
    ("MM2FinalGap", "mm2:final-gap-regular",
      [.nonterminal "MM2Gap"]) (by decide)
  refine ParserPackDerivesAt.structural
    (resultSort := "MM2FinalGap")
    (ruleLabel := "mm2:final-gap-regular")
    12 (mm2StructuralPositionValid 12 (by decide)) signature.1
      signature.2.1 ?_
  rw [signature.2.2]
  exact .nonterminal gap .nil

/-- Exact recursive ParserPack execution for the line feed and remaining
top-level occurrences after one canonical MM2 atom. -/
private def canonicalProgramTailDerivation :
    ∀ (before : List Nat) (program : List Atom),
      program.all atomSafe = true →
      ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
        (before ++ 10 :: canonicalProgramScalars program) "MM2Program"
        before.length
        (before.length + 1 + (canonicalProgramScalars program).length)
        (canonicalProgramTailCST program before.length)
  | before, [], _ => by
      have finalGap := canonicalFinalLineFeedGapDerivation before
      have signature := mm2StructuralSignatureAt 0 (by decide)
        ("MM2Program", "mm2:program-empty",
          [.nonterminal "MM2FinalGap", .terminal .eof]) (by decide)
      rw [canonicalProgramTailCST, canonicalProgramScalars]
      refine ParserPackDerivesAt.structural
        (resultSort := "MM2Program")
        (ruleLabel := "mm2:program-empty")
        0 (mm2StructuralPositionValid 0 (by decide)) signature.1
          signature.2.1 ?_
      rw [signature.2.2]
      exact .nonterminal finalGap (.terminal (.eof (by simp)) .nil)
  | before, atom :: rest, safe => by
      simp only [List.all_cons, Bool.and_eq_true] at safe
      let atomScalars := canonicalAtomScalars atom
      let restScalars := canonicalProgramScalars rest
      have gapDerivation := canonicalWhitespaceGapDerivation before
        (atomScalars ++ 10 :: restScalars) '\n' (by decide)
      have atomDerivation := canonicalAtomDerivation (before ++ [10])
        (10 :: restScalars) atom safe.1
      have restDerivation := canonicalProgramTailDerivation
        (before ++ [10] ++ atomScalars) rest safe.2
      have atomExact :
          ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
            (before ++ 10 :: (atomScalars ++ 10 :: restScalars)) "MM2Atom"
            (before.length + 1) (before.length + 1 + atomScalars.length)
            (canonicalAtomCST atom (before.length + 1)) := by
        simpa [atomScalars, restScalars, List.append_assoc] using atomDerivation
      have restExact :
          ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
            (before ++ 10 :: (atomScalars ++ 10 :: restScalars)) "MM2Program"
            (before.length + 1 + atomScalars.length)
            (before.length + 1 + (atomScalars ++ 10 :: restScalars).length)
            (canonicalProgramTailCST rest
              (before.length + 1 + atomScalars.length)) := by
        simpa [atomScalars, restScalars, List.append_assoc, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using restDerivation
      have signature := mm2StructuralSignatureAt 1 (by decide)
        ("MM2Program", "mm2:program-cons",
          [.nonterminal "MM2Gap", .nonterminal "MM2Atom",
           .nonterminal "MM2Program", .terminal .eof]) (by decide)
      rw [canonicalProgramTailCST, canonicalProgramScalars]
      dsimp [atomScalars, restScalars] at gapDerivation atomExact restExact
      refine ParserPackDerivesAt.structural
        (resultSort := "MM2Program")
        (ruleLabel := "mm2:program-cons")
        1 (mm2StructuralPositionValid 1 (by decide)) signature.1
          signature.2.1 ?_
      rw [signature.2.2]
      exact .nonterminal gapDerivation
        (.nonterminal atomExact
          (.nonterminal restExact
            (.terminal (.eof (by
              simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])) .nil)))

/-- Every canonically rendered syntax-safe MM2 program has an exact
whole-input derivation in the ParserPack generated from `mm2Syntax`. -/
theorem canonical_program_has_parser_derivation
    (program : List Atom) (safe : programSafe program = true) :
    Nonempty (ParserPackRootDerives mm2ParserProfile mm2ParserPackPlan
      (canonicalProgramScalars program) (canonicalProgramCST program 0)) := by
  simp only [programSafe, Bool.and_eq_true] at safe
  cases program with
  | nil =>
      have finalGap := canonicalFinalGapEmptyDerivation [] 0
      have signature := mm2StructuralSignatureAt 0 (by decide)
        ("MM2Program", "mm2:program-empty",
          [.nonterminal "MM2FinalGap", .terminal .eof]) (by decide)
      refine ⟨?_⟩
      rw [canonicalProgramScalars, canonicalProgramCST]
      refine ParserPackDerivesAt.structural
        (resultSort := "MM2Program")
        (ruleLabel := "mm2:program-empty")
        0 (mm2StructuralPositionValid 0 (by decide)) signature.1
          signature.2.1 ?_
      rw [signature.2.2]
      exact .nonterminal finalGap (.terminal (.eof rfl) .nil)
  | cons atom rest =>
      simp only [List.all_cons, Bool.and_eq_true] at safe
      let atomScalars := canonicalAtomScalars atom
      let restScalars := canonicalProgramScalars rest
      have gapDerivation := canonicalGapEmptyDerivation
        (atomScalars ++ 10 :: restScalars) 0
      have atomDerivation := canonicalAtomDerivation []
        (10 :: restScalars) atom safe.1.1
      have tailDerivation := canonicalProgramTailDerivation atomScalars
        rest safe.1.2
      have atomExact :
          ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
            (atomScalars ++ 10 :: restScalars) "MM2Atom" 0
            atomScalars.length (canonicalAtomCST atom 0) := by
        simpa [atomScalars, restScalars] using atomDerivation
      have tailExact :
          ParserPackDerivesAt mm2ParserProfile mm2ParserPackPlan
            (atomScalars ++ 10 :: restScalars) "MM2Program"
            atomScalars.length (atomScalars ++ 10 :: restScalars).length
            (canonicalProgramTailCST rest atomScalars.length) := by
        simpa [atomScalars, restScalars, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using tailDerivation
      have signature := mm2StructuralSignatureAt 1 (by decide)
        ("MM2Program", "mm2:program-cons",
          [.nonterminal "MM2Gap", .nonterminal "MM2Atom",
           .nonterminal "MM2Program", .terminal .eof]) (by decide)
      refine ⟨?_⟩
      simp only [canonicalProgramCST, canonicalProgramScalars, Nat.zero_add]
      dsimp [atomScalars, restScalars] at gapDerivation atomExact tailExact
      refine ParserPackDerivesAt.structural
        (resultSort := "MM2Program")
        (ruleLabel := "mm2:program-cons")
        1 (mm2StructuralPositionValid 1 (by decide)) signature.1
          signature.2.1 ?_
      rw [signature.2.2]
      exact .nonterminal gapDerivation
        (.nonterminal atomExact
          (.nonterminal tailExact (.terminal (.eof (by simp)) .nil)))

/-- The complete reference parser recovers the canonical CST within the
source-sensitive height bound certified for the generated MM2 ParserPack. -/
theorem canonical_program_is_enumerated
    (program : List Atom) (safe : programSafe program = true) :
    ∃ row ∈ enumerateRootWithin
        (1000 * (canonicalProgramScalars program).length + 9)
        mm2ParserProfile mm2ParserPackPlan (canonicalProgramScalars program),
      row.tree = canonicalProgramCST program 0 := by
  obtain ⟨derivation⟩ := canonical_program_has_parser_derivation program safe
  exact mm2_root_enumeration_complete derivation

theorem elaborateBranches_append (left right : List CST) :
    elaborateBranches (left ++ right) =
      elaborateBranches left ++ elaborateBranches right := by
  simp [elaborateBranches]

theorem elaborateBranches_branch_local
    (before after : List CST) (tree : CST) :
    ((elaborateBranches (before ++ tree :: after)).drop
        before.length).head? = some (elaborateRootCST tree) := by
  simp [elaborateBranches]

/-! ## Reader-token boundary admission -/

/-- Whether an atom CST ends with a delimiter of its own.  Expressions end
with `)`, and quoted symbols end with an unescaped quotation mark. -/
private def atomTreeRightDelimited : CST → Bool
  | .node label _ _ children =>
      if label == "mm2:atom-expression" then true
      else if label == "mm2:atom-symbol" then
        match children with
        | [.node childLabel _ _ _] => childLabel == "mm2:symbol-quoted"
        | _ => false
      else false
  | .terminal _ _ _ => false

/-- An immediately following expression begins with `(`, which terminates an
ordinary bare symbol or variable token without intervening whitespace. -/
private def atomTreeStartsWithReaderDelimiter : CST → Bool
  | .node label _ _ _ => label == "mm2:atom-expression"
  | .terminal _ _ _ => false

private def regularGapIsEmpty : CST → Bool
  | .node label _ _ _ => label == "mm2:gap-empty"
  | .terminal _ _ _ => false

/-- A regular gap begins with a reader delimiter precisely when its first
unit is whitespace.  A semicolon begins a comment only when the reader is
already between tokens; it cannot terminate a preceding bare token. -/
private def regularGapStartsWithWhitespace : CST → Bool
  | .node label _ _ children =>
      if label == "mm2:gap-cons" then
        match children with
        | .node unitLabel _ _ _ :: _ => unitLabel == "mm2:gap-whitespace"
        | _ => false
      else false
  | .terminal _ _ _ => false

private def finalGapIsEmpty : CST → Bool
  | .node label _ _ children =>
      if label == "mm2:final-gap-regular" then
        match children with
        | [gap] => regularGapIsEmpty gap
        | _ => false
      else false
  | .terminal _ _ _ => false

private def finalGapStartsWithWhitespace : CST → Bool
  | .node label _ _ children =>
      if label == "mm2:final-gap-regular" ||
          label == "mm2:final-gap-comment" then
        match children with
        | gap :: _ => regularGapStartsWithWhitespace gap
        | _ => false
      else false
  | .terminal _ _ _ => false

private def endBoundaryAdmitted (atom finalGap : CST) : Bool :=
  atomTreeRightDelimited atom || finalGapIsEmpty finalGap ||
    finalGapStartsWithWhitespace finalGap

private def followingBoundaryAdmitted
    (atom gap nextAtom : CST) : Bool :=
  atomTreeRightDelimited atom || regularGapStartsWithWhitespace gap ||
    atomTreeStartsWithReaderDelimiter nextAtom

/-- Boundary check for one top-level atom and the recursive program tail. -/
private def programBoundaryAdmitted (atom rest : CST) : Bool :=
  match rest with
  | .node label _ _ children =>
      if label == "mm2:program-empty" then
        match children with
        | [finalGap] => endBoundaryAdmitted atom finalGap
        | _ => false
      else if label == "mm2:program-cons" then
        match children with
        | gap :: nextAtom :: _ => followingBoundaryAdmitted atom gap nextAtom
        | _ => false
      else false
  | .terminal _ _ _ => false

/-- Boundary check for one expression-body atom and the recursive atom tail. -/
private def atomsBoundaryAdmitted (atom gap rest : CST) : Bool :=
  match rest with
  | .node label _ _ children =>
      if label == "mm2:atoms-empty" then
        atomTreeRightDelimited atom || regularGapIsEmpty gap ||
          regularGapStartsWithWhitespace gap
      else if label == "mm2:atoms-cons" then
        match children with
        | nextAtom :: _ => followingBoundaryAdmitted atom gap nextAtom
        | _ => false
      else false
  | .terminal _ _ _ => false

mutual
  /-- Source-derived admission judgment excluding scannerless derivations that
  stop a bare symbol or variable before the real MM2 reader would. -/
  def readerTokenBoundaries : CST → Bool
    | .terminal _ _ _ => true
    | .node label _ _ children =>
        let boundary :=
          if label == "mm2:program-cons" then
            match children with
            | _ :: atom :: rest :: [] => programBoundaryAdmitted atom rest
            | _ => false
          else if label == "mm2:atoms-cons" then
            match children with
            | atom :: gap :: rest :: [] =>
                atomsBoundaryAdmitted atom gap rest
            | _ => false
          else true
        boundary && readerTokenBoundariesList children

  def readerTokenBoundariesList : List CST → Bool
    | [] => true
    | tree :: trees =>
        readerTokenBoundaries tree && readerTokenBoundariesList trees
end

/-- Retain exactly those parser branches whose token boundaries agree with
the ordinary MM2 reader.  This is a syntax-derived GSLT-to-GSLT admission
pass over a complete parse forest, not a choice of one convenient branch. -/
def boundaryAdmittedTrees (trees : List CST) : List CST :=
  trees.filter readerTokenBoundaries

/-- Resolve target atoms only after applying the ordinary-reader token
boundary judgment to every parser branch. -/
def resolveBoundaryAdmittedPrograms (trees : List CST) : ProgramResolution :=
  resolvePrograms (boundaryAdmittedTrees trees)

private theorem readerTokenBoundaries_neutralNode
    (label : String) (start stop : Nat) (children : List CST)
    (notProgram : label ≠ "mm2:program-cons")
    (notAtoms : label ≠ "mm2:atoms-cons")
    (childrenAdmitted : readerTokenBoundariesList children = true) :
    readerTokenBoundaries (.node label start stop children) = true := by
  rw [readerTokenBoundaries.eq_def]
  simp [notProgram, notAtoms, childrenAdmitted]

private theorem readerTokenBoundaries_atomsCons
    (start stop : Nat) (atom gap rest : CST) :
    readerTokenBoundaries
        (.node "mm2:atoms-cons" start stop [atom, gap, rest]) =
      (atomsBoundaryAdmitted atom gap rest &&
        readerTokenBoundaries atom && readerTokenBoundaries gap &&
        readerTokenBoundaries rest) := by
  rw [readerTokenBoundaries.eq_def]
  simp [readerTokenBoundariesList, Bool.and_assoc]

private theorem readerTokenBoundaries_programCons
    (start stop : Nat) (gap atom rest : CST) :
    readerTokenBoundaries
        (.node "mm2:program-cons" start stop [gap, atom, rest]) =
      (programBoundaryAdmitted atom rest &&
        readerTokenBoundaries gap && readerTokenBoundaries atom &&
        readerTokenBoundaries rest) := by
  rw [readerTokenBoundaries.eq_def]
  simp [readerTokenBoundariesList, Bool.and_assoc]

@[simp] private theorem canonicalGapEmpty_readerTokenBoundaries
    (cursor : Nat) :
    readerTokenBoundaries (canonicalGapEmpty cursor) = true := by
  rfl

@[simp] private theorem canonicalWhitespaceGap_readerTokenBoundaries
    (character : Char) (cursor : Nat) :
    readerTokenBoundaries (canonicalWhitespaceGap character cursor) = true := by
  simp [canonicalWhitespaceGap, canonicalGapEmpty, canonicalLexical,
    canonicalNode, readerTokenBoundaries, readerTokenBoundariesList]

@[simp] private theorem atomsBoundaryAdmitted_canonicalEmpty
    (atom : CST) (atomStop : Nat) :
    atomsBoundaryAdmitted atom (canonicalGapEmpty atomStop)
        (canonicalNode "mm2:atoms-empty" atomStop atomStop) = true := by
  simp [atomsBoundaryAdmitted, canonicalGapEmpty, canonicalNode,
    regularGapIsEmpty]

@[simp] private theorem atomsBoundaryAdmitted_canonicalCons
    (atom : CST) (gapCursor nextCursor : Nat) (next : Atom)
    (rest : List Atom) :
    atomsBoundaryAdmitted atom (canonicalWhitespaceGap ' ' gapCursor)
        (canonicalAtomsCST (next :: rest) nextCursor) = true := by
  cases rest <;>
    simp [atomsBoundaryAdmitted, canonicalWhitespaceGap, canonicalNode,
      canonicalAtomsCST, followingBoundaryAdmitted,
      regularGapStartsWithWhitespace]

@[simp] private theorem programBoundaryAdmitted_canonicalProgramTail
    (atom : CST) (program : List Atom) (cursor : Nat) :
    programBoundaryAdmitted atom (canonicalProgramTailCST program cursor) =
      true := by
  cases program with
  | nil =>
      simp [programBoundaryAdmitted, canonicalProgramTailCST,
        canonicalFinalLineFeedGap, canonicalWhitespaceGap, canonicalGapEmpty,
        canonicalNode, endBoundaryAdmitted, finalGapStartsWithWhitespace,
        regularGapStartsWithWhitespace]
  | cons next rest =>
      simp [programBoundaryAdmitted, canonicalProgramTailCST,
        canonicalWhitespaceGap, canonicalNode, followingBoundaryAdmitted,
        regularGapStartsWithWhitespace]

private theorem canonicalBareTail_readerTokenBoundaries
    (characters : List Char) (cursor : Nat) :
    readerTokenBoundaries (canonicalBareTailCST characters cursor) = true := by
  induction characters generalizing cursor with
  | nil => rfl
  | cons character rest induction =>
      simp [canonicalBareTailCST, canonicalLexical, canonicalNode,
        readerTokenBoundaries, readerTokenBoundariesList, induction]

private theorem canonicalVariableChars_readerTokenBoundaries
    (characters : List Char) (cursor : Nat) :
    readerTokenBoundaries
        (canonicalVariableCharsCST characters cursor) = true := by
  induction characters generalizing cursor with
  | nil => rfl
  | cons character rest induction =>
      simp [canonicalVariableCharsCST, canonicalLexical, canonicalNode,
        readerTokenBoundaries, readerTokenBoundariesList, induction]

mutual
  private theorem canonicalAtom_readerTokenBoundaries
      (atom : Atom) (cursor : Nat) (safe : atomSafe atom = true) :
      readerTokenBoundaries (canonicalAtomCST atom cursor) = true := by
    cases atom with
    | symbol value =>
        cases characters : value.toList with
        | nil => simp [atomSafe, bareSymbolSafe, characters] at safe
        | cons head tail =>
            simp [canonicalAtomCST, characters, canonicalLexical,
              canonicalNode, readerTokenBoundaries,
              readerTokenBoundariesList,
              canonicalBareTail_readerTokenBoundaries]
    | var name =>
        simp [canonicalAtomCST, canonicalNode, readerTokenBoundaries,
          readerTokenBoundariesList,
          canonicalVariableChars_readerTokenBoundaries]
    | grounded value => simp [atomSafe] at safe
    | expression atoms =>
        simp only [atomSafe, Bool.and_eq_true] at safe
        have body := canonicalAtoms_readerTokenBoundaries atoms
          (cursor + 1) safe.2
        let stop := cursor + (canonicalAtomsScalars atoms).length + 2
        have expressionBoundary :
            readerTokenBoundaries
                (.node "mm2:expression" cursor stop
                  [canonicalGapEmpty (cursor + 1),
                   canonicalAtomsCST atoms (cursor + 1)]) = true := by
          apply readerTokenBoundaries_neutralNode
          · decide
          · decide
          · simp [readerTokenBoundariesList, body]
        have atomBoundary :
            readerTokenBoundaries
                (.node "mm2:atom-expression" cursor stop
                  [.node "mm2:expression" cursor stop
                    [canonicalGapEmpty (cursor + 1),
                     canonicalAtomsCST atoms (cursor + 1)]]) = true := by
          apply readerTokenBoundaries_neutralNode
          · decide
          · decide
          · simp [readerTokenBoundariesList, expressionBoundary]
        simpa [canonicalAtomCST, canonicalNode, stop] using atomBoundary

  private theorem canonicalAtoms_readerTokenBoundaries
      (atoms : List Atom) (cursor : Nat) (safe : atomsSafe atoms = true) :
      readerTokenBoundaries (canonicalAtomsCST atoms cursor) = true := by
    cases atoms with
    | nil => rfl
    | cons atom rest =>
        simp only [atomsSafe, Bool.and_eq_true] at safe
        cases rest with
        | nil =>
            have atomBoundary := canonicalAtom_readerTokenBoundaries atom
              cursor safe.1
            have gapBoundary := canonicalGapEmpty_readerTokenBoundaries
              (cursor + (canonicalAtomScalars atom).length)
            have localBoundary := atomsBoundaryAdmitted_canonicalEmpty
              (canonicalAtomCST atom cursor)
              (cursor + (canonicalAtomScalars atom).length)
            have nodeBoundary := readerTokenBoundaries_atomsCons cursor
              (cursor + (canonicalAtomScalars atom).length)
              (canonicalAtomCST atom cursor)
              (canonicalGapEmpty
                (cursor + (canonicalAtomScalars atom).length))
              (canonicalNode "mm2:atoms-empty"
                (cursor + (canonicalAtomScalars atom).length)
                (cursor + (canonicalAtomScalars atom).length))
            have restBoundary :
                readerTokenBoundaries
                    (canonicalNode "mm2:atoms-empty"
                      (cursor + (canonicalAtomScalars atom).length)
                      (cursor + (canonicalAtomScalars atom).length)) = true := by
              rfl
            have admittedNode :
                readerTokenBoundaries
                    (.node "mm2:atoms-cons" cursor
                      (cursor + (canonicalAtomScalars atom).length)
                      [canonicalAtomCST atom cursor,
                       canonicalGapEmpty
                         (cursor + (canonicalAtomScalars atom).length),
                       canonicalNode "mm2:atoms-empty"
                         (cursor + (canonicalAtomScalars atom).length)
                         (cursor + (canonicalAtomScalars atom).length)]) = true := by
              rw [nodeBoundary, localBoundary, atomBoundary, gapBoundary,
                restBoundary]
              rfl
            simpa [canonicalAtomsCST, canonicalNode] using admittedNode
        | cons next tail =>
            have atomBoundary := canonicalAtom_readerTokenBoundaries atom
              cursor safe.1
            have gapBoundary := canonicalWhitespaceGap_readerTokenBoundaries
              ' ' (cursor + (canonicalAtomScalars atom).length)
            have restBoundary := canonicalAtoms_readerTokenBoundaries
              (next :: tail)
              (cursor + (canonicalAtomScalars atom).length + 1) safe.2
            have localBoundary := atomsBoundaryAdmitted_canonicalCons
              (canonicalAtomCST atom cursor)
              (cursor + (canonicalAtomScalars atom).length)
              (cursor + (canonicalAtomScalars atom).length + 1) next tail
            have nodeBoundary := readerTokenBoundaries_atomsCons cursor
              (cursor + (canonicalAtomsScalars (atom :: next :: tail)).length)
              (canonicalAtomCST atom cursor)
              (canonicalWhitespaceGap ' '
                (cursor + (canonicalAtomScalars atom).length))
              (canonicalAtomsCST (next :: tail)
                (cursor + (canonicalAtomScalars atom).length + 1))
            have admittedNode :
                readerTokenBoundaries
                    (.node "mm2:atoms-cons" cursor
                      (cursor +
                        (canonicalAtomsScalars (atom :: next :: tail)).length)
                      [canonicalAtomCST atom cursor,
                       canonicalWhitespaceGap ' '
                         (cursor + (canonicalAtomScalars atom).length),
                       canonicalAtomsCST (next :: tail)
                         (cursor + (canonicalAtomScalars atom).length + 1)]) = true := by
              rw [nodeBoundary, localBoundary, atomBoundary, gapBoundary,
                restBoundary]
              rfl
            simpa [canonicalAtomsCST, canonicalNode] using admittedNode
end

private theorem canonicalProgramTail_readerTokenBoundaries
    (program : List Atom) (cursor : Nat)
    (safe : atomsSafe program = true) :
    readerTokenBoundaries (canonicalProgramTailCST program cursor) = true := by
  induction program generalizing cursor with
  | nil =>
      simp [canonicalProgramTailCST, canonicalFinalLineFeedGap,
        canonicalWhitespaceGap, canonicalGapEmpty, canonicalLexical,
        canonicalNode, readerTokenBoundaries, readerTokenBoundariesList]
  | cons atom rest induction =>
      simp only [atomsSafe, Bool.and_eq_true] at safe
      simp [canonicalProgramTailCST, canonicalWhitespaceGap,
        canonicalGapEmpty, canonicalLexical, canonicalNode,
        readerTokenBoundaries, readerTokenBoundariesList,
        canonicalAtom_readerTokenBoundaries atom (cursor + 1) safe.1,
        induction (cursor + 1 + (canonicalAtomScalars atom).length) safe.2]

/-- Every canonical renderer tree satisfies the reader's maximal-token
boundary discipline, for arbitrary representation-safe MM2 programs. -/
theorem canonicalProgram_readerTokenBoundaries
    (program : List Atom) (cursor : Nat)
    (safe : programSafe program = true) :
    readerTokenBoundaries (canonicalProgramCST program cursor) = true := by
  simp only [programSafe, Bool.and_eq_true] at safe
  have recursiveSafe : atomsSafe program = true := by
    rw [atomsSafe_eq_all]
    exact safe.1
  cases program with
  | nil =>
      simp [canonicalProgramCST, canonicalFinalGapEmpty, canonicalGapEmpty,
        canonicalNode, readerTokenBoundaries, readerTokenBoundariesList]
  | cons atom rest =>
      simp only [atomsSafe, Bool.and_eq_true] at recursiveSafe
      simp [canonicalProgramCST, canonicalGapEmpty, canonicalNode,
        readerTokenBoundaries, readerTokenBoundariesList,
        canonicalAtom_readerTokenBoundaries atom cursor recursiveSafe.1,
        canonicalProgramTail_readerTokenBoundaries rest
          (cursor + (canonicalAtomScalars atom).length) recursiveSafe.2]

/-- A parser derivation and successful lowering together form the exact
admission boundary consumed by MM2 execution. -/
structure ParsedProgram (input : List Nat) where
  tree : CST
  atoms : List Atom
  derivation :
    ParserPackRootDerives mm2ParserProfile mm2ParserPackPlan input tree
  tokenBoundaries : readerTokenBoundaries tree = true
  lowering : elaborateRootCST tree = .program atoms

/-- Canonical parsing and syntax-to-Atom lowering commute for every complete
program admitted by the ordinary MM2 representation boundary. -/
theorem canonical_program_is_parsed
    (program : List Atom) (safe : programSafe program = true) :
    Nonempty (ParsedProgram (canonicalProgramScalars program)) := by
  obtain ⟨derivation⟩ := canonical_program_has_parser_derivation program safe
  exact ⟨{
    tree := canonicalProgramCST program 0
    atoms := program
    derivation := derivation
    tokenBoundaries := canonicalProgram_readerTokenBoundaries program 0 safe
    lowering := elaborate_canonical_program program 0 safe }⟩

/-- The actual ordinary renderer spelling is accepted by the generated
ParserPack and lowers back to the exact source atom occurrences. -/
theorem render_program_has_exact_parser_lowering
    (program : List Atom) (safe : programSafe program = true) :
    ∃ rendered,
      renderProgram? program = some rendered ∧
      Nonempty (ParsedProgram (stringScalars rendered)) := by
  have safeParts :
      program.all atomSafe = true ∧ programVariableBudget program = true := by
    simpa only [programSafe, Bool.and_eq_true] using safe
  have recursiveSafe : atomsSafe program = true := by
    rw [atomsSafe_eq_all]
    exact safeParts.1
  have parsed := canonical_program_is_parsed program safe
  rw [canonicalProgramScalars_eq_stringScalars_ordinaryProgramString
    program recursiveSafe] at parsed
  exact ⟨ordinaryProgramString program, by simp [renderProgram?, safe], parsed⟩

/-- Any successful ordinary-MM2 rendering—not only a separately chosen
canonical witness—has a generated parse whose lowering recovers the exact
source atom occurrences. -/
theorem successful_render_has_exact_parser_lowering
    {program : List Atom} {rendered : String}
    (renderedExact : renderProgram? program = some rendered) :
    ∃ parsed : ParsedProgram (stringScalars rendered),
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
  rw [canonicalProgramScalars_eq_stringScalars_ordinaryProgramString
    program recursiveSafe] at derivation
  exact ⟨{
    tree := canonicalProgramCST program 0
    atoms := program
    derivation := derivation
    tokenBoundaries := canonicalProgram_readerTokenBoundaries program 0 safe
    lowering := elaborate_canonical_program program 0 safe }, rfl⟩

theorem programSafe_of_elaborateRootCST_eq_program
    {tree : CST} {atoms : List Atom}
    (lowering : elaborateRootCST tree = .program atoms) :
    programSafe atoms = true := by
  have finishAttribute_safe : ∀ (result : Attribute) (values : List Atom),
      finishAttribute result = .program values →
        programSafe values = true
    | .terminal _, _, contradiction => by
        simp [finishAttribute] at contradiction
    | .unit, _, contradiction => by
        simp [finishAttribute] at contradiction
    | .scalar _, _, contradiction => by
        simp [finishAttribute] at contradiction
    | .codepoints _, _, contradiction => by
        simp [finishAttribute] at contradiction
    | .atom _, _, contradiction => by
        simp [finishAttribute] at contradiction
    | .atoms _, _, contradiction => by
        simp [finishAttribute] at contradiction
    | .program source, target, exact => by
        by_cases safe : programSafe source = true
        · simp [finishAttribute, safe] at exact
          subst target
          exact safe
        · simp [finishAttribute, safe] at exact
  have finishElaboration_safe :
      ∀ (result : Except ElaborationError Attribute) (values : List Atom),
      finishElaboration result = .program values →
        programSafe values = true
    | .ok result, values, exact =>
        finishAttribute_safe result values exact
    | .error _, _, contradiction => by
        simp [finishElaboration] at contradiction
  exact finishElaboration_safe (elaborateTree tree) atoms lowering

theorem ParsedProgram.safe {input : List Nat} (parsed : ParsedProgram input) :
    programSafe parsed.atoms = true :=
  programSafe_of_elaborateRootCST_eq_program parsed.lowering

/-- The ordinary MM2 loader has support semantics, so repeated parsed atoms
are removed only at this explicit syntax-to-execution seam. -/
def ParsedProgram.initialSupport {input : List Nat}
    (parsed : ParsedProgram input) : List Atom :=
  parsed.atoms.eraseDups

private theorem eraseDups_nodup :
    (atoms : List Atom) → atoms.eraseDups.Nodup
  | [] => by simp
  | atom :: atoms => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, eraseDups_nodup _⟩
      intro member
      rw [List.mem_eraseDups, List.mem_filter] at member
      simp at member
termination_by atoms => atoms.length
decreasing_by
  have shorter :=
    List.length_filter_le (fun other => !other == atom) atoms
  simp only [List.length_cons]
  omega

theorem ParsedProgram.initialSupport_nodup
    {input : List Nat} (parsed : ParsedProgram input) :
    parsed.initialSupport.Nodup :=
  eraseDups_nodup parsed.atoms

/-- The parsed program enters the existing executable reflective MM2 GSLT
through its generated OSLF native type; parsing does not introduce a second
execution relation. -/
theorem ParsedProgram.execution_native_type_iff
    {input : List Nat} (parsed : ParsedProgram input)
    (policy : UnsupportedExecPolicy) (target : List Atom) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveNativeListExecGSLT policy)).satisfies
        parsed.initialSupport
        (reflectiveNativeListExactTargetNativeType policy target).pred ↔
      ReflectiveComputable.cReflectiveSourceWorkQueueStep
        policy parsed.initialSupport =
        some target :=
  satisfies_reflectiveNativeListExactTargetNativeType_iff_step
    policy parsed.initialSupport target

/-- Canonical rendering, generated parsing, syntax lowering, and the existing
reflective MM2 execution GSLT form one commuting boundary for every
representation-safe program. -/
theorem render_parse_execution_commutes
    (program : List Atom) (safe : programSafe program = true) :
    ∃ (rendered : String) (parsed : ParsedProgram (stringScalars rendered)),
      renderProgram? program = some rendered ∧
      parsed.atoms = program ∧
      parsed.initialSupport = program.eraseDups ∧
      ∀ (policy : UnsupportedExecPolicy) (target : List Atom),
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveNativeListExecGSLT policy)).satisfies
            parsed.initialSupport
            (reflectiveNativeListExactTargetNativeType policy target).pred ↔
          ReflectiveComputable.cReflectiveSourceWorkQueueStep
            policy parsed.initialSupport = some target := by
  have safeParts :
      program.all atomSafe = true ∧ programVariableBudget program = true := by
    simpa only [programSafe, Bool.and_eq_true] using safe
  have recursiveSafe : atomsSafe program = true := by
    rw [atomsSafe_eq_all]
    exact safeParts.1
  obtain ⟨canonicalDerivation⟩ :=
    canonical_program_has_parser_derivation program safe
  let rendered := ordinaryProgramString program
  have derivation :
      ParserPackRootDerives mm2ParserProfile mm2ParserPackPlan
        (stringScalars rendered) (canonicalProgramCST program 0) := by
    simpa [rendered,
      canonicalProgramScalars_eq_stringScalars_ordinaryProgramString
        program recursiveSafe] using canonicalDerivation
  let parsed : ParsedProgram (stringScalars rendered) := {
    tree := canonicalProgramCST program 0
    atoms := program
    derivation := derivation
    tokenBoundaries := canonicalProgram_readerTokenBoundaries program 0 safe
    lowering := elaborate_canonical_program program 0 safe
  }
  refine ⟨rendered, parsed, by simp [rendered, renderProgram?, safe], rfl,
    rfl, ?_⟩
  intro policy target
  exact parsed.execution_native_type_iff policy target

/-! ## Exact parser and lowering canaries -/

private def node (label : String) (start stop : Nat)
    (children : List CST := []) : CST :=
  .node label start stop children

private def lexical (label : String) (codepoint start : Nat) : CST :=
  node label start (start + 1) [.terminal [codepoint] start (start + 1)]

private def gapEmpty (cursor : Nat) : CST :=
  node "mm2:gap-empty" cursor cursor

private def finalGapEmpty (cursor : Nat) : CST :=
  node "mm2:final-gap-regular" cursor cursor [gapEmpty cursor]

private def emptyProgramTree : CST :=
  node "mm2:program-empty" 0 0 [finalGapEmpty 0]

private def emptyExpressionTree : CST :=
  node "mm2:program-cons" 0 2
    [gapEmpty 0,
     node "mm2:atom-expression" 0 2
       [node "mm2:expression" 0 2
         [gapEmpty 1, node "mm2:atoms-empty" 1 1]],
     node "mm2:program-empty" 2 2 [finalGapEmpty 2]]

private def pVariableXTree : CST :=
  node "mm2:program-cons" 0 6
    [gapEmpty 0,
     node "mm2:atom-expression" 0 6
       [node "mm2:expression" 0 6
         [gapEmpty 1,
          node "mm2:atoms-cons" 1 5
            [node "mm2:atom-symbol" 1 2
               [node "mm2:symbol-bare" 1 2
                 [lexical "mm2:lex-bare-head" 112 1,
                  node "mm2:bare-tail-empty" 2 2]],
             node "mm2:gap-cons" 2 3
               [node "mm2:gap-whitespace" 2 3
                  [lexical "mm2:lex-whitespace" 32 2],
                gapEmpty 3],
             node "mm2:atoms-cons" 3 5
               [node "mm2:atom-variable" 3 5
                  [node "mm2:variable" 3 5
                    [node "mm2:variable-chars-cons" 4 5
                      [lexical "mm2:lex-variable-char" 120 4,
                       node "mm2:variable-chars-empty" 5 5]]],
                gapEmpty 5,
                node "mm2:atoms-empty" 5 5]]]],
     node "mm2:program-empty" 6 6 [finalGapEmpty 6]]

theorem empty_program_elaborates_exactly :
    elaborateRootCST emptyProgramTree = .program [] := by
  rfl

theorem empty_expression_elaborates_exactly :
    elaborateRootCST emptyExpressionTree =
      .program [.expression []] := by
  rfl

theorem symbol_variable_expression_elaborates_exactly :
    elaborateRootCST pVariableXTree =
      .program [.expression [.symbol "p", .var "x"]] := by
  change (if programSafe
      [.expression [.symbol (codepointsToString [112]),
        .var (codepointsToString [120])]] then
      ElaborationOutcome.program
        [.expression [.symbol (codepointsToString [112]),
        .var (codepointsToString [120])]]
    else ElaborationOutcome.unsupportedRepresentation) =
      ElaborationOutcome.program
        [.expression [.symbol "p", .var "x"]]
  rw [codepointsToString_112, codepointsToString_120]
  rw [show programSafe
      [.expression [.symbol "p", .var "x"]] = true by
    simp [programSafe, programVariableBudget, atomVariableBudget,
      atomVariableNames, atomsVariableNames, atomSafe, atomsSafe, bareSymbolSafe,
      variableNameSafe, morkUtf8Bytes, Char.utf8Size]
    decide]
  simp

private def emptyVariableTree : CST :=
  node "mm2:program-cons" 0 1
    [gapEmpty 0,
     node "mm2:atom-variable" 0 1
       [node "mm2:variable" 0 1
         [node "mm2:variable-chars-empty" 1 1]],
     node "mm2:program-empty" 1 1 [finalGapEmpty 1]]

/-- The ordinary MORK reader admits bare `$` as the empty-spelling variable,
and canonical lowering preserves that exact atom. -/
theorem empty_variable_elaborates_exactly :
    elaborateRootCST emptyVariableTree = .program [.var ""] := by
  rfl

private def malformedProgramTree : CST :=
  node "mm2:program-empty" 0 0 []

theorem malformed_program_tree_is_rejected :
    elaborateRootCST malformedProgramTree = .malformedCST := by
  rfl

private def eofCommentPTree : CST :=
  node "mm2:program-empty" 0 2
    [node "mm2:final-gap-comment" 0 2
      [gapEmpty 0,
       node "mm2:eof-comment" 0 2
         [node "mm2:comment-tail-cons" 1 2
           [lexical "mm2:lex-comment-char" 112 1,
            node "mm2:comment-tail-empty" 2 2]]]]

/-- An EOF comment consumes its complete tail.  The character after `;`
cannot be exposed as a top-level executable atom. -/
theorem eof_comment_elaborates_to_empty_program :
    elaborateRootCST eofCommentPTree = .program [] := by
  rfl

theorem duplicate_syntax_branches_remain_visible :
    (elaborateBranches [emptyProgramTree, emptyProgramTree]).length = 2 := by
  rfl

theorem duplicate_syntax_branches_resolve_semantically :
    resolvePrograms [emptyProgramTree, emptyProgramTree] = .unique [] := by
  rfl

theorem distinct_programs_are_not_silently_selected :
    resolvePrograms [emptyProgramTree, emptyExpressionTree] =
      .ambiguous [[], [.expression []]] := by
  rfl

theorem generated_parser_accepts_empty_program :
    ∃ row ∈ enumerateRootWithin 6 mm2ParserProfile mm2ParserPackPlan [],
      row.tree = emptyProgramTree := by
  decide +kernel

theorem generated_parser_empty_program_has_semantic_derivation :
    Nonempty (ParserPackRootDerives mm2ParserProfile mm2ParserPackPlan []
      emptyProgramTree) := by
  obtain ⟨row, member, treeExact⟩ := generated_parser_accepts_empty_program
  obtain ⟨replay⟩ := enumerateDerivationsWithin_sound member
  rw [treeExact] at replay
  exact ⟨replay.derivation⟩

private def emptyExpressionInput : List Nat := [40, 41]

theorem generated_parser_accepts_empty_expression :
    ∃ row ∈ enumerateRootWithin 11 mm2ParserProfile mm2ParserPackPlan
        emptyExpressionInput,
      row.tree = emptyExpressionTree := by
  decide +kernel

theorem generated_parser_empty_expression_has_semantic_derivation :
    Nonempty (ParserPackRootDerives mm2ParserProfile mm2ParserPackPlan
      emptyExpressionInput emptyExpressionTree) := by
  obtain ⟨row, member, treeExact⟩ :=
    generated_parser_accepts_empty_expression
  obtain ⟨replay⟩ := enumerateDerivationsWithin_sound member
  rw [treeExact] at replay
  exact ⟨replay.derivation⟩

private def pVariableXInput : List Nat := [40, 112, 32, 36, 120, 41]

theorem generated_parser_accepts_symbol_variable_expression :
    ∃ row ∈ enumerateRootWithin 28 mm2ParserProfile mm2ParserPackPlan
        pVariableXInput,
      row.tree = pVariableXTree := by
  decide +kernel

theorem generated_symbol_variable_expression_is_admitted :
    Nonempty (ParsedProgram pVariableXInput) := by
  obtain ⟨row, member, treeExact⟩ :=
    generated_parser_accepts_symbol_variable_expression
  obtain ⟨replay⟩ := enumerateDerivationsWithin_sound member
  refine ⟨{
    tree := row.tree
    atoms := [.expression [.symbol "p", .var "x"]]
    derivation := replay.derivation
    tokenBoundaries := by rw [treeExact]; decide +kernel
    lowering := ?_ }⟩
  rw [treeExact]
  exact symbol_variable_expression_elaborates_exactly

private def eofCommentPInput : List Nat := [59, 112]

theorem generated_parser_keeps_eof_comment_tail_inert :
    ∃ row ∈ enumerateRootWithin 14 mm2ParserProfile mm2ParserPackPlan
        eofCommentPInput,
      row.tree = eofCommentPTree := by
  decide +kernel

theorem generated_eof_comment_cannot_expose_code :
    ∀ row ∈ enumerateRootWithin 14 mm2ParserProfile mm2ParserPackPlan
        eofCommentPInput,
      elaborateRootCST row.tree ≠ .program [.symbol "p"] := by
  decide +kernel

private def generatedTreesWithin (fuel : Nat) (input : List Nat) : List CST :=
  (enumerateRootWithin fuel mm2ParserProfile mm2ParserPackPlan input).map
    fun row => row.tree

private def pDollarXInput : List Nat := [112, 36, 120]

/-- The underlying scannerless grammar deliberately retains all physical
parses.  Without reader-token admission, `p$x` has four distinct atom
interpretations, so branch selection would be unsound. -/
theorem generated_pDollarX_exposes_scannerless_ambiguity :
    (representedPrograms
      (generatedTreesWithin 24 pDollarXInput)).eraseDups.length = 4 := by
  decide +kernel

/-- Reader-token admission restores the exact maximal token consumed by the
ordinary MM2 reader: `p$x` is one symbol, never a symbol-variable split. -/
theorem generated_pDollarX_is_unique_after_boundary_admission :
    resolveBoundaryAdmittedPrograms
        (generatedTreesWithin 24 pDollarXInput) =
      .unique [.symbol "p$x"] := by
  decide +kernel

private def pSemicolonXInput : List Nat := [112, 59, 120]

/-- A semicolon inside a bare token is not retroactively a comment boundary.
The admitted parser therefore agrees with the ordinary reader on `p;x`. -/
theorem generated_pSemicolonX_is_one_symbol :
    resolveBoundaryAdmittedPrograms
        (generatedTreesWithin 24 pSemicolonXInput) =
      .unique [.symbol "p;x"] := by
  decide +kernel

/-- A left parenthesis is a real reader delimiter, so a bare symbol may be
followed immediately by an expression without whitespace. -/
theorem generated_symbol_then_expression_adjacency_is_admitted :
    resolveBoundaryAdmittedPrograms
        (generatedTreesWithin 24 [112, 40, 41]) =
      .unique [.symbol "p", .expression []] := by
  decide +kernel

/-- A closing parenthesis delimits an expression, so the following bare
symbol also needs no intervening whitespace. -/
theorem generated_expression_then_symbol_adjacency_is_admitted :
    resolveBoundaryAdmittedPrograms
        (generatedTreesWithin 24 [40, 41, 112]) =
      .unique [.expression [], .symbol "p"] := by
  decide +kernel

/-- Missing closing parenthesis has no generated ParserPack derivation below
the complete structural height needed by the corresponding valid example. -/
theorem missing_right_parenthesis_has_no_bounded_parse :
    enumerateRootWithin 11 mm2ParserProfile mm2ParserPackPlan [40] = [] := by
  decide +kernel

#print axioms empty_program_elaborates_exactly
#print axioms empty_expression_elaborates_exactly
#print axioms symbol_variable_expression_elaborates_exactly
#print axioms empty_variable_elaborates_exactly
#print axioms malformed_program_tree_is_rejected
#print axioms canonical_program_has_parser_derivation
#print axioms canonical_program_is_enumerated
#print axioms canonical_program_is_parsed
#print axioms render_program_has_exact_parser_lowering
#print axioms successful_render_has_exact_parser_lowering
#print axioms canonicalProgram_readerTokenBoundaries
#print axioms programSafe_of_elaborateRootCST_eq_program
#print axioms ParsedProgram.execution_native_type_iff
#print axioms render_parse_execution_commutes
#print axioms eof_comment_elaborates_to_empty_program
#print axioms distinct_programs_are_not_silently_selected
#print axioms generated_parser_empty_program_has_semantic_derivation
#print axioms generated_parser_empty_expression_has_semantic_derivation
#print axioms generated_symbol_variable_expression_is_admitted
#print axioms generated_eof_comment_cannot_expose_code
#print axioms generated_pDollarX_exposes_scannerless_ambiguity
#print axioms generated_pDollarX_is_unique_after_boundary_admission
#print axioms generated_pSemicolonX_is_one_symbol
#print axioms generated_symbol_then_expression_adjacency_is_admitted
#print axioms generated_expression_then_symbol_adjacency_is_admitted
#print axioms missing_right_parenthesis_has_no_bounded_parse

end Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxSemantics
