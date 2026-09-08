import Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenHeightBound
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSyntax
import Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

/-!
# Exact semantics of maximal-token MM2 syntax trees

The generated parser returns occurrence-preserving CSTs.  This module lowers
the maximal-token grammar directly to the ordinary MM2 atom carrier.  Token
boundary correctness is carried by the grammar's program and atom-list
states, so lowering needs no branch filter and no independent reader test.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics

open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSyntax
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
open Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

inductive ElaborationOutcome where
  | program (atoms : List Atom)
  | malformedCST
  deriving Repr, DecidableEq

inductive ElaborationError where
  | malformedCST
  deriving Repr, DecidableEq

inductive Attribute where
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

def lexicalScalar? (children : List Attribute) : Option Nat :=
  match children with
  | [.terminal [codepoint]] => some codepoint
  | _ => none

def elaborateLexicalNode? (label : String)
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
  | some _ => (lexicalScalar? children).map .scalar

def elaborateNode (label : String)
    (children : List Attribute) : Except ElaborationError Attribute :=
  match elaborateLexicalNode? label children with
  | some lexical => .ok lexical
  | none =>
    match label, children with
    | "mm2:program-empty", [] => .ok (.program [])
    | "mm2:program-whitespace", [.scalar _, .program rest] =>
        .ok (.program rest)
    | "mm2:program-line-comment", [.unit, .program rest] =>
        .ok (.program rest)
    | "mm2:program-eof-comment", [.unit] => .ok (.program [])
    | "mm2:program-closed", [.atom atom, .program rest] =>
        .ok (.program (atom :: rest))
    | "mm2:program-open", [.atom atom, .program rest] =>
        .ok (.program (atom :: rest))
    | "mm2:program-after-open-end", [] => .ok (.program [])
    | "mm2:program-after-open-whitespace", [.scalar _, .program rest] =>
        .ok (.program rest)
    | "mm2:program-after-open-expression", [.atom atom, .program rest] =>
        .ok (.program (atom :: rest))

    | "mm2:expression", [.atoms atoms] =>
        .ok (.atom (.expression atoms))
    | "mm2:atoms-empty", [] => .ok (.atoms [])
    | "mm2:atoms-whitespace", [.scalar _, .atoms rest] =>
        .ok (.atoms rest)
    | "mm2:atoms-line-comment", [.unit, .atoms rest] =>
        .ok (.atoms rest)
    | "mm2:atoms-closed", [.atom atom, .atoms rest] =>
        .ok (.atoms (atom :: rest))
    | "mm2:atoms-open", [.atom atom, .atoms rest] =>
        .ok (.atoms (atom :: rest))
    | "mm2:atoms-after-open-end", [] => .ok (.atoms [])
    | "mm2:atoms-after-open-whitespace", [.scalar _, .atoms rest] =>
        .ok (.atoms rest)
    | "mm2:atoms-after-open-expression", [.atom atom, .atoms rest] =>
        .ok (.atoms (atom :: rest))

    | "mm2:closed-atom-quoted", [.codepoints codepoints] =>
        .ok (.atom (.symbol (codepointsToString codepoints)))
    | "mm2:closed-atom-expression", [.atom atom] => .ok (.atom atom)
    | "mm2:open-atom-bare", [.scalar head, .codepoints tail] =>
        .ok (.atom (.symbol (codepointsToString (head :: tail))))
    | "mm2:open-atom-variable", [.codepoints codepoints] =>
        .ok (.atom (.var (codepointsToString codepoints)))

    | "mm2:line-comment", [.codepoints _, .scalar 10] => .ok .unit
    | "mm2:eof-comment", [.codepoints _] => .ok .unit
    | "mm2:comment-tail-empty", [] => .ok (.codepoints [])
    | "mm2:comment-tail-cons", [.scalar head, .codepoints tail] =>
        .ok (.codepoints (head :: tail))
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
  def elaborateTrees :
      List CST -> Except ElaborationError (List Attribute)
    | [] => .ok []
    | tree :: trees =>
        match elaborateTree tree with
        | .error error => .error error
        | .ok head =>
            match elaborateTrees trees with
            | .error error => .error error
            | .ok tail => .ok (head :: tail)

  def elaborateTree : CST -> Except ElaborationError Attribute
    | .terminal codepoints _ _ => .ok (.terminal codepoints)
    | .node label _ _ children =>
        match elaborateTrees children with
        | .error error => .error error
        | .ok attributes => elaborateNode label attributes
end

def finishAttribute : Attribute -> ElaborationOutcome
  | .program atoms => .program atoms
  | _ => .malformedCST

def finishElaboration :
    Except ElaborationError Attribute -> ElaborationOutcome
  | .ok result => finishAttribute result
  | .error _ => .malformedCST

def elaborateRootCST (tree : CST) : ElaborationOutcome :=
  finishElaboration (elaborateTree tree)

def stringScalars (value : String) : List Nat :=
  value.toList.map Char.toNat

mutual
  def canonicalAtomScalars : Atom -> List Nat
    | .symbol value => stringScalars value
    | .var name => 36 :: stringScalars name
    | .grounded _ => []
    | .expression atoms => 40 :: canonicalAtomsScalars atoms ++ [41]

  def canonicalAtomsScalars : List Atom -> List Nat
    | [] => []
    | atom :: rest =>
        canonicalAtomScalars atom ++
          match rest with
          | [] => []
          | _ :: _ => 32 :: canonicalAtomsScalars rest
end

def canonicalProgramScalars : List Atom -> List Nat
  | [] => []
  | atom :: rest => canonicalAtomScalars atom ++ 10 ::
      canonicalProgramScalars rest

def node (label : String) (start stop : Nat)
    (children : List CST := []) : CST :=
  .node label start stop children

def lexical (label : String) (character : Char)
    (start : Nat) : CST :=
  node label start (start + 1)
    [.terminal [character.toNat] start (start + 1)]

def canonicalBareTail : List Char -> Nat -> CST
  | [], cursor => node "mm2:bare-tail-empty" cursor cursor
  | character :: rest, cursor =>
      node "mm2:bare-tail-cons" cursor (cursor + (character :: rest).length)
        [lexical "mm2:lex-bare-char" character cursor,
         canonicalBareTail rest (cursor + 1)]

def canonicalVariableChars : List Char -> Nat -> CST
  | [], cursor => node "mm2:variable-chars-empty" cursor cursor
  | character :: rest, cursor =>
      node "mm2:variable-chars-cons" cursor
        (cursor + (character :: rest).length)
        [lexical "mm2:lex-variable-char" character cursor,
         canonicalVariableChars rest (cursor + 1)]

def canonicalOpenAtom : Atom -> Nat -> CST
  | .symbol value, cursor =>
      match value.toList with
      | [] => node "mm2:unsupported-empty-symbol" cursor cursor
      | head :: tail =>
          let stop := cursor + (head :: tail).length
          node "mm2:open-atom-bare" cursor stop
            [lexical "mm2:lex-bare-head" head cursor,
             canonicalBareTail tail (cursor + 1)]
  | .var name, cursor =>
      let characters := name.toList
      let stop := cursor + 1 + characters.length
      node "mm2:open-atom-variable" cursor stop
        [node "mm2:variable" cursor stop
          [canonicalVariableChars characters (cursor + 1)]]
  | _, cursor => node "mm2:not-open-atom" cursor cursor

mutual
  def canonicalClosedAtom : Atom -> Nat -> CST
    | .expression atoms, cursor =>
        let stop := cursor + (canonicalAtomsScalars atoms).length + 2
        node "mm2:closed-atom-expression" cursor stop
          [node "mm2:expression" cursor stop
            [canonicalAtoms atoms (cursor + 1)]]
    | _, cursor => node "mm2:not-closed-atom" cursor cursor

  def canonicalAtoms : List Atom -> Nat -> CST
    | [], cursor => node "mm2:atoms-empty" cursor cursor
    | atom :: rest, cursor =>
        let atomStop := cursor + (canonicalAtomScalars atom).length
        match atom with
        | .expression _ =>
            let restTree :=
              match rest with
              | [] => node "mm2:atoms-empty" atomStop atomStop
              | _ :: _ =>
                  node "mm2:atoms-whitespace" atomStop
                    (atomStop + 1 + (canonicalAtomsScalars rest).length)
                    [lexical "mm2:lex-whitespace" ' ' atomStop,
                     canonicalAtoms rest (atomStop + 1)]
            node "mm2:atoms-closed" cursor
              (cursor + (canonicalAtomsScalars (atom :: rest)).length)
              [canonicalClosedAtom atom cursor,
               restTree]
        | .symbol _ | .var _ =>
            let restTree :=
              match rest with
              | [] => node "mm2:atoms-after-open-end" atomStop atomStop
              | _ :: _ =>
                  node "mm2:atoms-after-open-whitespace" atomStop
                    (atomStop + 1 + (canonicalAtomsScalars rest).length)
                    [lexical "mm2:lex-whitespace" ' ' atomStop,
                     canonicalAtoms rest (atomStop + 1)]
            node "mm2:atoms-open" cursor
              (cursor + (canonicalAtomsScalars (atom :: rest)).length)
              [canonicalOpenAtom atom cursor,
               restTree]
        | .grounded _ => node "mm2:unsupported-grounded" cursor cursor
end

def canonicalProgramCST : List Atom -> Nat -> CST
  | [], cursor => node "mm2:program-empty" cursor cursor
  | atom :: rest, cursor =>
      let atomStop := cursor + (canonicalAtomScalars atom).length
      let stop := cursor + (canonicalProgramScalars (atom :: rest)).length
      let restTree := canonicalProgramCST rest (atomStop + 1)
      match atom with
      | .expression _ =>
          node "mm2:program-closed" cursor stop
            [canonicalClosedAtom atom cursor,
             node "mm2:program-whitespace" atomStop stop
               [lexical "mm2:lex-whitespace" '\n' atomStop, restTree]]
      | .symbol _ | .var _ =>
          node "mm2:program-open" cursor stop
            [canonicalOpenAtom atom cursor,
             node "mm2:program-after-open-whitespace" atomStop stop
               [lexical "mm2:lex-whitespace" '\n' atomStop, restTree]]
      | .grounded _ => node "mm2:unsupported-grounded" cursor cursor

theorem codepointsToString_stringScalars (value : String) :
    codepointsToString (stringScalars value) = value := by
  apply String.toList_injective
  simp [codepointsToString, stringScalars, Function.comp_def,
    Char.ofNat_toNat]

mutual
  theorem canonicalAtomScalars_eq_rendererScalars
      (atom : Atom) (safe : atomSafe atom = true) :
      canonicalAtomScalars atom = stringScalars (ordinaryAtomString atom) := by
    cases atom with
    | symbol value =>
        rw [canonicalAtomScalars, ordinaryAtomString.eq_1]
    | var name =>
        rw [canonicalAtomScalars, ordinaryAtomString.eq_2]
        simp [stringScalars, String.toList_append]
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
            rw [canonicalAtomsScalars_eq_rendererScalars
              (atom :: rest) safe.2]
            simp [stringScalars, String.toList_append]

  theorem canonicalAtomsScalars_eq_rendererScalars
      (atoms : List Atom) (safe : atomsSafe atoms = true) :
      canonicalAtomsScalars atoms =
        stringScalars (ordinaryAtomString.renderAtoms atoms) := by
    cases atoms with
    | nil =>
        rw [canonicalAtomsScalars, ordinaryAtomString.renderAtoms.eq_1]
        simp [stringScalars]
    | cons atom rest =>
        simp only [atomsSafe, Bool.and_eq_true] at safe
        cases rest with
        | nil =>
            rw [canonicalAtomsScalars, ordinaryAtomString.renderAtoms.eq_2]
            simpa using canonicalAtomScalars_eq_rendererScalars atom safe.1
        | cons next tail =>
            rw [canonicalAtomsScalars]
            rw [ordinaryAtomString.renderAtoms.eq_3 atom (next :: tail)
              (by simp)]
            rw [canonicalAtomScalars_eq_rendererScalars atom safe.1]
            rw [canonicalAtomsScalars_eq_rendererScalars
              (next :: tail) safe.2]
            simp [stringScalars, String.toList_append]
end

theorem canonicalProgramScalars_eq_rendererScalars
    (program : List Atom) (safe : atomsSafe program = true) :
    canonicalProgramScalars program =
      stringScalars (ordinaryProgramString program) := by
  induction program with
  | nil =>
      simp [canonicalProgramScalars, ordinaryProgramString, stringScalars]
  | cons atom rest induction =>
      simp only [atomsSafe, Bool.and_eq_true] at safe
      rw [canonicalProgramScalars, ordinaryProgramString]
      rw [canonicalAtomScalars_eq_rendererScalars atom safe.1]
      rw [induction safe.2]
      simp [stringScalars, String.toList_append]

private theorem elaborateLexical_bareHead
    (character : Char) :
    elaborateNode "mm2:lex-bare-head" [.terminal [character.toNat]] =
      (Except.ok (.scalar character.toNat) :
        Except ElaborationError Attribute) := by
  rfl

private theorem elaborateLexical_bareChar
    (character : Char) :
    elaborateNode "mm2:lex-bare-char" [.terminal [character.toNat]] =
      (Except.ok (.scalar character.toNat) :
        Except ElaborationError Attribute) := by
  rfl

private theorem elaborateLexical_variableChar
    (character : Char) :
    elaborateNode "mm2:lex-variable-char" [.terminal [character.toNat]] =
      (Except.ok (.scalar character.toNat) :
        Except ElaborationError Attribute) := by
  rfl

private theorem elaborateLexical_space :
    elaborateNode "mm2:lex-whitespace" [.terminal [32]] =
      (Except.ok (.scalar 32) : Except ElaborationError Attribute) := by
  rfl

private theorem elaborateLexical_lineFeed :
    elaborateNode "mm2:lex-whitespace" [.terminal [10]] =
      (Except.ok (.scalar 10) : Except ElaborationError Attribute) := by
  rfl

private theorem elaborateNode_bareTailEmpty :
    elaborateNode "mm2:bare-tail-empty" [] = .ok (.codepoints []) := by
  rfl

private theorem elaborateNode_bareTailCons (head : Nat) (tail : List Nat) :
    elaborateNode "mm2:bare-tail-cons"
      [.scalar head, .codepoints tail] = .ok (.codepoints (head :: tail)) := by
  rfl

private theorem elaborateNode_variableCharsEmpty :
    elaborateNode "mm2:variable-chars-empty" [] =
      .ok (.codepoints []) := by
  rfl

private theorem elaborateNode_variableCharsCons
    (head : Nat) (tail : List Nat) :
    elaborateNode "mm2:variable-chars-cons"
      [.scalar head, .codepoints tail] = .ok (.codepoints (head :: tail)) := by
  rfl

private theorem elaborateNode_variable (values : List Nat) :
    elaborateNode "mm2:variable" [.codepoints values] =
      .ok (.codepoints values) := by
  rfl

private theorem elaborateNode_openBare (head : Nat) (tail : List Nat) :
    elaborateNode "mm2:open-atom-bare" [.scalar head, .codepoints tail] =
      .ok (.atom (.symbol (codepointsToString (head :: tail)))) := by
  rfl

private theorem elaborateNode_openVariable (values : List Nat) :
    elaborateNode "mm2:open-atom-variable" [.codepoints values] =
      .ok (.atom (.var (codepointsToString values))) := by
  rfl

private theorem elaborateNode_expression (values : List Atom) :
    elaborateNode "mm2:expression" [.atoms values] =
      .ok (.atom (.expression values)) := by
  rfl

private theorem elaborateNode_closedExpression (value : Atom) :
    elaborateNode "mm2:closed-atom-expression" [.atom value] =
      .ok (.atom value) := by
  rfl

private theorem elaborateNode_atomsEmpty :
    elaborateNode "mm2:atoms-empty" [] = .ok (.atoms []) := by
  rfl

private theorem elaborateNode_atomsOpen (head : Atom) (tail : List Atom) :
    elaborateNode "mm2:atoms-open" [.atom head, .atoms tail] =
      .ok (.atoms (head :: tail)) := by
  rfl

private theorem elaborateNode_atomsClosed (head : Atom) (tail : List Atom) :
    elaborateNode "mm2:atoms-closed" [.atom head, .atoms tail] =
      .ok (.atoms (head :: tail)) := by
  rfl

private theorem elaborateNode_atomsAfterOpenEnd :
    elaborateNode "mm2:atoms-after-open-end" [] = .ok (.atoms []) := by
  rfl

private theorem elaborateNode_atomsAfterOpenWhitespace
    (head : Nat) (tail : List Atom) :
    elaborateNode "mm2:atoms-after-open-whitespace"
      [.scalar head, .atoms tail] = .ok (.atoms tail) := by
  rfl

private theorem elaborateNode_atomsWhitespace
    (head : Nat) (tail : List Atom) :
    elaborateNode "mm2:atoms-whitespace" [.scalar head, .atoms tail] =
      .ok (.atoms tail) := by
  rfl

private theorem elaborateNode_programEmpty :
    elaborateNode "mm2:program-empty" [] = .ok (.program []) := by
  rfl

private theorem elaborateNode_programOpen (head : Atom) (tail : List Atom) :
    elaborateNode "mm2:program-open" [.atom head, .program tail] =
      .ok (.program (head :: tail)) := by
  rfl

private theorem elaborateNode_programClosed
    (head : Atom) (tail : List Atom) :
    elaborateNode "mm2:program-closed" [.atom head, .program tail] =
      .ok (.program (head :: tail)) := by
  rfl

private theorem elaborateNode_programAfterOpenWhitespace
    (head : Nat) (tail : List Atom) :
    elaborateNode "mm2:program-after-open-whitespace"
      [.scalar head, .program tail] = .ok (.program tail) := by
  rfl

private theorem elaborateNode_programWhitespace
    (head : Nat) (tail : List Atom) :
    elaborateNode "mm2:program-whitespace" [.scalar head, .program tail] =
      .ok (.program tail) := by
  rfl

private theorem elaborateBareTail :
    forall characters cursor,
      elaborateTree (canonicalBareTail characters cursor) =
        .ok (.codepoints (characters.map Char.toNat))
  | [], _ => by rfl
  | character :: rest, cursor => by
      simp [canonicalBareTail, lexical, node, elaborateTree, elaborateTrees,
        elaborateNode_bareTailCons,
        elaborateLexical_bareChar character,
        elaborateBareTail rest (cursor + 1)]

private theorem elaborateVariableChars :
    forall characters cursor,
      elaborateTree (canonicalVariableChars characters cursor) =
        .ok (.codepoints (characters.map Char.toNat))
  | [], _ => by rfl
  | character :: rest, cursor => by
      simp [canonicalVariableChars, lexical, node, elaborateTree, elaborateTrees,
        elaborateNode_variableCharsCons,
        elaborateLexical_variableChar character,
        elaborateVariableChars rest (cursor + 1)]

private theorem elaborateCanonicalSymbol
    (value : String) (cursor : Nat)
    (safe : atomSafe (.symbol value) = true) :
    elaborateTree (canonicalOpenAtom (.symbol value) cursor) =
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
      simp [canonicalOpenAtom, characters, lexical, node, elaborateTree,
        elaborateTrees, elaborateNode_openBare,
        elaborateLexical_bareHead head,
        elaborateBareTail tail (cursor + 1)]
      simpa using decoded

private theorem elaborateCanonicalVariable
    (name : String) (cursor : Nat) :
    elaborateTree (canonicalOpenAtom (.var name) cursor) =
      .ok (.atom (.var name)) := by
  simp [canonicalOpenAtom, node, elaborateTree, elaborateTrees,
    elaborateNode_variable, elaborateNode_openVariable,
    elaborateVariableChars name.toList (cursor + 1)]
  simpa [stringScalars] using codepointsToString_stringScalars name

mutual
  private theorem elaborateCanonicalExpression
      (atoms : List Atom) (cursor : Nat)
      (safe : atomSafe (.expression atoms) = true) :
      elaborateTree (canonicalClosedAtom (.expression atoms) cursor) =
        .ok (.atom (.expression atoms)) := by
    simp only [atomSafe, Bool.and_eq_true] at safe
    simp [canonicalClosedAtom, node, elaborateTree, elaborateTrees,
      elaborateNode_expression, elaborateNode_closedExpression,
      elaborateCanonicalAtoms atoms (cursor + 1) safe.2]

  private theorem elaborateCanonicalAtoms
      (atoms : List Atom) (cursor : Nat) (safe : atomsSafe atoms = true) :
      elaborateTree (canonicalAtoms atoms cursor) = .ok (.atoms atoms) := by
    cases atoms with
    | nil => rfl
    | cons atom rest =>
        simp only [atomsSafe, Bool.and_eq_true] at safe
        cases atom with
        | symbol value =>
            cases rest with
            | nil =>
                rw [canonicalAtoms]
                simp [node, elaborateTree, elaborateTrees,
                  elaborateNode_atomsAfterOpenEnd, elaborateNode_atomsOpen,
                  elaborateCanonicalSymbol value cursor safe.1]
            | cons next tail =>
                have tailExact := elaborateCanonicalAtoms (next :: tail)
                  (cursor + (canonicalAtomScalars (.symbol value)).length + 1)
                  safe.2
                rw [canonicalAtoms]
                simp [lexical, node, elaborateTree, elaborateTrees,
                  elaborateNode_atomsAfterOpenWhitespace,
                  elaborateNode_atomsOpen, elaborateLexical_space, tailExact,
                  elaborateCanonicalSymbol value cursor safe.1]
        | var name =>
            cases rest with
            | nil =>
                rw [canonicalAtoms]
                simp [node, elaborateTree, elaborateTrees,
                  elaborateNode_atomsAfterOpenEnd, elaborateNode_atomsOpen,
                  elaborateCanonicalVariable name cursor]
            | cons next tail =>
                have tailExact := elaborateCanonicalAtoms (next :: tail)
                  (cursor + (canonicalAtomScalars (.var name)).length + 1)
                  safe.2
                rw [canonicalAtoms]
                simp [lexical, node, elaborateTree, elaborateTrees,
                  elaborateNode_atomsAfterOpenWhitespace,
                  elaborateNode_atomsOpen, elaborateLexical_space, tailExact,
                  elaborateCanonicalVariable name cursor]
        | grounded value => simp [atomSafe] at safe
        | expression children =>
            cases rest with
            | nil =>
                rw [canonicalAtoms]
                simp [node, elaborateTree, elaborateTrees,
                  elaborateNode_atomsEmpty, elaborateNode_atomsClosed,
                  elaborateCanonicalExpression children cursor safe.1]
            | cons next tail =>
                have tailExact := elaborateCanonicalAtoms (next :: tail)
                  (cursor +
                    (canonicalAtomScalars (.expression children)).length + 1)
                  safe.2
                rw [canonicalAtoms]
                simp [lexical, node, elaborateTree, elaborateTrees,
                  elaborateNode_atomsWhitespace, elaborateNode_atomsClosed,
                  elaborateLexical_space, tailExact,
                  elaborateCanonicalExpression children cursor safe.1]
end

private theorem programAtomsSafe (program : List Atom)
    (safe : programSafe program = true) : program.all atomSafe = true := by
  simp only [programSafe, Bool.and_eq_true] at safe
  exact safe.1

theorem atomsSafe_eq_all (atoms : List Atom) :
    atomsSafe atoms = atoms.all atomSafe := by
  induction atoms with
  | nil => rfl
  | cons atom rest induction =>
      simp [atomsSafe, induction]

private theorem elaborateCanonicalProgramTree :
    forall program cursor,
      program.all atomSafe = true ->
        elaborateTree (canonicalProgramCST program cursor) =
          .ok (.program program)
  | [], _, _ => by rfl
  | atom :: rest, cursor, safe => by
      simp only [List.all_cons, Bool.and_eq_true] at safe
      have tailExact := elaborateCanonicalProgramTree rest
        (cursor + (canonicalAtomScalars atom).length + 1) safe.2
      cases atom with
      | symbol value =>
          rw [canonicalProgramCST]
          simp [lexical, node, elaborateTree, elaborateTrees,
            elaborateNode_programAfterOpenWhitespace,
            elaborateNode_programOpen, elaborateLexical_lineFeed, tailExact,
            elaborateCanonicalSymbol value cursor safe.1]
      | var name =>
          rw [canonicalProgramCST]
          simp [lexical, node, elaborateTree, elaborateTrees,
            elaborateNode_programAfterOpenWhitespace,
            elaborateNode_programOpen, elaborateLexical_lineFeed, tailExact,
            elaborateCanonicalVariable name cursor]
      | grounded value => simp [atomSafe] at safe
      | expression atoms =>
          rw [canonicalProgramCST]
          simp [lexical, node, elaborateTree, elaborateTrees,
            elaborateNode_programWhitespace, elaborateNode_programClosed,
            elaborateLexical_lineFeed, tailExact,
            elaborateCanonicalExpression atoms cursor safe.1]

/-- Canonical lowering is exact for every program admitted by the compact
MM2 representation boundary. -/
theorem elaborateCanonicalProgram
    (program : List Atom) (cursor : Nat) (safe : programSafe program = true) :
    elaborateRootCST (canonicalProgramCST program cursor) =
      .program program := by
  have atomsSafe := programAtomsSafe program safe
  simp [elaborateRootCST, finishElaboration,
    elaborateCanonicalProgramTree program cursor atomsSafe,
    finishAttribute]

/-! ## Canonical derivations in the generated ParserPack -/

private theorem lexicalPositionValid
    (position : Nat) (within : position < 8) :
    position < parserPackPlan.lexical.productions.length := by
  rw [parser_pack_inventory.1]
  exact within

private theorem structuralPositionValid
    (position : Nat) (within : position < 35) :
    position < parserPackPlan.structural.length := by
  rw [parser_pack_inventory.2]
  exact within

private theorem lexicalSignatureAt
    (position : Nat) (within : position < 8)
    (expected : String × String × TerminalMatcher)
    (expectedAt : lexicalSignatures[position]? = some expected) :
    let valid := lexicalPositionValid position within
    let row := parserPackPlan.lexical.productions.get ⟨position, valid⟩
    row.resultSort = expected.1 ∧
      row.label = expected.2.1 ∧ row.matcher = expected.2.2 := by
  have signatures := congrArg (fun rows => rows[position]?)
    parser_pack_signatures_exact.1
  rw [expectedAt] at signatures
  simp only [List.getElem?_map, Option.map_eq_some_iff] at signatures
  rcases signatures with ⟨row, rowAt, fields⟩
  have valid := lexicalPositionValid position within
  rw [List.getElem?_eq_getElem valid] at rowAt
  have rowExact :
      parserPackPlan.lexical.productions.get ⟨position, valid⟩ = row :=
    Option.some.inj rowAt
  subst row
  exact ⟨congrArg (fun signature => signature.1) fields,
    congrArg (fun signature => signature.2.1) fields,
    congrArg (fun signature => signature.2.2) fields⟩

private theorem structuralSignatureAt
    (position : Nat) (within : position < 35)
    (expected : String × String × List PackItem)
    (expectedAt : structuralSignatures[position]? = some expected) :
    let valid := structuralPositionValid position within
    let row := parserPackPlan.structural.get ⟨position, valid⟩
    row.resultSort = expected.1 ∧
      row.label = expected.2.1 ∧ row.items = expected.2.2 := by
  have signatures := congrArg (fun rows => rows[position]?)
    parser_pack_signatures_exact.2
  rw [expectedAt] at signatures
  simp only [List.getElem?_map, Option.map_eq_some_iff] at signatures
  rcases signatures with ⟨row, rowAt, fields⟩
  have valid := structuralPositionValid position within
  rw [List.getElem?_eq_getElem valid] at rowAt
  have rowExact : parserPackPlan.structural.get ⟨position, valid⟩ = row :=
    Option.some.inj rowAt
  subst row
  exact ⟨congrArg (fun signature => signature.1) fields,
    congrArg (fun signature => signature.2.1) fields,
    congrArg (fun signature => signature.2.2) fields⟩

private def bareHeadDerivation
    (before after : List Nat) (character : Char)
    (safe : isBareSymbolHead character = true) :
    ParserPackDerivesAt mm2ParserProfile parserPackPlan
      (before ++ character.toNat :: after) "MM2BareHead"
      before.length (before.length + 1)
      (lexical "mm2:lex-bare-head" character before.length) := by
  have signature := lexicalSignatureAt 1 (by decide)
    ("MM2BareHead", "mm2:lex-bare-head",
      TerminalMatcher.class "MM2BareHeadClass") (by decide)
  refine ParserPackDerivesAt.lexical
    (matcher := .class "MM2BareHeadClass")
    (resultSort := "MM2BareHead") (ruleLabel := "mm2:lex-bare-head")
    (children := [.terminal [character.toNat]
      before.length (before.length + 1)])
    1 (lexicalPositionValid 1 (by decide)) signature.2.2
      signature.1 signature.2.1 ?_
  exact ⟨.classMember (codepoint := character.toNat) (by simp)
    ((isBareSymbolHead_eq_true_iff_class character).mp safe), rfl⟩

private def bareCharDerivation
    (before after : List Nat) (character : Char)
    (safe : isBareSymbolChar character = true) :
    ParserPackDerivesAt mm2ParserProfile parserPackPlan
      (before ++ character.toNat :: after) "MM2BareChar"
      before.length (before.length + 1)
      (lexical "mm2:lex-bare-char" character before.length) := by
  have signature := lexicalSignatureAt 2 (by decide)
    ("MM2BareChar", "mm2:lex-bare-char",
      TerminalMatcher.class "MM2BareCharClass") (by decide)
  refine ParserPackDerivesAt.lexical
    (matcher := .class "MM2BareCharClass")
    (resultSort := "MM2BareChar") (ruleLabel := "mm2:lex-bare-char")
    (children := [.terminal [character.toNat]
      before.length (before.length + 1)])
    2 (lexicalPositionValid 2 (by decide)) signature.2.2
      signature.1 signature.2.1 ?_
  exact ⟨.classMember (codepoint := character.toNat) (by simp)
    ((isBareSymbolChar_eq_true_iff_class character).mp safe), rfl⟩

private def variableCharDerivation
    (before after : List Nat) (character : Char)
    (safe : isVariableChar character = true) :
    ParserPackDerivesAt mm2ParserProfile parserPackPlan
      (before ++ character.toNat :: after) "MM2VariableChar"
      before.length (before.length + 1)
      (lexical "mm2:lex-variable-char" character before.length) := by
  have signature := lexicalSignatureAt 3 (by decide)
    ("MM2VariableChar", "mm2:lex-variable-char",
      TerminalMatcher.class "MM2VariableCharClass") (by decide)
  refine ParserPackDerivesAt.lexical
    (matcher := .class "MM2VariableCharClass")
    (resultSort := "MM2VariableChar")
    (ruleLabel := "mm2:lex-variable-char")
    (children := [.terminal [character.toNat]
      before.length (before.length + 1)])
    3 (lexicalPositionValid 3 (by decide)) signature.2.2
      signature.1 signature.2.1 ?_
  exact ⟨.classMember (codepoint := character.toNat) (by simp)
    ((isVariableChar_eq_true_iff_class character).mp safe), rfl⟩

private def whitespaceDerivation
    (before after : List Nat) (character : Char)
    (safe : isWhitespace character = true) :
    ParserPackDerivesAt mm2ParserProfile parserPackPlan
      (before ++ character.toNat :: after) "MM2Whitespace"
      before.length (before.length + 1)
      (lexical "mm2:lex-whitespace" character before.length) := by
  have signature := lexicalSignatureAt 0 (by decide)
    ("MM2Whitespace", "mm2:lex-whitespace",
      TerminalMatcher.class "MM2WhitespaceClass") (by decide)
  refine ParserPackDerivesAt.lexical
    (matcher := .class "MM2WhitespaceClass")
    (resultSort := "MM2Whitespace") (ruleLabel := "mm2:lex-whitespace")
    (children := [.terminal [character.toNat]
      before.length (before.length + 1)])
    0 (lexicalPositionValid 0 (by decide)) signature.2.2
      signature.1 signature.2.1 ?_
  exact ⟨.classMember (codepoint := character.toNat) (by simp)
    ((isWhitespace_eq_true_iff_class character).mp safe), rfl⟩

private def bareTailDerivation :
    forall (before after : List Nat) (characters : List Char),
      characters.all isBareSymbolChar = true ->
      ParserPackDerivesAt mm2ParserProfile parserPackPlan
        (before ++ characters.map Char.toNat ++ after) "MM2BareTail"
        before.length (before.length + characters.length)
        (canonicalBareTail characters before.length)
  | before, after, [], _ => by
      have signature := structuralSignatureAt 26 (by decide)
        ("MM2BareTail", "mm2:bare-tail-empty", []) (by decide)
      refine ParserPackDerivesAt.structural
        (resultSort := "MM2BareTail") (ruleLabel := "mm2:bare-tail-empty")
        26 (structuralPositionValid 26 (by decide)) signature.1
          signature.2.1 ?_
      rw [signature.2.2]
      exact .nil
  | before, after, character :: rest, safe => by
      simp only [List.all_cons, Bool.and_eq_true] at safe
      have head := bareCharDerivation before
        (rest.map Char.toNat ++ after) character safe.1
      have tail := bareTailDerivation
        (before ++ [character.toNat]) after rest safe.2
      have headExact :
          ParserPackDerivesAt mm2ParserProfile parserPackPlan
            (before ++ (character :: rest).map Char.toNat ++ after)
            "MM2BareChar" before.length (before.length + 1)
            (lexical "mm2:lex-bare-char" character before.length) := by
        simpa [List.append_assoc] using head
      have tailExact :
          ParserPackDerivesAt mm2ParserProfile parserPackPlan
            (before ++ (character :: rest).map Char.toNat ++ after)
            "MM2BareTail" (before.length + 1)
            (before.length + (character :: rest).length)
            (canonicalBareTail rest (before.length + 1)) := by
        simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using tail
      have signature := structuralSignatureAt 27 (by decide)
        ("MM2BareTail", "mm2:bare-tail-cons",
          [.nonterminal "MM2BareChar", .nonterminal "MM2BareTail"])
        (by decide)
      rw [canonicalBareTail]
      refine ParserPackDerivesAt.structural
        (resultSort := "MM2BareTail") (ruleLabel := "mm2:bare-tail-cons")
        27 (structuralPositionValid 27 (by decide)) signature.1
          signature.2.1 ?_
      rw [signature.2.2]
      exact .nonterminal headExact (.nonterminal tailExact .nil)

private def variableCharsDerivation :
    forall (before after : List Nat) (characters : List Char),
      characters.all isVariableChar = true ->
      ParserPackDerivesAt mm2ParserProfile parserPackPlan
        (before ++ characters.map Char.toNat ++ after) "MM2VariableChars"
        before.length (before.length + characters.length)
        (canonicalVariableChars characters before.length)
  | before, after, [], _ => by
      have signature := structuralSignatureAt 29 (by decide)
        ("MM2VariableChars", "mm2:variable-chars-empty", []) (by decide)
      refine ParserPackDerivesAt.structural
        (resultSort := "MM2VariableChars")
        (ruleLabel := "mm2:variable-chars-empty")
        29 (structuralPositionValid 29 (by decide)) signature.1
          signature.2.1 ?_
      rw [signature.2.2]
      exact .nil
  | before, after, character :: rest, safe => by
      simp only [List.all_cons, Bool.and_eq_true] at safe
      have head := variableCharDerivation before
        (rest.map Char.toNat ++ after) character safe.1
      have tail := variableCharsDerivation
        (before ++ [character.toNat]) after rest safe.2
      have headExact :
          ParserPackDerivesAt mm2ParserProfile parserPackPlan
            (before ++ (character :: rest).map Char.toNat ++ after)
            "MM2VariableChar" before.length (before.length + 1)
            (lexical "mm2:lex-variable-char" character before.length) := by
        simpa [List.append_assoc] using head
      have tailExact :
          ParserPackDerivesAt mm2ParserProfile parserPackPlan
            (before ++ (character :: rest).map Char.toNat ++ after)
            "MM2VariableChars" (before.length + 1)
            (before.length + (character :: rest).length)
            (canonicalVariableChars rest (before.length + 1)) := by
        simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using tail
      have signature := structuralSignatureAt 30 (by decide)
        ("MM2VariableChars", "mm2:variable-chars-cons",
          [.nonterminal "MM2VariableChar",
           .nonterminal "MM2VariableChars"]) (by decide)
      rw [canonicalVariableChars]
      refine ParserPackDerivesAt.structural
        (resultSort := "MM2VariableChars")
        (ruleLabel := "mm2:variable-chars-cons")
        30 (structuralPositionValid 30 (by decide)) signature.1
          signature.2.1 ?_
      rw [signature.2.2]
      exact .nonterminal headExact (.nonterminal tailExact .nil)

private def charMatch (before after : List Nat) (codepoint : Nat) :
    TerminalMatchesAt mm2ParserProfile (before ++ codepoint :: after)
      (.char codepoint) before.length (before.length + 1) :=
  .char (codepoint := codepoint) (by simp)

private def symbolDerivation
    (before after : List Nat) (value : String)
    (safe : atomSafe (.symbol value) = true) :
    ParserPackDerivesAt mm2ParserProfile parserPackPlan
      (before ++ canonicalAtomScalars (.symbol value) ++ after)
      "MM2OpenAtom" before.length
      (before.length + (canonicalAtomScalars (.symbol value)).length)
      (canonicalOpenAtom (.symbol value) before.length) := by
  simp only [atomSafe] at safe
  cases characters : value.toList with
  | nil => simp [bareSymbolSafe, characters] at safe
  | cons head tail =>
      simp only [bareSymbolSafe, characters, Bool.and_eq_true] at safe
      have headDerivation := bareHeadDerivation before
        (tail.map Char.toNat ++ after) head safe.1.2
      have tailDerivation := bareTailDerivation
        (before ++ [head.toNat]) after tail safe.2
      have headExact :
          ParserPackDerivesAt mm2ParserProfile parserPackPlan
            (before ++ (head :: tail).map Char.toNat ++ after)
            "MM2BareHead" before.length (before.length + 1)
            (lexical "mm2:lex-bare-head" head before.length) := by
        simpa [List.append_assoc] using headDerivation
      have tailExact :
          ParserPackDerivesAt mm2ParserProfile parserPackPlan
            (before ++ (head :: tail).map Char.toNat ++ after)
            "MM2BareTail" (before.length + 1)
            (before.length + (head :: tail).length)
            (canonicalBareTail tail (before.length + 1)) := by
        simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using tailDerivation
      have signature := structuralSignatureAt 20 (by decide)
        ("MM2OpenAtom", "mm2:open-atom-bare",
          [.nonterminal "MM2BareHead", .nonterminal "MM2BareTail"])
        (by decide)
      have result :
          ParserPackDerivesAt mm2ParserProfile parserPackPlan
            (before ++ (head :: tail).map Char.toNat ++ after)
            "MM2OpenAtom" before.length
            (before.length + (head :: tail).length)
            (node "mm2:open-atom-bare" before.length
              (before.length + (head :: tail).length)
              [lexical "mm2:lex-bare-head" head before.length,
               canonicalBareTail tail (before.length + 1)]) := by
        refine ParserPackDerivesAt.structural
          (resultSort := "MM2OpenAtom")
          (ruleLabel := "mm2:open-atom-bare")
          20 (structuralPositionValid 20 (by decide)) signature.1
            signature.2.1 ?_
        rw [signature.2.2]
        exact .nonterminal headExact (.nonterminal tailExact .nil)
      simpa [canonicalAtomScalars, stringScalars, characters,
        canonicalOpenAtom] using result

private def variableDerivation
    (before after : List Nat) (name : String)
    (safe : atomSafe (.var name) = true) :
    ParserPackDerivesAt mm2ParserProfile parserPackPlan
      (before ++ canonicalAtomScalars (.var name) ++ after)
      "MM2OpenAtom" before.length
      (before.length + (canonicalAtomScalars (.var name)).length)
      (canonicalOpenAtom (.var name) before.length) := by
  simp only [atomSafe, variableNameSafe] at safe
  let characters := name.toList
  have charactersDerivation := variableCharsDerivation
    (before ++ [36]) after characters safe
  have charactersExact :
      ParserPackDerivesAt mm2ParserProfile parserPackPlan
        (before ++ (36 :: characters.map Char.toNat) ++ after)
        "MM2VariableChars" (before.length + 1)
        (before.length + 1 + characters.length)
        (canonicalVariableChars characters (before.length + 1)) := by
    simpa [List.append_assoc] using charactersDerivation
  have dollarExact :
      TerminalMatchesAt mm2ParserProfile
        (before ++ (36 :: characters.map Char.toNat) ++ after)
        (.char 36) before.length (before.length + 1) := by
    simpa [List.append_assoc] using
      charMatch before (characters.map Char.toNat ++ after) 36
  have variableSignature := structuralSignatureAt 28 (by decide)
    ("MM2Variable", "mm2:variable",
      [.terminal (.char 36), .nonterminal "MM2VariableChars"])
    (by decide)
  have variableExact :
      ParserPackDerivesAt mm2ParserProfile parserPackPlan
        (before ++ (36 :: characters.map Char.toNat) ++ after)
        "MM2Variable" before.length
        (before.length + 1 + characters.length)
        (node "mm2:variable" before.length
          (before.length + 1 + characters.length)
          [canonicalVariableChars characters (before.length + 1)]) := by
    refine ParserPackDerivesAt.structural
      (resultSort := "MM2Variable") (ruleLabel := "mm2:variable")
      28 (structuralPositionValid 28 (by decide)) variableSignature.1
        variableSignature.2.1 ?_
    rw [variableSignature.2.2]
    exact .terminal dollarExact (.nonterminal charactersExact .nil)
  have openSignature := structuralSignatureAt 21 (by decide)
    ("MM2OpenAtom", "mm2:open-atom-variable",
      [.nonterminal "MM2Variable"]) (by decide)
  have result :
      ParserPackDerivesAt mm2ParserProfile parserPackPlan
        (before ++ (36 :: characters.map Char.toNat) ++ after)
        "MM2OpenAtom" before.length
        (before.length + 1 + characters.length)
        (node "mm2:open-atom-variable" before.length
          (before.length + 1 + characters.length)
          [node "mm2:variable" before.length
            (before.length + 1 + characters.length)
            [canonicalVariableChars characters (before.length + 1)]]) := by
    refine ParserPackDerivesAt.structural
      (resultSort := "MM2OpenAtom")
      (ruleLabel := "mm2:open-atom-variable")
      21 (structuralPositionValid 21 (by decide)) openSignature.1
        openSignature.2.1 ?_
    rw [openSignature.2.2]
    exact .nonterminal variableExact .nil
  simpa [characters, canonicalAtomScalars, stringScalars,
    canonicalOpenAtom, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using result

private def canonicalAtomSort : Atom -> String
  | .expression _ => "MM2ClosedAtom"
  | _ => "MM2OpenAtom"

private def canonicalClassifiedAtom : Atom -> Nat -> CST
  | .expression children, cursor =>
      canonicalClosedAtom (.expression children) cursor
  | atom, cursor => canonicalOpenAtom atom cursor

private def emptyAtomsDerivation (input : List Nat) (cursor : Nat) :
    ParserPackDerivesAt mm2ParserProfile parserPackPlan input "MM2Atoms"
      cursor cursor (node "mm2:atoms-empty" cursor cursor) := by
  have signature := structuralSignatureAt 10 (by decide)
    ("MM2Atoms", "mm2:atoms-empty", []) (by decide)
  refine ParserPackDerivesAt.structural
    (resultSort := "MM2Atoms") (ruleLabel := "mm2:atoms-empty")
    10 (structuralPositionValid 10 (by decide)) signature.1
      signature.2.1 ?_
  rw [signature.2.2]
  exact .nil

private def emptyAtomsAfterOpenDerivation (input : List Nat) (cursor : Nat) :
    ParserPackDerivesAt mm2ParserProfile parserPackPlan input
      "MM2AtomsAfterOpen" cursor cursor
      (node "mm2:atoms-after-open-end" cursor cursor) := by
  have signature := structuralSignatureAt 15 (by decide)
    ("MM2AtomsAfterOpen", "mm2:atoms-after-open-end", []) (by decide)
  refine ParserPackDerivesAt.structural
    (resultSort := "MM2AtomsAfterOpen")
    (ruleLabel := "mm2:atoms-after-open-end")
    15 (structuralPositionValid 15 (by decide)) signature.1
      signature.2.1 ?_
  rw [signature.2.2]
  exact .nil

mutual
  private def canonicalAtomDerivation
      (before after : List Nat) (atom : Atom)
      (safe : atomSafe atom = true) :
      ParserPackDerivesAt mm2ParserProfile parserPackPlan
        (before ++ canonicalAtomScalars atom ++ after)
        (canonicalAtomSort atom) before.length
        (before.length + (canonicalAtomScalars atom).length)
        (canonicalClassifiedAtom atom before.length) := by
    cases atom with
    | symbol value =>
        simpa [canonicalAtomSort, canonicalClassifiedAtom] using
          symbolDerivation before after value safe
    | var name =>
        simpa [canonicalAtomSort, canonicalClassifiedAtom] using
          variableDerivation before after name safe
    | grounded value => simp [atomSafe] at safe
    | expression children =>
        simp only [atomSafe, Bool.and_eq_true] at safe
        let body := canonicalAtomsScalars children
        have leftExact :
            TerminalMatchesAt mm2ParserProfile
              (before ++ (40 :: body ++ 41 :: after)) (.char 40)
              before.length (before.length + 1) := by
          simpa [List.append_assoc] using
            charMatch before (body ++ 41 :: after) 40
        have childrenDerivation := canonicalAtomsDerivation
          (before ++ [40]) (41 :: after) children safe.2
        have childrenExact :
            ParserPackDerivesAt mm2ParserProfile parserPackPlan
              (before ++ (40 :: body ++ 41 :: after)) "MM2Atoms"
              (before.length + 1) (before.length + 1 + body.length)
              (canonicalAtoms children (before.length + 1)) := by
          simpa [body, List.append_assoc] using childrenDerivation
        have rightExact :
            TerminalMatchesAt mm2ParserProfile
              (before ++ (40 :: body ++ 41 :: after)) (.char 41)
              (before.length + 1 + body.length)
              (before.length + body.length + 2) := by
          have right := charMatch (before ++ [40] ++ body) after 41
          convert right using 1 <;> simp [List.append_assoc] <;> omega
        have expressionSignature := structuralSignatureAt 9 (by decide)
          ("MM2Expression", "mm2:expression",
            [.terminal (.char 40), .nonterminal "MM2Atoms",
             .terminal (.char 41)]) (by decide)
        have expressionExact :
            ParserPackDerivesAt mm2ParserProfile parserPackPlan
              (before ++ (40 :: body ++ 41 :: after)) "MM2Expression"
              before.length (before.length + body.length + 2)
              (node "mm2:expression" before.length
                (before.length + body.length + 2)
                [canonicalAtoms children (before.length + 1)]) := by
          refine ParserPackDerivesAt.structural
            (resultSort := "MM2Expression") (ruleLabel := "mm2:expression")
            9 (structuralPositionValid 9 (by decide)) expressionSignature.1
              expressionSignature.2.1 ?_
          rw [expressionSignature.2.2]
          exact .terminal leftExact
            (.nonterminal childrenExact (.terminal rightExact .nil))
        have closedSignature := structuralSignatureAt 19 (by decide)
          ("MM2ClosedAtom", "mm2:closed-atom-expression",
            [.nonterminal "MM2Expression"]) (by decide)
        have result :
            ParserPackDerivesAt mm2ParserProfile parserPackPlan
              (before ++ (40 :: body ++ 41 :: after)) "MM2ClosedAtom"
              before.length (before.length + body.length + 2)
              (node "mm2:closed-atom-expression" before.length
                (before.length + body.length + 2)
                [node "mm2:expression" before.length
                  (before.length + body.length + 2)
                  [canonicalAtoms children (before.length + 1)]]) := by
          refine ParserPackDerivesAt.structural
            (resultSort := "MM2ClosedAtom")
            (ruleLabel := "mm2:closed-atom-expression")
            19 (structuralPositionValid 19 (by decide)) closedSignature.1
              closedSignature.2.1 ?_
          rw [closedSignature.2.2]
          exact .nonterminal expressionExact .nil
        convert result using 1 <;>
          simp [body, canonicalAtomScalars, canonicalAtomSort,
            canonicalClassifiedAtom, canonicalClosedAtom,
            List.append_assoc]
        all_goals omega

  private def canonicalAtomsDerivation
      (before after : List Nat) (atoms : List Atom)
      (safe : atomsSafe atoms = true) :
      ParserPackDerivesAt mm2ParserProfile parserPackPlan
        (before ++ canonicalAtomsScalars atoms ++ after) "MM2Atoms"
        before.length (before.length + (canonicalAtomsScalars atoms).length)
        (canonicalAtoms atoms before.length) := by
    cases atoms with
    | nil =>
        simpa [canonicalAtomsScalars, canonicalAtoms] using
          emptyAtomsDerivation (before ++ after) before.length
    | cons atom rest =>
        simp only [atomsSafe, Bool.and_eq_true] at safe
        cases rest with
        | nil =>
            let atomScalars := canonicalAtomScalars atom
            have atomExact := canonicalAtomDerivation before after atom safe.1
            cases atom with
            | grounded value => simp [atomSafe] at safe
            | expression children =>
                have tailExact := emptyAtomsDerivation
                  (before ++ atomScalars ++ after)
                  (before.length + atomScalars.length)
                have signature := structuralSignatureAt 13 (by decide)
                  ("MM2Atoms", "mm2:atoms-closed",
                    [.nonterminal "MM2ClosedAtom",
                     .nonterminal "MM2Atoms"]) (by decide)
                rw [canonicalAtomsScalars, canonicalAtoms]
                simp only [canonicalAtomsScalars, List.append_nil]
                dsimp [atomScalars] at atomExact tailExact
                refine ParserPackDerivesAt.structural
                  (resultSort := "MM2Atoms")
                  (ruleLabel := "mm2:atoms-closed")
                  13 (structuralPositionValid 13 (by decide)) signature.1
                    signature.2.1 ?_
                rw [signature.2.2]
                have body := ParserPackItemsDeriveAt.nonterminal atomExact
                  (ParserPackItemsDeriveAt.nonterminal tailExact
                    ParserPackItemsDeriveAt.nil)
                simpa [canonicalAtomsScalars, canonicalAtomSort,
                  canonicalClassifiedAtom, List.append_assoc] using body
            | symbol value =>
                have tailExact := emptyAtomsAfterOpenDerivation
                  (before ++ atomScalars ++ after)
                  (before.length + atomScalars.length)
                have signature := structuralSignatureAt 14 (by decide)
                  ("MM2Atoms", "mm2:atoms-open",
                    [.nonterminal "MM2OpenAtom",
                     .nonterminal "MM2AtomsAfterOpen"]) (by decide)
                rw [canonicalAtomsScalars, canonicalAtoms]
                simp only [canonicalAtomsScalars, List.append_nil]
                dsimp [atomScalars] at atomExact tailExact
                refine ParserPackDerivesAt.structural
                  (resultSort := "MM2Atoms") (ruleLabel := "mm2:atoms-open")
                  14 (structuralPositionValid 14 (by decide)) signature.1
                    signature.2.1 ?_
                rw [signature.2.2]
                have body := ParserPackItemsDeriveAt.nonterminal atomExact
                  (ParserPackItemsDeriveAt.nonterminal tailExact
                    ParserPackItemsDeriveAt.nil)
                simpa [canonicalAtomsScalars, canonicalAtomSort,
                  canonicalClassifiedAtom, List.append_assoc] using body
            | var name =>
                have tailExact := emptyAtomsAfterOpenDerivation
                  (before ++ atomScalars ++ after)
                  (before.length + atomScalars.length)
                have signature := structuralSignatureAt 14 (by decide)
                  ("MM2Atoms", "mm2:atoms-open",
                    [.nonterminal "MM2OpenAtom",
                     .nonterminal "MM2AtomsAfterOpen"]) (by decide)
                rw [canonicalAtomsScalars, canonicalAtoms]
                simp only [canonicalAtomsScalars, List.append_nil]
                dsimp [atomScalars] at atomExact tailExact
                refine ParserPackDerivesAt.structural
                  (resultSort := "MM2Atoms") (ruleLabel := "mm2:atoms-open")
                  14 (structuralPositionValid 14 (by decide)) signature.1
                    signature.2.1 ?_
                rw [signature.2.2]
                have body := ParserPackItemsDeriveAt.nonterminal atomExact
                  (ParserPackItemsDeriveAt.nonterminal tailExact
                    ParserPackItemsDeriveAt.nil)
                simpa [canonicalAtomsScalars, canonicalAtomSort,
                  canonicalClassifiedAtom, List.append_assoc] using body
        | cons next tail =>
            let atomScalars := canonicalAtomScalars atom
            let restScalars := canonicalAtomsScalars (next :: tail)
            have atomExact := canonicalAtomDerivation before
              (32 :: restScalars ++ after) atom safe.1
            have spaceExact := whitespaceDerivation (before ++ atomScalars)
              (restScalars ++ after) ' ' (by decide)
            have restExact := canonicalAtomsDerivation
              (before ++ atomScalars ++ [32]) after (next :: tail) safe.2
            have atomForBody :
                ParserPackDerivesAt mm2ParserProfile parserPackPlan
                  (before ++ atomScalars ++ 32 :: restScalars ++ after)
                  (canonicalAtomSort atom) before.length
                  (before.length + atomScalars.length)
                  (canonicalClassifiedAtom atom before.length) := by
              simpa [atomScalars, restScalars, List.append_assoc] using
                atomExact
            have spaceForBody :
                ParserPackDerivesAt mm2ParserProfile parserPackPlan
                  (before ++ atomScalars ++ 32 :: restScalars ++ after)
                  "MM2Whitespace" (before.length + atomScalars.length)
                  (before.length + atomScalars.length + 1)
                  (lexical "mm2:lex-whitespace" ' '
                    (before.length + atomScalars.length)) := by
              simpa [atomScalars, restScalars, List.append_assoc] using
                spaceExact
            have restForBody :
                ParserPackDerivesAt mm2ParserProfile parserPackPlan
                  (before ++ atomScalars ++ 32 :: restScalars ++ after)
                  "MM2Atoms" (before.length + atomScalars.length + 1)
                  (before.length + atomScalars.length + 1 +
                    restScalars.length)
                  (canonicalAtoms (next :: tail)
                    (before.length + atomScalars.length + 1)) := by
              simpa [atomScalars, restScalars, List.append_assoc,
                Nat.add_assoc] using restExact
            cases atom with
            | grounded value => simp [atomSafe] at safe
            | expression children =>
                have tailSignature := structuralSignatureAt 11 (by decide)
                  ("MM2Atoms", "mm2:atoms-whitespace",
                    [.nonterminal "MM2Whitespace",
                     .nonterminal "MM2Atoms"]) (by decide)
                have tailExact :
                    ParserPackDerivesAt mm2ParserProfile parserPackPlan
                      (before ++ atomScalars ++ 32 :: restScalars ++ after)
                      "MM2Atoms" (before.length + atomScalars.length)
                      (before.length + atomScalars.length + 1 +
                        restScalars.length)
                      (node "mm2:atoms-whitespace"
                        (before.length + atomScalars.length)
                        (before.length + atomScalars.length + 1 +
                          restScalars.length)
                        [lexical "mm2:lex-whitespace" ' '
                          (before.length + atomScalars.length),
                         canonicalAtoms (next :: tail)
                          (before.length + atomScalars.length + 1)]) := by
                  refine ParserPackDerivesAt.structural
                    (resultSort := "MM2Atoms")
                    (ruleLabel := "mm2:atoms-whitespace")
                    11 (structuralPositionValid 11 (by decide))
                      tailSignature.1 tailSignature.2.1 ?_
                  rw [tailSignature.2.2]
                  exact .nonterminal spaceForBody
                    (.nonterminal restForBody .nil)
                have signature := structuralSignatureAt 13 (by decide)
                  ("MM2Atoms", "mm2:atoms-closed",
                    [.nonterminal "MM2ClosedAtom",
                     .nonterminal "MM2Atoms"]) (by decide)
                rw [canonicalAtomsScalars, canonicalAtoms]
                dsimp [atomScalars, restScalars] at atomForBody tailExact
                refine ParserPackDerivesAt.structural
                  (resultSort := "MM2Atoms")
                  (ruleLabel := "mm2:atoms-closed")
                  13 (structuralPositionValid 13 (by decide)) signature.1
                    signature.2.1 ?_
                rw [signature.2.2]
                have body := ParserPackItemsDeriveAt.nonterminal atomForBody
                  (ParserPackItemsDeriveAt.nonterminal tailExact
                    ParserPackItemsDeriveAt.nil)
                simpa [canonicalAtomSort, canonicalClassifiedAtom,
                  List.append_assoc, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using body
            | symbol value =>
                have tailSignature := structuralSignatureAt 16 (by decide)
                  ("MM2AtomsAfterOpen", "mm2:atoms-after-open-whitespace",
                    [.nonterminal "MM2Whitespace",
                     .nonterminal "MM2Atoms"]) (by decide)
                have tailExact :
                    ParserPackDerivesAt mm2ParserProfile parserPackPlan
                      (before ++ atomScalars ++ 32 :: restScalars ++ after)
                      "MM2AtomsAfterOpen"
                      (before.length + atomScalars.length)
                      (before.length + atomScalars.length + 1 +
                        restScalars.length)
                      (node "mm2:atoms-after-open-whitespace"
                        (before.length + atomScalars.length)
                        (before.length + atomScalars.length + 1 +
                          restScalars.length)
                        [lexical "mm2:lex-whitespace" ' '
                          (before.length + atomScalars.length),
                         canonicalAtoms (next :: tail)
                          (before.length + atomScalars.length + 1)]) := by
                  refine ParserPackDerivesAt.structural
                    (resultSort := "MM2AtomsAfterOpen")
                    (ruleLabel := "mm2:atoms-after-open-whitespace")
                    16 (structuralPositionValid 16 (by decide))
                      tailSignature.1 tailSignature.2.1 ?_
                  rw [tailSignature.2.2]
                  exact .nonterminal spaceForBody
                    (.nonterminal restForBody .nil)
                have signature := structuralSignatureAt 14 (by decide)
                  ("MM2Atoms", "mm2:atoms-open",
                    [.nonterminal "MM2OpenAtom",
                     .nonterminal "MM2AtomsAfterOpen"]) (by decide)
                rw [canonicalAtomsScalars, canonicalAtoms]
                dsimp [atomScalars, restScalars] at atomForBody tailExact
                refine ParserPackDerivesAt.structural
                  (resultSort := "MM2Atoms") (ruleLabel := "mm2:atoms-open")
                  14 (structuralPositionValid 14 (by decide)) signature.1
                    signature.2.1 ?_
                rw [signature.2.2]
                have body := ParserPackItemsDeriveAt.nonterminal atomForBody
                  (ParserPackItemsDeriveAt.nonterminal tailExact
                    ParserPackItemsDeriveAt.nil)
                simpa [canonicalAtomSort, canonicalClassifiedAtom,
                  List.append_assoc, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using body
            | var name =>
                have tailSignature := structuralSignatureAt 16 (by decide)
                  ("MM2AtomsAfterOpen", "mm2:atoms-after-open-whitespace",
                    [.nonterminal "MM2Whitespace",
                     .nonterminal "MM2Atoms"]) (by decide)
                have tailExact :
                    ParserPackDerivesAt mm2ParserProfile parserPackPlan
                      (before ++ atomScalars ++ 32 :: restScalars ++ after)
                      "MM2AtomsAfterOpen"
                      (before.length + atomScalars.length)
                      (before.length + atomScalars.length + 1 +
                        restScalars.length)
                      (node "mm2:atoms-after-open-whitespace"
                        (before.length + atomScalars.length)
                        (before.length + atomScalars.length + 1 +
                          restScalars.length)
                        [lexical "mm2:lex-whitespace" ' '
                          (before.length + atomScalars.length),
                         canonicalAtoms (next :: tail)
                          (before.length + atomScalars.length + 1)]) := by
                  refine ParserPackDerivesAt.structural
                    (resultSort := "MM2AtomsAfterOpen")
                    (ruleLabel := "mm2:atoms-after-open-whitespace")
                    16 (structuralPositionValid 16 (by decide))
                      tailSignature.1 tailSignature.2.1 ?_
                  rw [tailSignature.2.2]
                  exact .nonterminal spaceForBody
                    (.nonterminal restForBody .nil)
                have signature := structuralSignatureAt 14 (by decide)
                  ("MM2Atoms", "mm2:atoms-open",
                    [.nonterminal "MM2OpenAtom",
                     .nonterminal "MM2AtomsAfterOpen"]) (by decide)
                rw [canonicalAtomsScalars, canonicalAtoms]
                dsimp [atomScalars, restScalars] at atomForBody tailExact
                refine ParserPackDerivesAt.structural
                  (resultSort := "MM2Atoms") (ruleLabel := "mm2:atoms-open")
                  14 (structuralPositionValid 14 (by decide)) signature.1
                    signature.2.1 ?_
                rw [signature.2.2]
                have body := ParserPackItemsDeriveAt.nonterminal atomForBody
                  (ParserPackItemsDeriveAt.nonterminal tailExact
                    ParserPackItemsDeriveAt.nil)
                simpa [canonicalAtomSort, canonicalClassifiedAtom,
                  List.append_assoc, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using body
end

private def canonicalProgramDerivation :
    forall (before : List Nat) (program : List Atom),
      program.all atomSafe = true ->
      ParserPackDerivesAt mm2ParserProfile parserPackPlan
        (before ++ canonicalProgramScalars program) "MM2Program"
        before.length
        (before.length + (canonicalProgramScalars program).length)
        (canonicalProgramCST program before.length)
  | before, [], _ => by
      have signature := structuralSignatureAt 0 (by decide)
        ("MM2Program", "mm2:program-empty", []) (by decide)
      rw [canonicalProgramScalars, canonicalProgramCST]
      refine ParserPackDerivesAt.structural
        (resultSort := "MM2Program") (ruleLabel := "mm2:program-empty")
        0 (structuralPositionValid 0 (by decide)) signature.1
          signature.2.1 ?_
      rw [signature.2.2]
      exact .nil
  | before, atom :: rest, safe => by
      simp only [List.all_cons, Bool.and_eq_true] at safe
      let atomScalars := canonicalAtomScalars atom
      let restScalars := canonicalProgramScalars rest
      have atomDerivation := canonicalAtomDerivation before
        (10 :: restScalars) atom safe.1
      have lineFeedDerivation := whitespaceDerivation
        (before ++ atomScalars) restScalars '\n' (by decide)
      have restDerivation := canonicalProgramDerivation
        (before ++ atomScalars ++ [10]) rest safe.2
      have atomExact :
          ParserPackDerivesAt mm2ParserProfile parserPackPlan
            (before ++ atomScalars ++ 10 :: restScalars)
            (canonicalAtomSort atom) before.length
            (before.length + atomScalars.length)
            (canonicalClassifiedAtom atom before.length) := by
        simpa [atomScalars, restScalars, List.append_assoc] using
          atomDerivation
      have lineFeedExact :
          ParserPackDerivesAt mm2ParserProfile parserPackPlan
            (before ++ atomScalars ++ 10 :: restScalars)
            "MM2Whitespace" (before.length + atomScalars.length)
            (before.length + atomScalars.length + 1)
            (lexical "mm2:lex-whitespace" '\n'
              (before.length + atomScalars.length)) := by
        simpa [atomScalars, restScalars, List.append_assoc] using
          lineFeedDerivation
      have restExact :
          ParserPackDerivesAt mm2ParserProfile parserPackPlan
            (before ++ atomScalars ++ 10 :: restScalars)
            "MM2Program" (before.length + atomScalars.length + 1)
            (before.length + atomScalars.length + 1 + restScalars.length)
            (canonicalProgramCST rest
              (before.length + atomScalars.length + 1)) := by
        simpa [atomScalars, restScalars, List.append_assoc,
          Nat.add_assoc] using restDerivation
      cases atom with
      | grounded value => simp [atomSafe] at safe
      | expression children =>
          have whitespaceSignature := structuralSignatureAt 1 (by decide)
            ("MM2Program", "mm2:program-whitespace",
              [.nonterminal "MM2Whitespace", .nonterminal "MM2Program"])
            (by decide)
          have tailExact :
              ParserPackDerivesAt mm2ParserProfile parserPackPlan
                (before ++ atomScalars ++ 10 :: restScalars)
                "MM2Program" (before.length + atomScalars.length)
                (before.length + atomScalars.length + 1 +
                  restScalars.length)
                (node "mm2:program-whitespace"
                  (before.length + atomScalars.length)
                  (before.length + atomScalars.length + 1 +
                    restScalars.length)
                  [lexical "mm2:lex-whitespace" '\n'
                    (before.length + atomScalars.length),
                   canonicalProgramCST rest
                    (before.length + atomScalars.length + 1)]) := by
            refine ParserPackDerivesAt.structural
              (resultSort := "MM2Program")
              (ruleLabel := "mm2:program-whitespace")
              1 (structuralPositionValid 1 (by decide))
                whitespaceSignature.1 whitespaceSignature.2.1 ?_
            rw [whitespaceSignature.2.2]
            exact .nonterminal lineFeedExact
              (.nonterminal restExact .nil)
          have signature := structuralSignatureAt 4 (by decide)
            ("MM2Program", "mm2:program-closed",
              [.nonterminal "MM2ClosedAtom", .nonterminal "MM2Program"])
            (by decide)
          rw [canonicalProgramScalars, canonicalProgramCST]
          dsimp [atomScalars, restScalars] at atomExact tailExact
          refine ParserPackDerivesAt.structural
            (resultSort := "MM2Program") (ruleLabel := "mm2:program-closed")
            4 (structuralPositionValid 4 (by decide)) signature.1
              signature.2.1 ?_
          rw [signature.2.2]
          have body := ParserPackItemsDeriveAt.nonterminal atomExact
            (ParserPackItemsDeriveAt.nonterminal tailExact
              ParserPackItemsDeriveAt.nil)
          simpa [canonicalAtomSort, canonicalClassifiedAtom,
            canonicalProgramScalars, List.append_assoc,
            Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using body
      | symbol value =>
          have tailSignature := structuralSignatureAt 7 (by decide)
            ("MM2ProgramAfterOpen", "mm2:program-after-open-whitespace",
              [.nonterminal "MM2Whitespace",
               .nonterminal "MM2Program"]) (by decide)
          have tailExact :
              ParserPackDerivesAt mm2ParserProfile parserPackPlan
                (before ++ atomScalars ++ 10 :: restScalars)
                "MM2ProgramAfterOpen"
                (before.length + atomScalars.length)
                (before.length + atomScalars.length + 1 +
                  restScalars.length)
                (node "mm2:program-after-open-whitespace"
                  (before.length + atomScalars.length)
                  (before.length + atomScalars.length + 1 +
                    restScalars.length)
                  [lexical "mm2:lex-whitespace" '\n'
                    (before.length + atomScalars.length),
                   canonicalProgramCST rest
                    (before.length + atomScalars.length + 1)]) := by
            refine ParserPackDerivesAt.structural
              (resultSort := "MM2ProgramAfterOpen")
              (ruleLabel := "mm2:program-after-open-whitespace")
              7 (structuralPositionValid 7 (by decide)) tailSignature.1
                tailSignature.2.1 ?_
            rw [tailSignature.2.2]
            exact .nonterminal lineFeedExact (.nonterminal restExact .nil)
          have signature := structuralSignatureAt 5 (by decide)
            ("MM2Program", "mm2:program-open",
              [.nonterminal "MM2OpenAtom",
               .nonterminal "MM2ProgramAfterOpen"])
            (by decide)
          rw [canonicalProgramScalars, canonicalProgramCST]
          dsimp [atomScalars, restScalars] at atomExact tailExact
          refine ParserPackDerivesAt.structural
            (resultSort := "MM2Program") (ruleLabel := "mm2:program-open")
            5 (structuralPositionValid 5 (by decide)) signature.1
              signature.2.1 ?_
          rw [signature.2.2]
          have body := ParserPackItemsDeriveAt.nonterminal atomExact
            (ParserPackItemsDeriveAt.nonterminal tailExact
              ParserPackItemsDeriveAt.nil)
          simpa [canonicalAtomSort, canonicalClassifiedAtom,
            canonicalProgramScalars, List.append_assoc,
            Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using body
      | var name =>
          have tailSignature := structuralSignatureAt 7 (by decide)
            ("MM2ProgramAfterOpen", "mm2:program-after-open-whitespace",
              [.nonterminal "MM2Whitespace",
               .nonterminal "MM2Program"]) (by decide)
          have tailExact :
              ParserPackDerivesAt mm2ParserProfile parserPackPlan
                (before ++ atomScalars ++ 10 :: restScalars)
                "MM2ProgramAfterOpen"
                (before.length + atomScalars.length)
                (before.length + atomScalars.length + 1 +
                  restScalars.length)
                (node "mm2:program-after-open-whitespace"
                  (before.length + atomScalars.length)
                  (before.length + atomScalars.length + 1 +
                    restScalars.length)
                  [lexical "mm2:lex-whitespace" '\n'
                    (before.length + atomScalars.length),
                   canonicalProgramCST rest
                    (before.length + atomScalars.length + 1)]) := by
            refine ParserPackDerivesAt.structural
              (resultSort := "MM2ProgramAfterOpen")
              (ruleLabel := "mm2:program-after-open-whitespace")
              7 (structuralPositionValid 7 (by decide)) tailSignature.1
                tailSignature.2.1 ?_
            rw [tailSignature.2.2]
            exact .nonterminal lineFeedExact (.nonterminal restExact .nil)
          have signature := structuralSignatureAt 5 (by decide)
            ("MM2Program", "mm2:program-open",
              [.nonterminal "MM2OpenAtom",
               .nonterminal "MM2ProgramAfterOpen"])
            (by decide)
          rw [canonicalProgramScalars, canonicalProgramCST]
          dsimp [atomScalars, restScalars] at atomExact tailExact
          refine ParserPackDerivesAt.structural
            (resultSort := "MM2Program") (ruleLabel := "mm2:program-open")
            5 (structuralPositionValid 5 (by decide)) signature.1
              signature.2.1 ?_
          rw [signature.2.2]
          have body := ParserPackItemsDeriveAt.nonterminal atomExact
            (ParserPackItemsDeriveAt.nonterminal tailExact
              ParserPackItemsDeriveAt.nil)
          simpa [canonicalAtomSort, canonicalClassifiedAtom,
            canonicalProgramScalars, List.append_assoc,
            Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using body

/-- Every canonically rendered ordinary MM2 program has a whole-input
derivation in the ParserPack generated from the authored maximal-token
language. -/
theorem canonical_program_has_parser_derivation
    (program : List Atom) (safe : programSafe program = true) :
    Nonempty (ParserPackRootDerives mm2ParserProfile parserPackPlan
      (canonicalProgramScalars program) (canonicalProgramCST program 0)) := by
  have atomsSafe := programAtomsSafe program safe
  refine ⟨?_⟩
  change ParserPackDerivesAt mm2ParserProfile parserPackPlan
    (canonicalProgramScalars program) parserPackPlan.lexical.startSort
    0 (canonicalProgramScalars program).length
    (canonicalProgramCST program 0)
  rw [ParserPackPlanAgreement.startSort_eq parserPackAgreement]
  simpa [mm2ParserProfile] using
    canonicalProgramDerivation [] program atomsSafe

/-- Exhaustive reference enumeration contains the exact canonical parse. -/
theorem canonical_program_is_enumerated
    (program : List Atom) (safe : programSafe program = true) :
    ∃ row ∈ enumerateRootWithin
        (1000 * (canonicalProgramScalars program).length + 9)
        mm2ParserProfile parserPackPlan (canonicalProgramScalars program),
      row.tree = canonicalProgramCST program 0 := by
  obtain ⟨derivation⟩ := canonical_program_has_parser_derivation program safe
  exact MM2MaximalTokenHeightBound.root_enumeration_complete derivation

/-- Authoritative admission joins a generated parser derivation to the
independently defined CST elaboration. -/
structure ParsedProgram (input : List Nat) where
  tree : CST
  atoms : List Atom
  derivation :
    ParserPackRootDerives mm2ParserProfile parserPackPlan input tree
  lowering : elaborateRootCST tree = .program atoms

/-- The generated parser and independent elaborator commute on every
canonically represented ordinary MM2 program. -/
theorem canonical_program_parser_square
    (program : List Atom) (safe : programSafe program = true) :
    Nonempty (ParsedProgram (canonicalProgramScalars program)) := by
  obtain ⟨derivation⟩ := canonical_program_has_parser_derivation program safe
  exact ⟨{
    tree := canonicalProgramCST program 0
    atoms := program
    derivation := derivation
    lowering := elaborateCanonicalProgram program 0 safe }⟩

/-- A successful target-owned rendering is parsed by the generated
ParserPack and elaborates to the exact source atom occurrences. -/
theorem successful_render_has_exact_parser_square
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
  rw [canonicalProgramScalars_eq_rendererScalars
    program recursiveSafe] at derivation
  exact ⟨{
    tree := canonicalProgramCST program 0
    atoms := program
    derivation := derivation
    lowering := elaborateCanonicalProgram program 0 safe }, rfl⟩

private def pDollarXTree : CST :=
  node "mm2:program-open" 0 3
    [node "mm2:open-atom-bare" 0 3
      [lexical "mm2:lex-bare-head" 'p' 0,
       node "mm2:bare-tail-cons" 1 3
        [lexical "mm2:lex-bare-char" '$' 1,
         node "mm2:bare-tail-cons" 2 3
          [lexical "mm2:lex-bare-char" 'x' 2,
           node "mm2:bare-tail-empty" 3 3]]],
     node "mm2:program-after-open-end" 3 3]

theorem pDollarX_is_one_symbol :
    elaborateRootCST pDollarXTree = .program [.symbol "p$x"] := by
  decide +kernel

private def quotedRawTree : CST :=
  node "mm2:program-closed" 0 6
    [node "mm2:closed-atom-quoted" 0 6
      [node "mm2:quoted-symbol" 0 6
        [node "mm2:quoted-chars-plain" 1 5
          [lexical "mm2:lex-quoted-char" 'a' 1,
           node "mm2:quoted-chars-escaped" 2 5
            [lexical "mm2:lex-escaped-char" '"' 3,
             node "mm2:quoted-chars-plain" 4 5
              [lexical "mm2:lex-quoted-char" 'b' 4,
               node "mm2:quoted-chars-empty" 5 5]]]]],
     node "mm2:program-empty" 6 6]

/-- Quoted MM2 tokens preserve their exact quote and escape bytes.  They are
symbols in the reader carrier, not host string literals. -/
theorem quoted_token_preserves_raw_spelling :
    elaborateRootCST quotedRawTree =
      .program [.symbol "\"a\\\"b\""] := by
  decide +kernel

private def malformedOpenAtomTree : CST :=
  node "mm2:program-open" 0 3
    [node "mm2:open-atom-bare" 0 1 [],
     node "mm2:program-after-open-end" 1 1]

/-- Lowering rejects a tree whose constructor is missing its required
lexical children. -/
theorem malformed_open_atom_tree_rejected :
    elaborateRootCST malformedOpenAtomTree = .malformedCST := by
  decide +kernel

#print axioms codepointsToString_stringScalars
#print axioms canonicalProgramScalars_eq_rendererScalars
#print axioms elaborateCanonicalProgram
#print axioms canonical_program_has_parser_derivation
#print axioms canonical_program_is_enumerated
#print axioms canonical_program_parser_square
#print axioms successful_render_has_exact_parser_square
#print axioms pDollarX_is_one_symbol
#print axioms quoted_token_preserves_raw_spelling
#print axioms malformed_open_atom_tree_rejected

end Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics
