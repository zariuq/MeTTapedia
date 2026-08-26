import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler

/-!
# Proof-relevant semantics for scannerless presentation expressions

`LanguageDefSyntaxCompiler.Expr` is the source language rendered for
GSLT2Parse.  This module gives that source language an exact span semantics
before any parser backend is selected.  References resolve through actual
presentation definitions, character classes through actual membership facts,
and repetition carries an explicit progress witness.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PresentationExprSemantics

open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler

set_option autoImplicit true in
/-- Exact scannerless recognition over one immutable codepoint sequence,
parameterized by the evidence carried by an authored character class.

The relation is proof-relevant.  Alternative choice, reference resolution,
and semantic-action correspondence theorems. -/
inductive RecognizesAtUsing
    (classEvidence : String → Nat → Prop)
    (presentation : Presentation) (input : List Nat) :
    Expr → Nat → Nat → Type where
  | epsilon (cursor : Nat) :
      RecognizesAtUsing classEvidence presentation input .epsilon cursor cursor
  | char
      (lookup : input[start]? = some codepoint) :
      RecognizesAtUsing classEvidence presentation input
        (.char codepoint) start (start + 1)
  | classMember
      (lookup : input[start]? = some codepoint)
      (evidence : classEvidence className codepoint) :
      RecognizesAtUsing classEvidence presentation input
        (.class className) start (start + 1)
  | literal
      (slice : input.extract start (start + codepoints.length) = codepoints) :
      RecognizesAtUsing classEvidence presentation input (.literal codepoints)
        start (start + codepoints.length)
  | altLeft
      (left : RecognizesAtUsing classEvidence presentation input
        first start stop) :
      RecognizesAtUsing classEvidence presentation input
        (.alt first second) start stop
  | altRight
      (right : RecognizesAtUsing classEvidence presentation input
        second start stop) :
      RecognizesAtUsing classEvidence presentation input
        (.alt first second) start stop
  | seq
      (firstResult : RecognizesAtUsing classEvidence presentation input
        first start middle)
      (secondResult : RecognizesAtUsing classEvidence presentation input
        second middle stop) :
      RecognizesAtUsing classEvidence presentation input
        (.seq first second) start stop
  | left
      (firstResult : RecognizesAtUsing classEvidence presentation input
        first start middle)
      (secondResult : RecognizesAtUsing classEvidence presentation input
        second middle stop) :
      RecognizesAtUsing classEvidence presentation input
        (.left first second) start stop
  | right
      (firstResult : RecognizesAtUsing classEvidence presentation input
        first start middle)
      (secondResult : RecognizesAtUsing classEvidence presentation input
        second middle stop) :
      RecognizesAtUsing classEvidence presentation input
        (.right first second) start stop
  | node
      (bodyResult : RecognizesAtUsing classEvidence presentation input
        body start stop) :
      RecognizesAtUsing classEvidence presentation input
        (.node label body) start stop
  | ref
      (definition : Definition)
      (member : definition ∈ presentation.definitions)
      (nameEq : definition.name = name)
      (bodyResult : RecognizesAtUsing classEvidence presentation input
        definition.body start stop) :
      RecognizesAtUsing classEvidence presentation input (.ref name) start stop
  | starZero (cursor : Nat) :
      RecognizesAtUsing classEvidence presentation input
        (.star body) cursor cursor
  | starMore
      (head : RecognizesAtUsing classEvidence presentation input
        body start middle)
      (progress : start < middle)
      (tail : RecognizesAtUsing classEvidence presentation input
        (.star body) middle stop) :
      RecognizesAtUsing classEvidence presentation input
        (.star body) start stop
  | plus
      (head : RecognizesAtUsing classEvidence presentation input
        body start middle)
      (progress : start < middle)
      (tail : RecognizesAtUsing classEvidence presentation input
        (.star body) middle stop) :
      RecognizesAtUsing classEvidence presentation input
        (.plus body) start stop
  | eof
      (atEnd : cursor = input.length) :
      RecognizesAtUsing classEvidence presentation input .eof cursor cursor

/-- The original finite positive-membership interpretation is one exact
instance of the evidence-parameterized recognition relation. -/
abbrev FiniteClassEvidence (presentation : Presentation)
    (className : String) (codepoint : Nat) : Prop :=
  ({ className, codepoint } : ClassMember) ∈ presentation.members

abbrev RecognizesAt (presentation : Presentation) (input : List Nat) :
    Expr → Nat → Nat → Type :=
  RecognizesAtUsing (FiniteClassEvidence presentation) presentation input

/-! ## Exact concrete-syntax output

The recognition evidence above deliberately records parser choices rather than
only an accepted language.  The following output projection interprets the
semantic actions of `Expr`: `seq` retains both sides, `left` and `right` drop
the indicated administrative result, and `node` creates one labelled CST
occurrence.  Terminal leaves retain their exact codepoints and source span.
-/

/-- One occurrence in the scannerless concrete-syntax tree.  Spans are part
of the value, so equal lexemes at different source occurrences remain
distinct. -/
inductive CST where
  | terminal (codepoints : List Nat) (start stop : Nat)
  | node (label : String) (start stop : Nat) (children : List CST)
  deriving Repr

mutual
  private def decEqCST : (left right : CST) → Decidable (left = right)
    | .terminal leftCodepoints leftStart leftStop,
        .terminal rightCodepoints rightStart rightStop =>
      if codepointsEq : leftCodepoints = rightCodepoints then
        if startEq : leftStart = rightStart then
          if stopEq : leftStop = rightStop then
            isTrue (by subst_vars; rfl)
          else
            isFalse (by intro equality; cases equality; exact stopEq rfl)
        else
          isFalse (by intro equality; cases equality; exact startEq rfl)
      else
        isFalse (by intro equality; cases equality; exact codepointsEq rfl)
    | .node leftLabel leftStart leftStop leftChildren,
        .node rightLabel rightStart rightStop rightChildren =>
      if labelEq : leftLabel = rightLabel then
        if startEq : leftStart = rightStart then
          if stopEq : leftStop = rightStop then
            match decEqCSTList leftChildren rightChildren with
            | isTrue childrenEq => isTrue (by subst_vars; rfl)
            | isFalse childrenEq =>
                isFalse (by intro equality; cases equality; exact childrenEq rfl)
          else
            isFalse (by intro equality; cases equality; exact stopEq rfl)
        else
          isFalse (by intro equality; cases equality; exact startEq rfl)
      else
        isFalse (by intro equality; cases equality; exact labelEq rfl)
    | .terminal _ _ _, .node _ _ _ _ => isFalse CST.noConfusion
    | .node _ _ _ _, .terminal _ _ _ => isFalse CST.noConfusion

  private def decEqCSTList :
      (left right : List CST) → Decidable (left = right)
    | [], [] => isTrue rfl
    | head :: tail, [] => isFalse (by intro equality; cases equality)
    | [], head :: tail => isFalse (by intro equality; cases equality)
    | leftHead :: leftTail, rightHead :: rightTail =>
      match decEqCST leftHead rightHead, decEqCSTList leftTail rightTail with
      | isTrue headEq, isTrue tailEq => isTrue (by subst_vars; rfl)
      | isFalse headEq, _ =>
          isFalse (by intro equality; cases equality; exact headEq rfl)
      | _, isFalse tailEq =>
          isFalse (by intro equality; cases equality; exact tailEq rfl)
end

instance : DecidableEq CST := decEqCST

/-- Deterministic semantic-action output of one proof-relevant recognition.
The function consumes the evidence itself, so alternative and definition
choices remain available in the fibre even when their CST outputs agree. -/
def RecognizesAtUsing.cst
    {classEvidence : String → Nat → Prop}
    {presentation : Presentation} {input : List Nat}
    {expression : Expr} {start stop : Nat} :
    RecognizesAtUsing classEvidence presentation input expression start stop →
      List CST
  | .epsilon _ => []
  | .char (codepoint := codepoint) _ =>
      [.terminal [codepoint] start (start + 1)]
  | .classMember (codepoint := codepoint) _ _ =>
      [.terminal [codepoint] start (start + 1)]
  | .literal (codepoints := codepoints) _ =>
      [.terminal codepoints start (start + codepoints.length)]
  | .altLeft leftResult => leftResult.cst
  | .altRight rightResult => rightResult.cst
  | .seq firstResult secondResult =>
      firstResult.cst ++ secondResult.cst
  | .left firstResult _ => firstResult.cst
  | .right _ secondResult => secondResult.cst
  | .node (label := label) bodyResult =>
      [.node label start stop bodyResult.cst]
  | .ref _ _ _ bodyResult => bodyResult.cst
  | .starZero _ => []
  | .starMore head _ tail => head.cst ++ tail.cst
  | .plus head _ tail => head.cst ++ tail.cst
  | .eof _ => []

/-- Recognition at one exact CST output.  This is an indexed refinement of
the original evidence, not a second parser relation. -/
abbrev CSTRecognizesAtUsing
    (classEvidence : String → Nat → Prop)
    (presentation : Presentation) (input : List Nat)
    (expression : Expr) (start stop : Nat) (output : List CST) : Type :=
  { derivation :
      RecognizesAtUsing classEvidence presentation input expression start stop //
    derivation.cst = output }

abbrev CSTRecognizesAt (presentation : Presentation) (input : List Nat)
    (expression : Expr) (start stop : Nat) (output : List CST) : Type :=
  CSTRecognizesAtUsing (FiniteClassEvidence presentation) presentation input
    expression start stop output

/-- The total space of CST-indexed evidence is exactly equivalent to the
original proof fibre.  Thus adding CST outputs neither invents nor identifies
recognition evidence. -/
def recognizesAtUsingCSTEquiv
    (classEvidence : String → Nat → Prop)
    (presentation : Presentation) (input : List Nat)
    (expression : Expr) (start stop : Nat) :
    RecognizesAtUsing classEvidence presentation input expression start stop ≃
      Σ output, CSTRecognizesAtUsing classEvidence presentation input
        expression start stop output where
  toFun derivation := ⟨derivation.cst, ⟨derivation, rfl⟩⟩
  invFun indexed := indexed.2.1
  left_inv _ := rfl
  right_inv indexed := by
    rcases indexed with ⟨output, derivation, outputEq⟩
    subst output
    rfl

/-- Existential acceptance is the corresponding propositional shadow of the
exact fibre equivalence. -/
theorem recognizesAtUsing_iff_exists_cst
    (classEvidence : String → Nat → Prop)
    (presentation : Presentation) (input : List Nat)
    (expression : Expr) (start stop : Nat) :
    Nonempty
        (RecognizesAtUsing classEvidence presentation input expression
          start stop) ↔
      ∃ output, Nonempty
        (CSTRecognizesAtUsing classEvidence presentation input expression
          start stop output) := by
  constructor
  · rintro ⟨derivation⟩
    exact ⟨derivation.cst, ⟨⟨derivation, rfl⟩⟩⟩
  · rintro ⟨_, ⟨derivation⟩⟩
    exact ⟨derivation.1⟩

/-- A named definition derivation retains the exact source definition chosen
from the presentation. -/
structure DefinitionDerivation (presentation : Presentation)
    (input : List Nat) (name : String) (start stop : Nat) : Type where
  definition : Definition
  member : definition ∈ presentation.definitions
  nameEq : definition.name = name
  derivation : RecognizesAt presentation input definition.body start stop

/-- Whole-input acceptance of a named presentation root. -/
structure Accepts (presentation : Presentation) (root : String)
    (input : List Nat) : Type where
  rootDerivation : DefinitionDerivation presentation input root 0 input.length

/-- Character-class inversion exposes the exact consumed codepoint and the
source membership fact. -/
def RecognizesAt.classEvidence
    {presentation : Presentation} {input : List Nat}
    {className : String} {start : Nat}
    (derivation :
      RecognizesAt presentation input (.class className) start (start + 1)) :
    Σ codepoint,
      (input[start]? = some codepoint) ×'
      (({ className, codepoint } : ClassMember) ∈ presentation.members) :=
  match derivation with
  | .classMember lookup member => ⟨_, lookup, member⟩

/-! ## Positive and negative calibration -/

private def digitPresentation : Presentation :=
  { name := "DigitFixture"
    definitions := [{ name := "digit", body := .class "digit" }]
    members := [{ className := "digit", codepoint := 48 }] }

def digitPositive : Accepts digitPresentation "digit" [48] :=
  { rootDerivation :=
      { definition := { name := "digit", body := .class "digit" }
        member := by simp [digitPresentation]
        nameEq := rfl
        derivation := .classMember (by rfl)
          (by simp [FiniteClassEvidence, digitPresentation]) } }

theorem digitPositive_exact_cst :
    Nonempty (CSTRecognizesAt digitPresentation [48]
      (.class "digit") 0 1 [.terminal [48] 0 1]) := by
  exact ⟨⟨digitPositive.rootDerivation.derivation, rfl⟩⟩

/-- Equal codepoints at different physical spans remain different CST
occurrences. -/
theorem equal_lexemes_at_distinct_spans_are_distinct :
    CST.terminal [48] 0 1 ≠ CST.terminal [48] 1 2 := by
  decide

/-- A codepoint absent from the authored class cannot acquire a derivation. -/
theorem digitNegative :
    IsEmpty (Accepts digitPresentation "digit" [49]) := by
  constructor
  intro accepted
  rcases accepted with ⟨⟨definition, member, nameEq, derivation⟩⟩
  simp [digitPresentation] at member
  subst definition
  cases derivation with
  | classMember lookup member =>
      simp at lookup
      subst_vars
      simp [FiniteClassEvidence, digitPresentation] at member

end Mettapedia.GSLT.Parsing.PresentationExprSemantics
