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
/-- Exact scannerless recognition over one immutable codepoint sequence.

The relation is proof-relevant.  Alternative choice, reference resolution,
and semantic-action correspondence theorems. -/
inductive RecognizesAt (presentation : Presentation) (input : List Nat) :
    Expr → Nat → Nat → Type where
  | epsilon (cursor : Nat) :
      RecognizesAt presentation input .epsilon cursor cursor
  | char
      (lookup : input[start]? = some codepoint) :
      RecognizesAt presentation input (.char codepoint) start (start + 1)
  | classMember
      (lookup : input[start]? = some codepoint)
      (member : ({ className, codepoint } : ClassMember) ∈
        presentation.members) :
      RecognizesAt presentation input (.class className) start (start + 1)
  | literal
      (slice : input.extract start (start + codepoints.length) = codepoints) :
      RecognizesAt presentation input (.literal codepoints)
        start (start + codepoints.length)
  | altLeft
      (left : RecognizesAt presentation input first start stop) :
      RecognizesAt presentation input (.alt first second) start stop
  | altRight
      (right : RecognizesAt presentation input second start stop) :
      RecognizesAt presentation input (.alt first second) start stop
  | seq
      (firstResult : RecognizesAt presentation input first start middle)
      (secondResult : RecognizesAt presentation input second middle stop) :
      RecognizesAt presentation input (.seq first second) start stop
  | left
      (firstResult : RecognizesAt presentation input first start middle)
      (secondResult : RecognizesAt presentation input second middle stop) :
      RecognizesAt presentation input (.left first second) start stop
  | right
      (firstResult : RecognizesAt presentation input first start middle)
      (secondResult : RecognizesAt presentation input second middle stop) :
      RecognizesAt presentation input (.right first second) start stop
  | node
      (bodyResult : RecognizesAt presentation input body start stop) :
      RecognizesAt presentation input (.node label body) start stop
  | ref
      (definition : Definition)
      (member : definition ∈ presentation.definitions)
      (nameEq : definition.name = name)
      (bodyResult : RecognizesAt presentation input definition.body start stop) :
      RecognizesAt presentation input (.ref name) start stop
  | starZero (cursor : Nat) :
      RecognizesAt presentation input (.star body) cursor cursor
  | starMore
      (head : RecognizesAt presentation input body start middle)
      (progress : start < middle)
      (tail : RecognizesAt presentation input (.star body) middle stop) :
      RecognizesAt presentation input (.star body) start stop
  | plus
      (head : RecognizesAt presentation input body start middle)
      (progress : start < middle)
      (tail : RecognizesAt presentation input (.star body) middle stop) :
      RecognizesAt presentation input (.plus body) start stop
  | eof
      (atEnd : cursor = input.length) :
      RecognizesAt presentation input .eof cursor cursor

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
        derivation := .classMember (by rfl) (by simp [digitPresentation]) } }

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
      simp [digitPresentation] at member

end Mettapedia.GSLT.Parsing.PresentationExprSemantics
