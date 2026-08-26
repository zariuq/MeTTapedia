/-!
# Language-neutral ParserPack lexical profiles

ParserPack extends an authored structural `LanguageDef` only with scalar
classes and lexical states.  This module gives that extension an exact,
backend-independent meaning.  Point classes and complement classes are
distinct constructors; both are restricted to Unicode scalar values.

The definitions mirror the data consumed by the ParserPack compiler without
making any particular C structure or parser backend authoritative.
-/

namespace Mettapedia.GSLT.Parsing.ParserProfileSemantics

/-- A scalar class is either a finite positive set or the complement of a
finite exclusion set, always within the Unicode-scalar carrier. -/
inductive LexicalClassKind where
  | points (codepoints : List Nat)
  | except (excluded : List Nat)
  deriving DecidableEq, Repr

structure LexicalClassDecl where
  name : String
  kind : LexicalClassKind
  deriving DecidableEq, Repr

structure LexicalStateDecl where
  resultSort : String
  className : String
  ruleLabel : String
  deriving DecidableEq, Repr

structure ParserProfileLayer where
  name : String
  startSort : String
  classes : List LexicalClassDecl
  states : List LexicalStateDecl
  deriving DecidableEq, Repr

def ParserProfileLayer.class? (profile : ParserProfileLayer)
    (name : String) : Option LexicalClassDecl :=
  profile.classes.find? (fun declaration => declaration.name == name)

/-- Fail-closed unique lookup of the lexical rule for a result sort. -/
def ParserProfileLayer.lexicalRule? (profile : ParserProfileLayer)
    (resultSort : String) : Option String :=
  match profile.states.filter (fun state => state.resultSort == resultSort) with
  | [state] => some state.ruleLabel
  | _ => none

/-- JSON and ParserPack operate on Unicode scalar values, not arbitrary
natural numbers.  In particular, surrogate code points are excluded. -/
def isUnicodeScalar (codepoint : Nat) : Bool :=
  decide (codepoint ≤ 1114111 ∧ (codepoint < 55296 ∨ 57343 < codepoint))

def LexicalClassKind.accepts (kind : LexicalClassKind)
    (codepoint : Nat) : Bool :=
  isUnicodeScalar codepoint &&
    match kind with
    | .points codepoints => codepoints.contains codepoint
    | .except excluded => !(excluded.contains codepoint)

def ParserProfileLayer.classAccepts? (profile : ParserProfileLayer)
    (className : String) (codepoint : Nat) : Option Bool :=
  (profile.class? className).map fun declaration =>
    declaration.kind.accepts codepoint

/-- Proposition-valued evidence associated with the exact profile lookup.
An undefined class supplies no evidence. -/
def ParserProfileLayer.ClassEvidence (profile : ParserProfileLayer)
    (className : String) (codepoint : Nat) : Prop :=
  profile.classAccepts? className codepoint = some true

/-! ## Generic calibration and negative controls -/

private def calibrationProfile : ParserProfileLayer := {
  name := "Calibration"
  startSort := "Start"
  classes := [
    { name := "digit", kind := .points [48, 49] },
    { name := "unquoted", kind := .except [34, 92] }]
  states := [
    { resultSort := "Digit", className := "digit", ruleLabel := "lex-digit" }]
}

theorem point_class_positive_and_negative :
    calibrationProfile.classAccepts? "digit" 48 = some true ∧
      calibrationProfile.classAccepts? "digit" 50 = some false := by
  decide

theorem complement_class_positive_and_negative :
    calibrationProfile.classAccepts? "unquoted" 65 = some true ∧
      calibrationProfile.classAccepts? "unquoted" 34 = some false := by
  decide

/-- Complement syntax never expands the carrier beyond Unicode scalars. -/
theorem complement_rejects_non_scalars :
    calibrationProfile.classAccepts? "unquoted" 55296 = some false ∧
      calibrationProfile.classAccepts? "unquoted" 1114112 = some false := by
  decide

/-- Unknown classes fail closed instead of becoming an `any` terminal. -/
theorem unknown_class_has_no_evidence (codepoint : Nat) :
    ¬ calibrationProfile.ClassEvidence "missing" codepoint := by
  simp [ParserProfileLayer.ClassEvidence,
    ParserProfileLayer.classAccepts?, ParserProfileLayer.class?,
    calibrationProfile]

end Mettapedia.GSLT.Parsing.ParserProfileSemantics
