import Mettapedia.GSLT.Parsing.PlainBnfSemanticAdmission

/-!
# Unicode-domain transport through admitted lexical declarations

This module uses the existing independent structured grammar and admission
models. It proves scalar bounds and exact first-occurrence lookup transport;
recognizing a lexical constructor or an acceptance tag is not a premise.
The public runtime must separately establish typed input admission and that
the authored validator's successful execution satisfies these invariants.
No source evaluator or alternate grammar representation is introduced here.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfLexicalDomain

open PlainBnfStructuredDenotation PlainBnfSemanticAdmission
open PlainBnfLexicalScalarSemantics

/-- The integer carrier and Unicode exclusions are both part of the domain. -/
def UnicodeInteger (scalar : Int) : Prop :=
  0 ≤ scalar ∧ scalar ≤ 1114111 ∧ (scalar < 55296 ∨ 57343 < scalar)

theorem unicodeInteger_iff (scalar : Int) :
    isUnicodeScalarInt scalar = true ↔ UnicodeInteger scalar := by
  simp [isUnicodeScalarInt, UnicodeInteger]

theorem scalarList_member_domain (scalars : List Int) (valid : ScalarListWellFormed scalars)
    (scalar : Int) (member : scalar ∈ scalars) : UnicodeInteger scalar := by
  induction scalars with
  | nil => simp at member
  | cons head tail ih =>
      cases tail with
      | nil =>
          have same : scalar = head := by simpa using member
          subst scalar
          exact (unicodeInteger_iff head).mp valid
      | cons next rest =>
          rcases List.mem_cons.mp member with same | later
          · subst scalar
            exact (unicodeInteger_iff head).mp valid.1
          · exact ih valid.2.2 later

def matcherScalars : LexicalMatcher → List Nat
  | .points scalars | .except scalars => scalars

def MatcherDomain (matcher : LexicalMatcher) : Prop :=
  ∀ scalar ∈ matcherScalars matcher, UnicodeInteger scalar

theorem matcherWellFormed_domain (matcher : LexicalMatcher) (valid : MatcherWellFormed matcher) :
    MatcherDomain matcher := by
  cases matcher with
  | points scalars =>
      intro scalar member
      exact scalarList_member_domain _ valid _ (List.mem_map.mpr ⟨scalar, member, rfl⟩)
  | except scalars =>
      rcases valid with empty | valid
      · subst scalars
        intro scalar member
        simp [matcherScalars] at member
      · intro scalar member
        exact scalarList_member_domain _ valid _ (List.mem_map.mpr ⟨scalar, member, rfl⟩)

theorem checked_matcher_domain (matcher : LexicalMatcher)
    (accepted : checkLexicalMatcher matcher = true) : MatcherDomain matcher :=
  matcherWellFormed_domain matcher ((checkLexicalMatcher_eq_true_iff matcher).mp accepted)

def DeclarationDomain (declaration : LexicalDeclaration) : Prop := MatcherDomain declaration.matcher

def EnvironmentDomain (declarations : List LexicalDeclaration) : Prop :=
  ∀ declaration ∈ declarations, DeclarationDomain declaration

theorem declarationWellFormed_domain (declaration : LexicalDeclaration)
    (valid : DeclarationWellFormed declaration) : DeclarationDomain declaration :=
  matcherWellFormed_domain declaration.matcher valid.2.2.2

theorem wellFormed_environment_domain (document : Document) (authority : GrammarAuthority)
    (valid : WellFormed document authority) : EnvironmentDomain authority.lexicalDeclarations := by
  intro declaration member
  have allDeclarations := valid.2.2.2.2.2.2.1
  exact declarationWellFormed_domain declaration
    ((List.forall_iff_forall_mem.mp allDeclarations) declaration member)

theorem checked_environment_domain (document : Document) (authority : GrammarAuthority)
    (accepted : check document authority = true) : EnvironmentDomain authority.lexicalDeclarations :=
  wellFormed_environment_domain document authority ((check_eq_true_iff document authority).mp accepted)

/-- The returned occurrence retains the complete declaration, not a Boolean
or lexical-class tag. The input position is independent of authored origin. -/
def firstLookupFrom (name : String) : List LexicalDeclaration → Nat → Option LexicalOccurrence
  | [], _ => none
  | head :: tail, index =>
      if name = head.referenceName then some ⟨index, head⟩
      else firstLookupFrom name tail (index + 1)

def firstLookup (name : String) (declarations : List LexicalDeclaration) : Option LexicalOccurrence :=
  firstLookupFrom name declarations 0

/-- The exact source-order prefix skipped by a successful lookup. In
particular, a later equal name cannot replace the first occurrence. -/
theorem firstLookupFrom_some_iff (name : String) (declarations : List LexicalDeclaration)
    (index : Nat) (occurrence : LexicalOccurrence) :
    firstLookupFrom name declarations index = some occurrence ↔
      ∃ skipped rest, declarations = skipped ++ occurrence.declaration :: rest ∧
        occurrence.declarationIndex = index + skipped.length ∧
        name = occurrence.declaration.referenceName ∧
        ∀ earlier ∈ skipped, name ≠ earlier.referenceName := by
  induction declarations generalizing index with
  | nil =>
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨skipped, rest, same, _⟩
        have lengths := congrArg List.length same
        simp at lengths
  | cons head tail ih =>
      by_cases equal : name = head.referenceName
      · constructor
        · intro found
          have same : (⟨index, head⟩ : LexicalOccurrence) = occurrence := by
            simpa [firstLookupFrom, equal] using found
          subst occurrence
          exact ⟨[], tail, rfl, by simp, equal, by simp⟩
        · rintro ⟨skipped, rest, same, position, nameMatch, absent⟩
          cases skipped with
          | nil =>
              have headSame := (List.cons.inj same).1
              have indexSame : occurrence.declarationIndex = index := by simpa using position
              rcases occurrence with ⟨occurrenceIndex, declaration⟩
              simp only at headSame indexSame
              subst declaration
              subst occurrenceIndex
              simp [firstLookupFrom, equal]
          | cons first earlier =>
              have headSame := (List.cons.inj same).1
              exact False.elim ((absent first (by simp)) (headSame ▸ equal))
      · constructor
        · intro found
          have child : firstLookupFrom name tail (index + 1) = some occurrence := by
            simpa [firstLookupFrom, equal] using found
          obtain ⟨skipped, rest, same, position, nameMatch, absent⟩ := (ih (index + 1)).mp child
          refine ⟨head :: skipped, rest, by simp [same], ?_, nameMatch, ?_⟩
          · simp only [List.length_cons]
            omega
          · intro earlier member
            rcases List.mem_cons.mp member with same | member
            · simpa [same] using equal
            · exact absent earlier member
        · rintro ⟨skipped, rest, same, position, nameMatch, absent⟩
          cases skipped with
          | nil =>
              have headSame := (List.cons.inj same).1
              exact False.elim (equal (headSame ▸ nameMatch))
          | cons first earlier =>
              have parts := List.cons.inj same
              have child := (ih (index + 1)).mpr
                ⟨earlier, rest, parts.2, by simp only [List.length_cons] at position; omega,
                  nameMatch, fun declaration member => absent declaration (by simp [member])⟩
              simpa [firstLookupFrom, equal] using child

theorem firstLookup_domain (name : String) (declarations : List LexicalDeclaration)
    (valid : EnvironmentDomain declarations) (occurrence : LexicalOccurrence)
    (found : firstLookup name declarations = some occurrence) : DeclarationDomain occurrence.declaration := by
  obtain ⟨skipped, rest, same, _, _, _⟩ := (firstLookupFrom_some_iff name declarations 0 occurrence).mp found
  apply valid occurrence.declaration
  rw [same]
  simp

/-- This is the independent typed-analysis license: actual admission
reflection must supply `WellFormed`, and lookup must identify its complete
first declaration before any scalar specialization uses these bounds. -/
theorem admitted_first_lookup_scalar_domain (input : AdmittedInput) (name : String)
    (occurrence : LexicalOccurrence) (found : firstLookup name input.authority.lexicalDeclarations = some occurrence)
    (scalar : Nat) (member : scalar ∈ matcherScalars occurrence.declaration.matcher) :
    UnicodeInteger scalar :=
  firstLookup_domain name input.authority.lexicalDeclarations
    (wellFormed_environment_domain input.document input.authority input.wellFormed)
    occurrence found scalar member

theorem unicodeInteger_fits_signed64 (scalar : Int) (valid : UnicodeInteger scalar) :
    -(2 ^ 63 : Int) ≤ scalar ∧ scalar < 2 ^ 63 := by
  obtain ⟨nonnegative, upper, _⟩ := valid
  constructor <;> omega

theorem unicodeInteger_successor_fits_signed64 (scalar : Int) (valid : UnicodeInteger scalar) :
    -(2 ^ 63 : Int) ≤ scalar + 1 ∧ scalar + 1 < 2 ^ 63 := by
  obtain ⟨nonnegative, upper, _⟩ := valid
  constructor <;> omega

private def testDeclaration (matcher : LexicalMatcher) (origin : Nat) : LexicalDeclaration :=
  ⟨"name", "class", matcher, "label", ⟨"authority", origin⟩⟩

example : firstLookup "name"
    [testDeclaration (.points [65]) 2, testDeclaration (.points [66]) 7] =
    some ⟨0, testDeclaration (.points [65]) 2⟩ := by decide

/-- A successful first-match lookup alone does not validate the selected
declaration: the first match here contains a surrogate code point. -/
example : firstLookup "name"
    [testDeclaration (.points [55296]) 2, testDeclaration (.points [65]) 7] =
      some ⟨0, testDeclaration (.points [55296]) 2⟩ ∧
    ¬ DeclarationDomain (testDeclaration (.points [55296]) 2) := by
  constructor
  · decide
  · simp [DeclarationDomain, MatcherDomain, matcherScalars, testDeclaration, UnicodeInteger]

example : MatcherDomain (.except []) := by simp [MatcherDomain, matcherScalars]

#print axioms checked_environment_domain
#print axioms firstLookupFrom_some_iff
#print axioms admitted_first_lookup_scalar_domain
#print axioms unicodeInteger_fits_signed64
#print axioms unicodeInteger_successor_fits_signed64

end Mettapedia.GSLT.Parsing.PlainBnfLexicalDomain
