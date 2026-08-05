import Mettapedia.GSLT.Parsing.PresentationExprSemantics
import Mettapedia.GSLT.Parsing.SeparatorPlan

/-!
# Executable correspondence for presentation-derived separator plans

A `SeparatorPlan` is useful only if its native branch decision is exactly the
decision licensed by the source presentation.  This module proves that joint
at the byte level.  The executable classifier consults the presentation's
actual member facts, while the specification side is the proof-relevant
scannerless `Expr` semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SeparatorPlanCorrespondence

open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.GSLT.Parsing.SeparatorPlan

/-- The three outcomes needed by a whitespace-delimited streaming scanner. -/
inductive Decision where
  | separator
  | content
  | eof
deriving DecidableEq, Repr

/-- Native classification generated from a presentation-owned separator
class.  No language-specific codepoint appears in this function. -/
def decideAt (presentation : Presentation) (plan : Plan)
    (input : List Nat) (cursor : Nat) : Decision :=
  if inBounds : cursor < input.length then
    if classContains presentation plan.separatorClass input[cursor] then
      .separator
    else
      .content
  else
    .eof

/-- Executable class membership is equivalent to a one-codepoint source
derivation.  This is both preservation and reflection for the generated
class-test instruction. -/
theorem classContains_iff_recognizesAt
    (presentation : Presentation) (className : String)
    (input : List Nat) (cursor : Nat)
    (inBounds : cursor < input.length) :
    classContains presentation className input[cursor] = true ↔
      Nonempty (RecognizesAt presentation input (.class className)
        cursor (cursor + 1)) := by
  constructor
  · intro contains
    refine ⟨.classMember (codepoint := input[cursor]) ?_ ?_⟩
    · simp
    · exact (classContains_eq_true_iff presentation className input[cursor]).mp
        contains
  · rintro ⟨derivation⟩
    rcases derivation.classEvidence with ⟨codepoint, lookup, member⟩
    have lookupAt : input[cursor]? = some input[cursor] := by simp
    rw [lookupAt] at lookup
    injection lookup with codepointEq
    subst codepoint
    exact (classContains_eq_true_iff presentation className input[cursor]).mpr
      member

/-- A generated separator branch is taken exactly when the source class has
a derivation at that byte. -/
theorem decideAt_separator_iff
    (presentation : Presentation) (plan : Plan)
    (input : List Nat) (cursor : Nat) :
    decideAt presentation plan input cursor = .separator ↔
      Nonempty (RecognizesAt presentation input (.class plan.separatorClass)
        cursor (cursor + 1)) := by
  by_cases inBounds : cursor < input.length
  · simpa [decideAt, inBounds] using
      classContains_iff_recognizesAt presentation plan.separatorClass
        input cursor inBounds
  · have impossible : ¬ Nonempty
        (RecognizesAt presentation input (.class plan.separatorClass)
          cursor (cursor + 1)) := by
      rintro ⟨derivation⟩
      rcases derivation.classEvidence with ⟨codepoint, lookup, _⟩
      have lookupNone : input[cursor]? = none := by simp [inBounds]
      rw [lookupNone] at lookup
      contradiction
    simp [decideAt, inBounds, impossible]

/-- EOF classification is exact on a cursor known not to have advanced past
the input.  Scanner cursor accounting supplies this bound compositionally. -/
theorem decideAt_eof_iff
    (presentation : Presentation) (plan : Plan)
    (input : List Nat) (cursor : Nat)
    (cursorBound : cursor ≤ input.length) :
    decideAt presentation plan input cursor = .eof ↔
      Nonempty (RecognizesAt presentation input .eof cursor cursor) := by
  constructor
  · intro decided
    have atEnd : cursor = input.length := by
      unfold decideAt at decided
      split at decided <;> rename_i inBounds
      · split at decided <;> simp_all
      · exact Nat.le_antisymm cursorBound (Nat.le_of_not_gt inBounds)
    exact ⟨.eof atEnd⟩
  · rintro ⟨derivation⟩
    cases derivation with
    | eof atEnd =>
        subst cursor
        simp [decideAt]

/-- Preservation and reflection for the exact presentation schema accepted
by `SeparatorPlan.compile?`: the native separator branch is equivalent to
the `alt (class ...) eof` body consuming one codepoint. -/
theorem decideAt_separator_iff_planBody
    (presentation : Presentation) (plan : Plan)
    (input : List Nat) (cursor : Nat) :
    decideAt presentation plan input cursor = .separator ↔
      Nonempty (RecognizesAt presentation input
        (.alt (.class plan.separatorClass) .eof) cursor (cursor + 1)) := by
  constructor
  · intro decided
    have recognized :=
      (decideAt_separator_iff presentation plan input cursor).mp decided
    exact ⟨.altLeft recognized.some⟩
  · rintro ⟨recognized⟩
    cases recognized with
    | altLeft classResult =>
        exact (decideAt_separator_iff presentation plan input cursor).mpr
          ⟨classResult⟩
    | altRight eofResult =>
        cases eofResult

/-- The same generated branch is exact at EOF.  The cursor bound is supplied
by the scanner's independent cursor-accounting theorem. -/
theorem decideAt_eof_iff_planBody
    (presentation : Presentation) (plan : Plan)
    (input : List Nat) (cursor : Nat)
    (cursorBound : cursor ≤ input.length) :
    decideAt presentation plan input cursor = .eof ↔
      Nonempty (RecognizesAt presentation input
        (.alt (.class plan.separatorClass) .eof) cursor cursor) := by
  constructor
  · intro decided
    have recognized :=
      (decideAt_eof_iff presentation plan input cursor cursorBound).mp decided
    exact ⟨.altRight recognized.some⟩
  · rintro ⟨recognized⟩
    cases recognized with
    | altLeft classResult =>
        cases classResult
    | altRight eofResult =>
        exact (decideAt_eof_iff presentation plan input cursor cursorBound).mpr
          ⟨eofResult⟩

/-- End-to-end preservation/reflection for a successfully compiled separator
definition.  The theorem returns the exact source definition selected by the
compiler together with the semantic equivalence of its body and the native
branch. -/
theorem compile?_separator_correspondence
    {presentation : Presentation} {definitionName : String} {plan : Plan}
    (compiled : compile? presentation definitionName = some plan)
    (input : List Nat) (cursor : Nat) :
    ∃ definition,
      presentation.definitions.find? (fun candidate =>
        candidate.name == definitionName) = some definition ∧
      definition ∈ presentation.definitions ∧
      definition.name = definitionName ∧
      (decideAt presentation plan input cursor = .separator ↔
        Nonempty (RecognizesAt presentation input definition.body
          cursor (cursor + 1))) := by
  rcases compile?_selected compiled with
    ⟨definition, selected, nameEq, bodyEq⟩
  refine ⟨definition, selected, List.mem_of_find?_eq_some selected, nameEq, ?_⟩
  rw [bodyEq]
  exact decideAt_separator_iff_planBody presentation plan input cursor

/-- EOF half of the same end-to-end compiler theorem. -/
theorem compile?_eof_correspondence
    {presentation : Presentation} {definitionName : String} {plan : Plan}
    (compiled : compile? presentation definitionName = some plan)
    (input : List Nat) (cursor : Nat)
    (cursorBound : cursor ≤ input.length) :
    ∃ definition,
      presentation.definitions.find? (fun candidate =>
        candidate.name == definitionName) = some definition ∧
      definition ∈ presentation.definitions ∧
      definition.name = definitionName ∧
      (decideAt presentation plan input cursor = .eof ↔
        Nonempty (RecognizesAt presentation input definition.body
          cursor cursor)) := by
  rcases compile?_selected compiled with
    ⟨definition, selected, nameEq, bodyEq⟩
  refine ⟨definition, selected, List.mem_of_find?_eq_some selected, nameEq, ?_⟩
  rw [bodyEq]
  exact decideAt_eof_iff_planBody presentation plan input cursor cursorBound

/-- A content branch is not an unclassified default: it carries the exact
negative fact that the authored separator class has no derivation here. -/
theorem decideAt_content_iff
    (presentation : Presentation) (plan : Plan)
    (input : List Nat) (cursor : Nat) :
    decideAt presentation plan input cursor = .content ↔
      cursor < input.length ∧
      ¬ Nonempty (RecognizesAt presentation input
        (.class plan.separatorClass) cursor (cursor + 1)) := by
  by_cases inBounds : cursor < input.length
  · constructor
    · intro decided
      refine ⟨inBounds, ?_⟩
      intro recognized
      have contains :=
        (classContains_iff_recognizesAt presentation plan.separatorClass
          input cursor inBounds).mpr recognized
      simp [decideAt, inBounds, contains] at decided
    · rintro ⟨_, notRecognized⟩
      have notContains :
          classContains presentation plan.separatorClass input[cursor] ≠ true :=
        fun contains => notRecognized <|
          (classContains_iff_recognizesAt presentation plan.separatorClass
            input cursor inBounds).mp contains
      have containsFalse :
          classContains presentation plan.separatorClass input[cursor] = false :=
        Bool.eq_false_of_not_eq_true notContains
      simp [decideAt, inBounds, containsFalse]
  · simp [decideAt, inBounds]

/-! ## Positive and negative calibration -/

private def separatorFixture : Presentation :=
  { name := "SeparatorFixture"
    definitions :=
      [{ name := "separator", body := .alt (.class "space") .eof }]
    members := [{ className := "space", codepoint := 32 }] }

private def separatorFixturePlan : Plan :=
  { definitionName := "separator", separatorClass := "space" }

example : decideAt separatorFixture separatorFixturePlan [32] 0 = .separator := by
  decide

example : decideAt separatorFixture separatorFixturePlan [65] 0 = .content := by
  decide

example : decideAt separatorFixture separatorFixturePlan [] 0 = .eof := by
  decide

end Mettapedia.GSLT.Parsing.SeparatorPlanCorrespondence
