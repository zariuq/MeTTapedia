import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler

/-!
# Separator plans extracted from scannerless GSLT presentations

This module recognizes the small but common presentation schema in which a
named token separator is one authored character class or end-of-file.  The
result is an explicit specialization plan; successful extraction carries a
soundness theorem back to the exact definition in the source presentation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SeparatorPlan

open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler

/-- Data needed by a whitespace-delimited incremental scanner. -/
structure Plan where
  definitionName : String
  separatorClass : String
deriving DecidableEq, Repr

/-- Extract only the recognized `alt (class ...) eof` separator schema. -/
def compile? (presentation : Presentation) (definitionName : String) :
    Option Plan := do
  let definition ←
    presentation.definitions.find? (fun candidate =>
      candidate.name == definitionName)
  match definition.body with
  | .alt (.class separatorClass) .eof =>
      some { definitionName, separatorClass }
  | _ => none

/-- Successful extraction identifies the exact definition selected by the
compiler's first-match lookup. -/
theorem compile?_selected
    {presentation : Presentation} {definitionName : String} {plan : Plan}
    (compiled : compile? presentation definitionName = some plan) :
    ∃ definition,
      presentation.definitions.find? (fun candidate =>
        candidate.name == definitionName) = some definition ∧
      definition.name = definitionName ∧
      definition.body = .alt (.class plan.separatorClass) .eof := by
  unfold compile? at compiled
  cases found : presentation.definitions.find? (fun candidate =>
      candidate.name == definitionName) with
  | none => simp [found] at compiled
  | some definition =>
      have named : definition.name = definitionName := by
        have selected := List.find?_some found
        simpa using selected
      cases body : definition.body with
      | alt left right =>
          cases left <;> cases right <;> simp [found, body] at compiled
          case class.eof separatorClass =>
            cases compiled
            exact ⟨definition, rfl, named, body⟩
      | _ => simp [found, body] at compiled

/-- Successful extraction is evidence about an actual source definition, not
permission to substitute a separately authored separator policy. -/
theorem compile?_sound
    {presentation : Presentation} {definitionName : String} {plan : Plan}
    (compiled : compile? presentation definitionName = some plan) :
    ∃ definition ∈ presentation.definitions,
      definition.name = definitionName ∧
      definition.body = .alt (.class plan.separatorClass) .eof := by
  rcases compile?_selected compiled with
    ⟨definition, selected, nameEq, bodyEq⟩
  exact ⟨definition, List.mem_of_find?_eq_some selected, nameEq, bodyEq⟩

/-- Executable membership in one presentation-owned character class. -/
def classContains (presentation : Presentation) (className : String)
    (codepoint : Nat) : Bool :=
  presentation.members.any fun member =>
    member.className == className && member.codepoint == codepoint

/-- The executable class lookup is exactly membership of the corresponding
`ClassMember` fact in the authored presentation. -/
theorem classContains_eq_true_iff
    (presentation : Presentation) (className : String) (codepoint : Nat) :
    classContains presentation className codepoint = true ↔
      ({ className, codepoint } : ClassMember) ∈ presentation.members := by
  simp [classContains, List.any_eq_true]
  constructor
  · rintro ⟨member, memberIn, nameEq, codepointEq⟩
    have memberEq : member = ({ className, codepoint } : ClassMember) := by
      cases member
      simp_all
    simpa [memberEq] using memberIn
  · intro memberIn
    exact ⟨{ className, codepoint }, memberIn, by simp⟩

end Mettapedia.GSLT.Parsing.SeparatorPlan
