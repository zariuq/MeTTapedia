import Mettapedia.GSLT.LanguageDef.TypedOccurrenceCoverage

/-!
# Typed addresses of admitted rewrite-side rows

A structurally admitted row selects an actual occurrence of its rule.
For left and right sites, rest-aware rewrite typing refines that row to its
typed binder context. Premise sites need their own premise typing judgment.
-/

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding

set_option autoImplicit false

/-- Structural admission really checks every stored explicit row, including
rows not reached by a particular match. -/
theorem admittedFor_row_declared
    {rule : RewriteRule} {spec : RuleBindingSpec}
    (admitted : admittedFor rule spec = true)
    {row : MetavariableOccurrence}
    (member : row ∈ spec.occurrences) :
    occurrenceDeclared rule row = true := by
  have rowsPass : spec.occurrences.all (fun row =>
      occurrenceDeclared rule row &&
        match dependencies? spec row.name,
          occurrenceDepthAtSite? rule row.site row.path with
        | some dependencies, some depth =>
            row.arguments.length == dependencies.length &&
              row.arguments.all (fun argument => argument.isGroundAt depth)
        | _, _ => false) = true := by
    simp only [admittedFor, Bool.and_eq_true] at admitted
    tauto
  have rowPass := List.all_eq_true.mp rowsPass row member
  simp only [Bool.and_eq_true] at rowPass
  exact rowPass.1

/-- An admitted left/right occurrence row in a typed authored rewrite has an
actual typed site and the exact ordered local binder sorts. This is the
canonical rule carrier, rather than an independently retyped pattern. -/
theorem RewriteHasType.typedSideRow
    {language : LanguageDef} {rule : RewriteRule}
    (typed : RewriteHasType language rule)
    {spec : RuleBindingSpec} (admitted : admittedFor rule spec = true)
    {row : MetavariableOccurrence} (member : row ∈ spec.occurrences)
    (side : row.site = .left ∨ row.site = .right) :
    ∃ pattern rootType binderPrefix,
      sitePattern? rule row.site = some pattern ∧
      TypedOccurrenceAt language
        (FreeTypeContext.ofList rule.typeContext) []
        pattern rootType binderPrefix row.path row.name := by
  have declared := admittedFor_row_declared admitted member
  obtain ⟨rootType, leftTyped, rightTyped⟩ := typed
  rcases side with left | right
  · have observed : occurrenceAt? rule.left row.path = some row.name := by
      simpa [occurrenceDeclared, sitePattern?, left] using declared
    obtain ⟨binderPrefix, classified⟩ :=
      leftTyped.occurrenceAt_typed observed
    exact ⟨rule.left, rootType, binderPrefix,
      by simp [sitePattern?, left], classified⟩
  · have observed : occurrenceAt? rule.right row.path = some row.name := by
      simpa [occurrenceDeclared, sitePattern?, right] using declared
    obtain ⟨binderPrefix, classified⟩ :=
      rightTyped.occurrenceAt_typed observed
    exact ⟨rule.right, rootType, binderPrefix,
      by simp [sitePattern?, right], classified⟩

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
