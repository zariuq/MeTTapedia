import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-!
# Reflection on one sort

A reflective presentation tells quote and drop apart by their constructor
labels.  It does not require names and processes to live in two different
sorts.  This module checks both sides of that rule on a small language whose
only sort is `Term`:

* positive: quote and drop are two distinct endomaps of `Term`, with a nullary
  unit and the quote-drop equation, and the presentation validates;
* negative: a presentation naming one constructor as both quote and drop is
  rejected, and so is one whose unit is not nullary.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReflectionOnOneSort

open Mettapedia.OSLF.MeTTaIL.Syntax

private def term : TypeExpr := .base "Term"

/-- A language with one sort: names and processes are both terms. -/
def oneSort : LanguageDef where
  name := "OneSort"
  types := ["Term"]
  terms := [
    { label := "Nil", category := "Term", params := [], syntaxPattern := [.terminal "()"] },
    { label := "Quote", category := "Term", params := [.simple "t" term],
      syntaxPattern := [.terminal "'", .nonTerminal "t"] },
    { label := "Drop", category := "Term", params := [.simple "t" term],
      syntaxPattern := [.terminal "!", .nonTerminal "t"] },
    { label := "App", category := "Term", params := [.simple "f" term, .simple "a" term],
      syntaxPattern := [.terminal "(", .nonTerminal "f", .nonTerminal "a", .terminal ")"] },
    { label := "Par", category := "Term", params := [.simple "ts" (TypeExpr.bag term)],
      syntaxPattern := [.terminal "{", .nonTerminal "ts", .separator "|", .terminal "}"],
      algebra? := some { flatten := true, unit := some "Nil" } }
  ]
  equations := [
    { name := "QuoteDrop", typeContext := [("x", term)], premises := [],
      left := .apply "Quote" [.apply "Drop" [.fvar "x"]], right := .fvar "x" },
    { name := "QuoteQuote", typeContext := [("x", term)], premises := [],
      left := .apply "Quote" [.apply "Quote" [.fvar "x"]], right := .fvar "x" }
  ]
  rewrites := []

/-- Quote and drop on the one sort, with `Nil` as the parallel unit. -/
def presentation : ReflectivePresentationDecl where
  name := "one-sort"
  processSort := "Term"
  nameSort := "Term"
  quoteConstructor := "Quote"
  dropConstructor := "Drop"
  parallelCollection := .hashBag
  parallelUnitConstructor := "Nil"
  quoteDropEquation := "QuoteDrop"
  -- Closed: one-sort quotations are code that substitution leaves opaque.
  quoteScope := .closed

/-- Positive: a presentation whose names and processes share one sort validates. -/
theorem presentation_valid : oneSort.validateReflectivePresentation presentation = [] := by
  apply LanguageDef.validateReflectivePresentation_eq_nil_of_unique
    (quote := oneSort.terms[1]) (drop := oneSort.terms[2]) (unit := oneSort.terms[0])
    (equation := oneSort.equations[0])
    (quoteParameter := "t") (dropParameter := "t") (equationVariable := "x")
  all_goals simp [oneSort, presentation, term, LanguageDef.typeNames, TypeDecl.plain]

/-- The validated one-sort presentation still keeps quote and drop apart. -/
theorem quote_ne_drop : presentation.quoteConstructor ≠ presentation.dropConstructor :=
  ReflectiveCanonical.quoteConstructor_ne_dropConstructor_of_validate
    oneSort presentation presentation_valid

/-- Negative: one constructor cannot serve as both quote and drop. -/
def quoteAsDrop : ReflectivePresentationDecl :=
  { presentation with dropConstructor := "Quote", quoteDropEquation := "QuoteQuote" }

theorem quoteAsDrop_rejected : oneSort.validateReflectivePresentation quoteAsDrop ≠ [] := by
  intro valid
  exact ReflectiveCanonical.quoteConstructor_ne_dropConstructor_of_validate
    oneSort quoteAsDrop valid rfl

/-- Negative: the parallel unit must be nullary; `App` takes two arguments. -/
def appAsUnit : ReflectivePresentationDecl :=
  { presentation with parallelUnitConstructor := "App" }

theorem appAsUnit_rejected : oneSort.validateReflectivePresentation appAsUnit ≠ [] := by
  intro valid
  obtain ⟨witness⟩ :=
    LanguageDef.reflectivePresentationWitness_of_validate_eq_nil oneSort appAsUnit valid
  have listed : witness.unit ∈ oneSort.terms.filter
      (fun rule => rule.label == appAsUnit.parallelUnitConstructor) := by
    rw [witness.unitUnique]
    exact List.mem_singleton.mpr rfl
  have nullary := witness.unitParameters
  simp [oneSort, appAsUnit, presentation] at listed
  simp [listed] at nullary

end Mettapedia.OSLF.MeTTaIL.ReflectionOnOneSort
