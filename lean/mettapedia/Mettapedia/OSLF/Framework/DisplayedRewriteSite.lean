import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Displayed source sites of authored rewrites

The source-indexed OSLF construction is indexed by selected occurrences in the
source side of authored rewrites.  A selected occurrence is not merely a
pattern that happens to occur somewhere: it retains the rewrite-list index,
the focused pattern, the one-hole context, and evidence that filling the
context reconstructs that rewrite's left-hand side.

This module defines that input boundary.  It does not yet emit a typed
definition and therefore does not claim to implement the OSLF generation
functor.  Later generators can consume a finite `DisplayedSiteSelection` and
prove their output adequate for exactly those requested sites.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- One selected occurrence in the source of an authored rewrite.

The `Fin` index retains authored-list identity and order.  The `Selects`
evidence rules out an arbitrary context that merely carries plausible syntax.
-/
structure DisplayedRewriteSite (language : LanguageDef) where
  rewriteIndex : Fin language.rewrites.length
  focus : Pattern
  context : OneHoleContext
  selects : Selects focus context language.rewrites[rewriteIndex].left

namespace DisplayedRewriteSite

/-- A displayed site is determined by its authored rewrite occurrence, focus,
and zipper.  Selection evidence is proof-irrelevant. -/
@[ext]
theorem ext {language : LanguageDef}
    {first second : DisplayedRewriteSite language}
    (rewriteIndex : first.rewriteIndex = second.rewriteIndex)
    (focus : first.focus = second.focus)
    (context : first.context = second.context) : first = second := by
  cases first
  cases second
  cases rewriteIndex
  cases focus
  cases context
  rfl

/-- The authored rewrite containing a displayed site. -/
def rewrite {language : LanguageDef}
    (site : DisplayedRewriteSite language) : RewriteRule :=
  language.rewrites[site.rewriteIndex]

/-- The source pattern reconstructed by a displayed site. -/
def source {language : LanguageDef}
    (site : DisplayedRewriteSite language) : Pattern :=
  site.rewrite.left

/-- A displayed site reconstructs the source of its indexed rewrite. -/
theorem context_fill_focus {language : LanguageDef}
    (site : DisplayedRewriteSite language) :
    site.context.fill site.focus = site.source :=
  site.selects.fill_eq

/-- The whole left-hand side is always a valid root site. -/
def root (language : LanguageDef)
    (rewriteIndex : Fin language.rewrites.length) :
    DisplayedRewriteSite language where
  rewriteIndex := rewriteIndex
  focus := language.rewrites[rewriteIndex].left
  context := .hole
  selects := .here

/-- Compile a displayed site from the exact zipper enumerator. -/
def ofCompiledContext (language : LanguageDef)
    (rewriteIndex : Fin language.rewrites.length)
    (focus : Pattern) (context : OneHoleContext)
    (compiled : context ∈ zippersAt focus language.rewrites[rewriteIndex].left) :
    DisplayedRewriteSite language where
  rewriteIndex := rewriteIndex
  focus := focus
  context := context
  selects := zippersAt_sound compiled

/-- Every displayed site is found by the exact zipper enumerator. -/
theorem context_mem_zippersAt {language : LanguageDef}
    (site : DisplayedRewriteSite language) :
    site.context ∈ zippersAt site.focus site.source :=
  zippersAt_complete site.selects

end DisplayedRewriteSite

/-- A finite, authored-order selection of source occurrences requested from a
later typing-definition generator.  Repeated entries remain repeated. -/
abbrev DisplayedSiteSelection (language : LanguageDef) :=
  List (DisplayedRewriteSite language)

namespace DisplayedSiteSelection

/-- Every site requested by `smaller` is also requested by `larger`.
This relation ignores order and multiplicity; it is the logical coverage
order, not the incremental-build order. -/
def Covers {language : LanguageDef}
    (smaller larger : DisplayedSiteSelection language) : Prop :=
  ∀ site, site ∈ smaller → site ∈ larger

theorem covers_refl {language : LanguageDef}
    (selection : DisplayedSiteSelection language) :
    Covers selection selection := by
  intro site membership
  exact membership

theorem covers_trans {language : LanguageDef}
    {first second third : DisplayedSiteSelection language}
    (firstSecond : Covers first second) (secondThird : Covers second third) :
    Covers first third := by
  intro site membership
  exact secondThird site (firstSecond site membership)

/-- `extended` was obtained by appending a delta to `base`.  This is stronger
than `Covers`: it preserves authored order and supplies the exact incremental
compilation unit. -/
def AppendOnlyExtension {language : LanguageDef}
    (base extended : DisplayedSiteSelection language) : Prop :=
  ∃ delta, extended = base ++ delta

theorem appendOnlyExtension_refl {language : LanguageDef}
    (selection : DisplayedSiteSelection language) :
    AppendOnlyExtension selection selection := by
  exact ⟨[], by simp⟩

theorem appendOnlyExtension_trans {language : LanguageDef}
    {first second third : DisplayedSiteSelection language}
    (firstSecond : AppendOnlyExtension first second)
    (secondThird : AppendOnlyExtension second third) :
    AppendOnlyExtension first third := by
  obtain ⟨firstDelta, rfl⟩ := firstSecond
  obtain ⟨secondDelta, rfl⟩ := secondThird
  exact ⟨firstDelta ++ secondDelta, by simp [List.append_assoc]⟩

theorem appendOnlyExtension_covers {language : LanguageDef}
    {base extended : DisplayedSiteSelection language}
    (extension : AppendOnlyExtension base extended) :
    Covers base extended := by
  obtain ⟨delta, rfl⟩ := extension
  intro site member
  exact List.mem_append_left _ member

end DisplayedSiteSelection

/-! ## Positive and negative controls -/

namespace DisplayedRewriteSite.Canary

def repeatedSourceRule : RewriteRule where
  name := "displayed-site-canary:contract-pair"
  typeContext := []
  premises := []
  left := .apply "displayed-site-canary:pair" [.fvar "x", .fvar "x"]
  right := .fvar "x"

def language : LanguageDef :=
  { LanguageDef.empty "displayed-site-canary" with
    rewrites := [repeatedSourceRule] }

def rewriteIndex : Fin language.rewrites.length := ⟨0, by decide⟩

/-- The first occurrence of `x` in `pair(x, x)`. -/
def firstOccurrence : DisplayedRewriteSite language where
  rewriteIndex := rewriteIndex
  focus := .fvar "x"
  context := .apply "displayed-site-canary:pair" [] .hole [.fvar "x"]
  selects := .apply .here

/-- The second occurrence of the same pattern in `pair(x, x)`. -/
def secondOccurrence : DisplayedRewriteSite language where
  rewriteIndex := rewriteIndex
  focus := .fvar "x"
  context := .apply "displayed-site-canary:pair" [.fvar "x"] .hole []
  selects := .apply .here

theorem firstOccurrence_reconstructs_source :
    firstOccurrence.context.fill firstOccurrence.focus =
      repeatedSourceRule.left := by
  exact firstOccurrence.context_fill_focus

/-- Equal focused syntax does not erase occurrence identity: the two zippers
select different positions. -/
theorem repeated_focus_occurrences_distinct :
    firstOccurrence.context ≠ secondOccurrence.context := by
  decide

/-- A context with the wrong constructor head cannot be certified as selecting
the requested occurrence in the authored source. -/
theorem wrong_head_not_selected :
    ¬ Selects (.fvar "x")
      (.apply "displayed-site-canary:not-pair" [] .hole [.fvar "x"])
      repeatedSourceRule.left := by
  intro selected
  have reconstructed := selected.fill_eq
  simp [OneHoleContext.fill, repeatedSourceRule] at reconstructed

def firstSelection : DisplayedSiteSelection language := [firstOccurrence]

def bothSelection : DisplayedSiteSelection language :=
  [firstOccurrence, secondOccurrence]

theorem both_extends_first :
    DisplayedSiteSelection.AppendOnlyExtension firstSelection bothSelection := by
  exact ⟨[secondOccurrence], rfl⟩

/-- Reordering an existing selection is coverage-preserving but is not an
append-only compilation delta. -/
theorem reversed_not_appendOnlyExtension :
    ¬ DisplayedSiteSelection.AppendOnlyExtension
      [firstOccurrence] [secondOccurrence, firstOccurrence] := by
  rintro ⟨delta, equality⟩
  have heads : secondOccurrence = firstOccurrence := by
    simpa using congrArg List.head? equality
  exact repeated_focus_occurrences_distinct
    (congrArg DisplayedRewriteSite.context heads.symm)

end DisplayedRewriteSite.Canary

#print axioms DisplayedRewriteSite.context_fill_focus
#print axioms DisplayedRewriteSite.context_mem_zippersAt
#print axioms DisplayedSiteSelection.appendOnlyExtension_trans
#print axioms DisplayedSiteSelection.appendOnlyExtension_covers
#print axioms DisplayedRewriteSite.Canary.firstOccurrence_reconstructs_source
#print axioms DisplayedRewriteSite.Canary.repeated_focus_occurrences_distinct
#print axioms DisplayedRewriteSite.Canary.wrong_head_not_selected
#print axioms DisplayedRewriteSite.Canary.reversed_not_appendOnlyExtension

end Mettapedia.OSLF.Framework
