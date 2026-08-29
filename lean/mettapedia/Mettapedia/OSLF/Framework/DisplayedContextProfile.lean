import Mettapedia.OSLF.Framework.DisplayedRewriteTyping

/-!
# Free-variable profiles of displayed rewrite contexts

A contextual modal constructor is indexed by the variables occurring in the
fixed part of a one-hole rewrite context, not by variables occurring only in
the selected focus.  This module computes that distinction structurally and
recovers the exact authored type of every retained context variable.

The profile is executable.  Typing evidence proves that its `filterMap`
cannot drop a name; no principal typing or global context normalization is
assumed.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

namespace DisplayedContextProfile

/-- Free metavariable names in the fixed frames around the hole.  Names that
occur only in the eventual focus are deliberately absent. -/
def externalFreeFvarNames : OneHoleContext → List String
  | .hole => []
  | .apply _ before inner after =>
      before.flatMap Pattern.freeFvarNames ++
        externalFreeFvarNames inner ++
        after.flatMap Pattern.freeFvarNames
  | .lambda _ inner => externalFreeFvarNames inner
  | .multiLambda _ _ inner => externalFreeFvarNames inner
  | .substBody inner replacement =>
      externalFreeFvarNames inner ++ replacement.freeFvarNames
  | .substReplacement body inner =>
      body.freeFvarNames ++ externalFreeFvarNames inner
  | .collection _ before inner after rest =>
      before.flatMap Pattern.freeFvarNames ++
        externalFreeFvarNames inner ++
        after.flatMap Pattern.freeFvarNames ++ rest.toList

/-- Plugging a focus combines exactly the fixed-context support and the
focus support.  The theorem is extensional on membership because the two
ordered lists may interleave according to the hole position. -/
theorem mem_freeFvarNames_fill_iff (context : OneHoleContext)
    (focus : Pattern) (name : String) :
    name ∈ (context.fill focus).freeFvarNames ↔
      name ∈ externalFreeFvarNames context ∨
        name ∈ focus.freeFvarNames := by
  induction context with
  | hole => simp [OneHoleContext.fill, externalFreeFvarNames]
  | apply constructor before inner after inductionHypothesis =>
      simp [OneHoleContext.fill, externalFreeFvarNames,
        Pattern.freeFvarNames, inductionHypothesis, or_assoc, or_left_comm,
        or_comm]
  | lambda binder inner inductionHypothesis =>
      simpa [OneHoleContext.fill, externalFreeFvarNames,
        Pattern.freeFvarNames] using inductionHypothesis
  | multiLambda arity binders inner inductionHypothesis =>
      simpa [OneHoleContext.fill, externalFreeFvarNames,
        Pattern.freeFvarNames] using inductionHypothesis
  | substBody inner replacement inductionHypothesis =>
      simp [OneHoleContext.fill, externalFreeFvarNames,
        Pattern.freeFvarNames, inductionHypothesis, or_assoc, or_left_comm,
        or_comm]
  | substReplacement body inner inductionHypothesis =>
      simp [OneHoleContext.fill, externalFreeFvarNames,
        Pattern.freeFvarNames, inductionHypothesis, or_assoc, or_left_comm,
        or_comm]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp [OneHoleContext.fill, externalFreeFvarNames,
        Pattern.freeFvarNames, inductionHypothesis, or_assoc, or_left_comm,
        or_comm]

/-- Every fixed-context variable remains a variable of the filled source. -/
theorem mem_freeFvarNames_fill_of_mem_external
    (context : OneHoleContext) (focus : Pattern) {name : String}
    (membership : name ∈ externalFreeFvarNames context) :
    name ∈ (context.fill focus).freeFvarNames :=
  (mem_freeFvarNames_fill_iff context focus name).2 (Or.inl membership)

/-- Stable authored-order support of the fixed part of a displayed context. -/
def variableNames {definition : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping definition) : List String :=
  (externalFreeFvarNames typing.site.context).eraseDups

/-- Exact first-match type-context lookup used by the sorting judgment. -/
def variableType? {definition : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping definition) (name : String) :
    Option TypeExpr :=
  FreeTypeContext.ofList typing.site.rewrite.typeContext name

/-- Every selected fixed-context variable is backed by the authored rewrite
typing context. -/
theorem variableType?_exists {definition : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping definition) {name : String}
    (membership : name ∈ variableNames typing) :
    ∃ type, variableType? typing name = some type := by
  have externalMembership :
      name ∈ externalFreeFvarNames typing.site.context := by
    simpa [variableNames] using membership
  have filledMembership :
      name ∈ (typing.site.context.fill typing.site.focus).freeFvarNames :=
    mem_freeFvarNames_fill_of_mem_external
      typing.site.context typing.site.focus externalMembership
  have sourceMembership : name ∈ typing.site.rewrite.left.freeFvarNames := by
    rw [typing.site.context_fill_focus] at filledMembership
    simpa [DisplayedRewriteSite.source, DisplayedRewriteSite.rewrite] using
      filledMembership
  obtain ⟨type, lookup⟩ :=
    typing.rewriteLeftTyped.freeType_of_mem_freeFvarNames_of_isObjectPattern
      typing.sourceIsObject sourceMembership
  exact ⟨type, lookup⟩

/-- Executable context profile.  The output order is the first-occurrence
order of the fixed context; each row carries its exact authored type. -/
def bindings {definition : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping definition) :
    List (String × TypeExpr) :=
  (variableNames typing).filterMap fun name =>
    (variableType? typing name).map fun type => (name, type)

private theorem filterMap_total_names
    (names : List String) (lookup : String → Option TypeExpr)
    (total : ∀ name ∈ names, ∃ type, lookup name = some type) :
    (names.filterMap fun name =>
      (lookup name).map fun type => (name, type)).map Prod.fst = names := by
  induction names with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      obtain ⟨headType, headLookup⟩ := total head (by simp)
      simp only [List.filterMap_cons, headLookup, Option.map_some,
        List.map_cons]
      congr 1
      exact inductionHypothesis fun name membership =>
        total name (by simp [membership])

/-- Executable profiling drops no context variable. -/
theorem bindingNames {definition : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping definition) :
    (bindings typing).map Prod.fst = variableNames typing := by
  apply filterMap_total_names
  intro name membership
  exact variableType?_exists typing membership

@[simp]
theorem length_bindings {definition : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping definition) :
    (bindings typing).length = (variableNames typing).length := by
  have lengths := congrArg List.length (bindingNames typing)
  simpa using lengths

/-- Carrier types demanded by the fixed free-variable profile. -/
def carrierTypes {definition : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping definition) : List TypeExpr :=
  (bindings typing).map Prod.snd

/-! ## Positive and negative controls -/

namespace Canary

private def context : OneHoleContext :=
  OneHoleContext.apply "displayed-context-profile:pair"
    [.fvar "left"] .hole [.fvar "right"]

/-- Fixed-frame variables are retained on both sides of the hole. -/
theorem external_variables_retained :
    externalFreeFvarNames context = ["left", "right"] := by
  simp [context, externalFreeFvarNames, Pattern.freeFvarNames]

/-- A variable occurring only in the focus does not become a context
parameter. -/
theorem focus_only_variable_absent :
    "focus" ∉ externalFreeFvarNames context := by
  simp [context, externalFreeFvarNames, Pattern.freeFvarNames]

/-- Filling recovers all three supports without conflating their roles. -/
theorem filled_support_exact :
    (Pattern.apply "displayed-context-profile:pair"
      [.fvar "left", .fvar "focus", .fvar "right"]).freeFvarNames =
        ["left", "focus", "right"] := by
  simp [Pattern.freeFvarNames]

end Canary

#print axioms mem_freeFvarNames_fill_iff
#print axioms variableType?_exists
#print axioms bindingNames
#print axioms length_bindings
#print axioms Canary.external_variables_retained
#print axioms Canary.focus_only_variable_absent
#print axioms Canary.filled_support_exact

end DisplayedContextProfile

end Mettapedia.OSLF.Framework
