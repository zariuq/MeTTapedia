import Mettapedia.OSLF.Framework.ContextualModalSignature

/-!
# Variable roles at one displayed rewrite occurrence

The modal rules generated from an authored rewrite distinguish three kinds of
free-variable support around a selected occurrence:

* rely variables occur only in the fixed one-hole context;
* focus parameters occur only in the selected focus;
* shared variables occur in both and therefore carry a matching constraint.

All three rows retain first-occurrence order.  Their union is exactly the
free-variable support of the selected rewrite source, and every retained name
has an authored type in that rewrite's type context.  This boundary is purely
source-derived; it does not inspect a generated calculus or a derivation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.DisplayedRewriteVariableProfile

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {language : LanguageDef}

/-- Duplicate-free free-variable support of the fixed context frames. -/
def contextNames (site : DisplayedRewriteSite language) : List String :=
  (DisplayedContextProfile.externalFreeFvarNames site.context).eraseDups

/-- Duplicate-free free-variable support of the selected focus. -/
def focusNames (site : DisplayedRewriteSite language) : List String :=
  site.focus.freeFvarNames.eraseDups

/-- Variables supplied independently by the fixed context. -/
def relyNames (site : DisplayedRewriteSite language) : List String :=
  (contextNames site).filter fun name => !(focusNames site).contains name

/-- Variables constrained to agree between the focus and fixed context. -/
def sharedNames (site : DisplayedRewriteSite language) : List String :=
  (contextNames site).filter fun name => (focusNames site).contains name

/-- Variables supplied by the selected focus but absent from the context. -/
def focusParameterNames (site : DisplayedRewriteSite language) : List String :=
  (focusNames site).filter fun name => !(contextNames site).contains name

@[simp]
theorem relyNames_root (language : LanguageDef)
    (index : Fin language.rewrites.length) :
    relyNames (DisplayedRewriteSite.root language index) = [] := by
  simp [relyNames, contextNames, focusNames, DisplayedRewriteSite.root,
    DisplayedContextProfile.externalFreeFvarNames]

@[simp]
theorem sharedNames_root (language : LanguageDef)
    (index : Fin language.rewrites.length) :
    sharedNames (DisplayedRewriteSite.root language index) = [] := by
  simp [sharedNames, contextNames, focusNames, DisplayedRewriteSite.root,
    DisplayedContextProfile.externalFreeFvarNames]

@[simp]
theorem focusParameterNames_root (language : LanguageDef)
    (index : Fin language.rewrites.length) :
    focusParameterNames (DisplayedRewriteSite.root language index) =
      language.rewrites[index].left.freeFvarNames.eraseDups := by
  simp [focusParameterNames, contextNames, focusNames,
    DisplayedRewriteSite.root, DisplayedContextProfile.externalFreeFvarNames]

@[simp]
theorem mem_relyNames (site : DisplayedRewriteSite language) (name : String) :
    name ∈ relyNames site ↔
      name ∈ contextNames site ∧ name ∉ focusNames site := by
  simp [relyNames]

@[simp]
theorem mem_sharedNames (site : DisplayedRewriteSite language) (name : String) :
    name ∈ sharedNames site ↔
      name ∈ contextNames site ∧ name ∈ focusNames site := by
  simp [sharedNames]

@[simp]
theorem mem_focusParameterNames (site : DisplayedRewriteSite language)
    (name : String) :
    name ∈ focusParameterNames site ↔
      name ∈ focusNames site ∧ name ∉ contextNames site := by
  simp [focusParameterNames]

/-- The three roles partition the complete free-variable support of the
authored rewrite source. -/
theorem mem_source_iff_roles (site : DisplayedRewriteSite language)
    (name : String) :
    name ∈ site.rewrite.left.freeFvarNames ↔
      name ∈ relyNames site ∨ name ∈ sharedNames site ∨
        name ∈ focusParameterNames site := by
  change name ∈ site.source.freeFvarNames ↔ _
  rw [← site.context_fill_focus]
  rw [DisplayedContextProfile.mem_freeFvarNames_fill_iff]
  simp [contextNames, focusNames]
  tauto

/-- No variable can occupy two of the three roles. -/
theorem roles_pairwise_exclusive (site : DisplayedRewriteSite language)
    (name : String) :
    ¬ (name ∈ relyNames site ∧ name ∈ sharedNames site) ∧
      ¬ (name ∈ relyNames site ∧ name ∈ focusParameterNames site) ∧
      ¬ (name ∈ sharedNames site ∧
        name ∈ focusParameterNames site) := by
  simp
  tauto

/-! ## Authored typing of every role -/

/-- Exact authored type-context lookup shared by the three rows. -/
def variableType? {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) (name : String) :
    Option TypeExpr :=
  FreeTypeContext.ofList typing.site.rewrite.typeContext name

/-- Every source variable is backed by the authored rewrite type context. -/
theorem variableType?_exists {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) {name : String}
    (membership : name ∈ typing.site.rewrite.left.freeFvarNames) :
    ∃ type, variableType? typing name = some type := by
  obtain ⟨type, lookup⟩ :=
    typing.rewriteLeftTyped.freeType_of_mem_freeFvarNames_of_isObjectPattern
      typing.sourceIsObject membership
  exact ⟨type, lookup⟩

/-- Add the exact authored type to an ordered name row. -/
def typedBindings {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) (names : List String) :
    List (String × TypeExpr) :=
  names.filterMap fun name =>
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

/-- When a requested name row is covered by the authored source support,
adding its exact type annotations preserves the name row verbatim. -/
theorem typedBindingNames_of_supported
    {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) (names : List String)
    (supported : ∀ name ∈ names,
      name ∈ typing.site.rewrite.left.freeFvarNames) :
    (typedBindings typing names).map Prod.fst = names := by
  apply filterMap_total_names
  intro name membership
  exact variableType?_exists typing (supported name membership)

def relyBindings {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) : List (String × TypeExpr) :=
  typedBindings typing (relyNames typing.site)

def sharedBindings {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) : List (String × TypeExpr) :=
  typedBindings typing (sharedNames typing.site)

def focusParameterBindings {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) : List (String × TypeExpr) :=
  typedBindings typing (focusParameterNames typing.site)

theorem relyBindingNames {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) :
    (relyBindings typing).map Prod.fst = relyNames typing.site := by
  apply typedBindingNames_of_supported
  intro name membership
  exact (mem_source_iff_roles typing.site name).2 (Or.inl membership)

theorem sharedBindingNames {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) :
    (sharedBindings typing).map Prod.fst = sharedNames typing.site := by
  apply typedBindingNames_of_supported
  intro name membership
  exact (mem_source_iff_roles typing.site name).2
    (Or.inr (Or.inl membership))

theorem focusParameterBindingNames {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) :
    (focusParameterBindings typing).map Prod.fst =
      focusParameterNames typing.site := by
  apply typedBindingNames_of_supported
  intro name membership
  exact (mem_source_iff_roles typing.site name).2
    (Or.inr (Or.inr membership))

/-! ## Discriminating controls -/

namespace Canary

open Mettapedia.OSLF.Framework.ContextualModalSignature.Canary

/-- The middle-of-ternary occurrence has two genuine rely variables. -/
theorem middle_rely_roles (name : String) :
    name ∈ relyNames middleSite ↔ name = "left" ∨ name = "right" := by
  rw [mem_relyNames]
  simp [contextNames, focusNames, middleSite,
    DisplayedContextProfile.externalFreeFvarNames, Pattern.freeFvarNames]
  rintro (rfl | rfl) <;> decide

/-- Its selected focus contributes one introduction parameter. -/
theorem middle_focus_parameter_role (name : String) :
    name ∈ focusParameterNames middleSite ↔ name = "focus" := by
  rw [mem_focusParameterNames]
  simp [contextNames, focusNames, middleSite,
    DisplayedContextProfile.externalFreeFvarNames, Pattern.freeFvarNames]
  rintro rfl
  decide

/-- The three variables in the middle example are pairwise source-local. -/
theorem middle_has_no_shared_role (name : String) :
    name ∉ sharedNames middleSite := by
  rw [mem_sharedNames]
  simp [contextNames, focusNames, middleSite,
    DisplayedContextProfile.externalFreeFvarNames, Pattern.freeFvarNames]
  rintro (rfl | rfl) <;> decide

open Mettapedia.OSLF.Framework.DisplayedRewriteSite.Canary

/-- Repeating the same authored variable inside and outside the hole is a
shared constraint, not an extra rely or focus parameter. -/
theorem repeated_variable_is_shared (name : String) :
    name ∈ sharedNames firstOccurrence ↔ name = "x" := by
  rw [mem_sharedNames]
  simp [contextNames, focusNames, firstOccurrence,
    DisplayedContextProfile.externalFreeFvarNames, Pattern.freeFvarNames]

theorem repeated_variable_is_not_rely (name : String) :
    name ∉ relyNames firstOccurrence := by
  rw [mem_relyNames]
  simp [contextNames, focusNames, firstOccurrence,
    DisplayedContextProfile.externalFreeFvarNames, Pattern.freeFvarNames]

theorem repeated_variable_is_not_focus_parameter (name : String) :
    name ∉ focusParameterNames firstOccurrence := by
  rw [mem_focusParameterNames]
  simp [contextNames, focusNames, firstOccurrence,
    DisplayedContextProfile.externalFreeFvarNames, Pattern.freeFvarNames]

end Canary

#print axioms mem_source_iff_roles
#print axioms roles_pairwise_exclusive
#print axioms relyNames_root
#print axioms sharedNames_root
#print axioms focusParameterNames_root
#print axioms variableType?_exists
#print axioms relyBindingNames
#print axioms sharedBindingNames
#print axioms focusParameterBindingNames
#print axioms Canary.middle_rely_roles
#print axioms Canary.middle_focus_parameter_role
#print axioms Canary.middle_has_no_shared_role
#print axioms Canary.repeated_variable_is_shared
#print axioms Canary.repeated_variable_is_not_rely
#print axioms Canary.repeated_variable_is_not_focus_parameter

end Mettapedia.OSLF.Framework.DisplayedRewriteVariableProfile
