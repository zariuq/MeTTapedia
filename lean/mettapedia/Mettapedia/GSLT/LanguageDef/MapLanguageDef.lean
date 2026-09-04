import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Image of a language definition under a symbol action

`StructuralMorphism` carries each authored declaration of a source
presentation to a declaration of a target.  This module defines the underlying
whole-presentation symbol action: `mapLanguageDef` applies one
`LanguageDefSymbolMap` action to every declaration list at once.  Identity and
composition laws follow from the established per-declaration laws, and the
membership transport lemmas supply the bridge used when a mapped presentation
is included into a larger validated target.

This is not by itself a functor on validated structural presentations.  Its
image is a raw `LanguageDef`, not a `ValidatedLanguageDef`: a
non-injective sort action can collapse two authored sorts onto one name, so
validity is not preserved automatically.  The concluding canaries record one
positive image computation and that exact failure.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Apply a symbol action to every declaration list of a presentation.  The
language name is not a symbol namespace and is retained. -/
def mapLanguageDef (symbols : LanguageDefSymbolMap)
    (language : LanguageDef) : LanguageDef :=
  { language with
    types := language.types.map (mapTypeDecl symbols)
    terms := language.terms.map (mapGrammarRule symbols)
    equations := language.equations.map (mapEquation symbols)
    rewrites := language.rewrites.map (mapRewriteRule symbols) }

@[simp] theorem mapLanguageDef_name (symbols : LanguageDefSymbolMap)
    (language : LanguageDef) :
    (mapLanguageDef symbols language).name = language.name := rfl

@[simp] theorem mapLanguageDef_types (symbols : LanguageDefSymbolMap)
    (language : LanguageDef) :
    (mapLanguageDef symbols language).types =
      language.types.map (mapTypeDecl symbols) := rfl

@[simp] theorem mapLanguageDef_terms (symbols : LanguageDefSymbolMap)
    (language : LanguageDef) :
    (mapLanguageDef symbols language).terms =
      language.terms.map (mapGrammarRule symbols) := rfl

@[simp] theorem mapLanguageDef_equations (symbols : LanguageDefSymbolMap)
    (language : LanguageDef) :
    (mapLanguageDef symbols language).equations =
      language.equations.map (mapEquation symbols) := rfl

@[simp] theorem mapLanguageDef_rewrites (symbols : LanguageDefSymbolMap)
    (language : LanguageDef) :
    (mapLanguageDef symbols language).rewrites =
      language.rewrites.map (mapRewriteRule symbols) := rfl

private theorem listMapEqSelf {α : Type} {function : α → α}
    (pointwise : ∀ element, function element = element) :
    ∀ elements : List α, elements.map function = elements := by
  intro elements
  induction elements with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [pointwise head, inductionHypothesis]

/-- The identity symbol action leaves every presentation unchanged. -/
@[simp] theorem mapLanguageDef_id (language : LanguageDef) :
    mapLanguageDef LanguageDefSymbolMap.id language = language := by
  cases language
  simp [mapLanguageDef, listMapEqSelf mapTypeDecl_id,
    listMapEqSelf mapGrammarRule_id, listMapEqSelf mapEquation_id,
    listMapEqSelf mapRewriteRule_id]

/-- Composite symbol actions act by consecutive application. -/
theorem mapLanguageDef_comp (first second : LanguageDefSymbolMap)
    (language : LanguageDef) :
    mapLanguageDef (first.comp second) language =
      mapLanguageDef second (mapLanguageDef first language) := by
  cases language
  simp [mapLanguageDef, List.map_map, Function.comp_def]

/-! ## Membership transport into the image -/

theorem mem_types_mapLanguageDef (symbols : LanguageDefSymbolMap)
    {declaration : TypeDecl} {language : LanguageDef}
    (membership : List.Mem declaration language.types) :
    List.Mem (mapTypeDecl symbols declaration)
      (mapLanguageDef symbols language).types :=
  List.mem_map_of_mem membership

theorem mem_terms_mapLanguageDef (symbols : LanguageDefSymbolMap)
    {rule : GrammarRule} {language : LanguageDef}
    (membership : List.Mem rule language.terms) :
    List.Mem (mapGrammarRule symbols rule)
      (mapLanguageDef symbols language).terms :=
  List.mem_map_of_mem membership

theorem mem_equations_mapLanguageDef (symbols : LanguageDefSymbolMap)
    {equation : Equation} {language : LanguageDef}
    (membership : List.Mem equation language.equations) :
    List.Mem (mapEquation symbols equation)
      (mapLanguageDef symbols language).equations :=
  List.mem_map_of_mem membership

theorem mem_rewrites_mapLanguageDef (symbols : LanguageDefSymbolMap)
    {rewrite : RewriteRule} {language : LanguageDef}
    (membership : List.Mem rewrite language.rewrites) :
    List.Mem (mapRewriteRule symbols rewrite)
      (mapLanguageDef symbols language).rewrites :=
  List.mem_map_of_mem membership

/-- Sort-name membership (the `String`-in-`List TypeDecl` sense used by
`LangSort`) transports along the sort action. -/
theorem sortName_mem_mapLanguageDef (symbols : LanguageDefSymbolMap)
    {sortName : String} {language : LanguageDef}
    (membership : sortName ∈ language.types) :
    symbols.sort sortName ∈ (mapLanguageDef symbols language).types := by
  have named : sortName ∈ language.types.map (·.name) := membership
  obtain ⟨declaration, declarationMem, nameEq⟩ := List.mem_map.mp named
  show symbols.sort sortName ∈
    ((mapLanguageDef symbols language).types).map (·.name)
  refine List.mem_map.mpr
    ⟨mapTypeDecl symbols declaration,
      mem_types_mapLanguageDef symbols declarationMem, ?_⟩
  simp [mapTypeDecl, nameEq]

/-! ## Canaries -/

private def twoSortCanary : LanguageDef :=
  { name := "map-canary"
    types := [TypeDecl.plain "Data", TypeDecl.plain "Ctrl"]
    terms := []
    equations := []
    rewrites := [] }

private def markSorts : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with sort := fun sortName => sortName ++ "!" }

private def collapseSorts : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with sort := fun _ => "Point" }

/-- Positive canary: the image renames each authored sort declaration. -/
theorem mapLanguageDef_marks_sorts :
    (mapLanguageDef markSorts twoSortCanary).types =
      [TypeDecl.plain "Data!", TypeDecl.plain "Ctrl!"] := by decide

/-- Negative canary: a non-injective sort action collapses distinct authored
sorts onto one name, so the image of a valid presentation need not be valid.
This is why `StructuralMorphism` targets an independently validated
presentation rather than an automatically validated image. -/
theorem mapLanguageDef_can_break_validity :
    (mapLanguageDef collapseSorts twoSortCanary).validate ≠ [] := by
  intro validated
  have nodup :=
    LanguageDef.typeNames_nodup_of_validate_eq_nil _ validated
  exact absurd nodup (by decide)

#print axioms mapLanguageDef_id
#print axioms mapLanguageDef_comp
#print axioms sortName_mem_mapLanguageDef
#print axioms mapLanguageDef_can_break_validity

end Mettapedia.GSLT.LanguageDef
