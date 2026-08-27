import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Conservative coproducts of validated language definitions

Independent operational presentations may be placed side by side after their
symbols are embedded into disjoint namespaces.  This module separates the raw
list construction from the proof that it is conservative:

* all four authored name families are globally duplicate-free;
* every mapped constructor, equation, and rewrite row remains valid when the
  other component's declarations are present.

The second condition is the capture/interference boundary.  It rules out the
subtle case where a newly added constructor name turns an existing schema
variable into a constructor-shaped wildcard collision.  Once these exact
conditions hold, validation of the union and both structural inclusions are
derived rather than postulated.
-/

namespace Mettapedia.GSLT.LanguageDef.StructuralCoproduct

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

/-- Rename every authored symbol of a language presentation while preserving
declaration order, concrete syntax, binding shape, and evaluation policy. -/
def renameLanguage (name : String) (symbols : PresentationSymbols)
    (language : LanguageDef) : LanguageDef := {
  name := name
  types := language.types.map (mapTypeDecl symbols)
  terms := language.terms.map (mapGrammarRule symbols)
  equations := language.equations.map (mapEquation symbols)
  rewrites := language.rewrites.map (mapRewriteRule symbols)
}

/-- Raw tagged union of two presentations.  Validation is deliberately not
part of this constructor; it is supplied only by `Compatibility.valid`. -/
def rawCoproduct (name : String)
    (leftSymbols rightSymbols : PresentationSymbols)
    (left right : LanguageDef) : LanguageDef :=
  let left' := renameLanguage (name ++ ".left") leftSymbols left
  let right' := renameLanguage (name ++ ".right") rightSymbols right
  { name := name
    types := left'.types ++ right'.types
    terms := left'.terms ++ right'.terms
    equations := left'.equations ++ right'.equations
    rewrites := left'.rewrites ++ right'.rewrites }

/-- Exact noninterference data for a proposed coproduct.  Global name
uniqueness prevents ambiguous declarations.  Row stability says that adding
the other component creates no capture, ambiguity, or dangling reference.
These are precisely the extra obligations not implied by validating the two
components separately. -/
structure Compatibility
    (name : String)
    (leftSymbols rightSymbols : PresentationSymbols)
    (left right : ValidatedLanguageDef) where
  typeNamesNodup :
    (rawCoproduct name leftSymbols rightSymbols left.language right.language).typeNames.Nodup
  constructorNamesNodup :
    ((rawCoproduct name leftSymbols rightSymbols left.language right.language).terms.map
      (·.label)).Nodup
  equationNamesNodup :
    ((rawCoproduct name leftSymbols rightSymbols left.language right.language).equations.map
      (·.name)).Nodup
  rewriteNamesNodup :
    ((rawCoproduct name leftSymbols rightSymbols left.language right.language).rewrites.map
      (·.name)).Nodup
  leftTermsStable : ∀ term ∈ left.language.terms,
    LanguageDef.validateTerm
      (rawCoproduct name leftSymbols rightSymbols left.language right.language)
      (mapGrammarRule leftSymbols term) = []
  rightTermsStable : ∀ term ∈ right.language.terms,
    LanguageDef.validateTerm
      (rawCoproduct name leftSymbols rightSymbols left.language right.language)
      (mapGrammarRule rightSymbols term) = []
  leftEquationsStable : ∀ equation ∈ left.language.equations,
    LanguageDef.validateEquation
      (rawCoproduct name leftSymbols rightSymbols left.language right.language)
      (mapEquation leftSymbols equation) = []
  rightEquationsStable : ∀ equation ∈ right.language.equations,
    LanguageDef.validateEquation
      (rawCoproduct name leftSymbols rightSymbols left.language right.language)
      (mapEquation rightSymbols equation) = []
  leftRewritesStable : ∀ rewrite ∈ left.language.rewrites,
    LanguageDef.validateRewrite
      (rawCoproduct name leftSymbols rightSymbols left.language right.language)
      (mapRewriteRule leftSymbols rewrite) = []
  rightRewritesStable : ∀ rewrite ∈ right.language.rewrites,
    LanguageDef.validateRewrite
      (rawCoproduct name leftSymbols rightSymbols left.language right.language)
      (mapRewriteRule rightSymbols rewrite) = []

namespace Compatibility

variable {name : String} {leftSymbols rightSymbols : PresentationSymbols}
  {left right : ValidatedLanguageDef}

/-- A compatible raw coproduct passes the ordinary `LanguageDef` validation
gate.  No component theorem is replaced: compatibility only proves that every
mapped row survives the larger signature unchanged. -/
theorem valid
    (compatible : Compatibility name leftSymbols rightSymbols left right) :
    (rawCoproduct name leftSymbols rightSymbols
      left.language right.language).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · exact compatible.typeNamesNodup
  · exact compatible.constructorNamesNodup
  · exact compatible.equationNamesNodup
  · exact compatible.rewriteNamesNodup
  · intro term membership
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      exact compatible.leftTermsStable source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      exact compatible.rightTermsStable source sourceMember
  · intro equation membership
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      exact compatible.leftEquationsStable source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      exact compatible.rightEquationsStable source sourceMember
  · intro rewrite membership
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      exact compatible.leftRewritesStable source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      exact compatible.rightRewritesStable source sourceMember

/-- The validated coproduct object determined by a compatibility witness. -/
def presentation
    (compatible : Compatibility name leftSymbols rightSymbols left right) :
    ValidatedLanguageDef where
  language := rawCoproduct name leftSymbols rightSymbols
    left.language right.language
  valid := compatible.valid

/-- Canonical structural inclusion of the left presentation. -/
def leftInclusion
    (compatible : Compatibility name leftSymbols rightSymbols left right) :
    StructuralMorphism left compatible.presentation where
  symbols := leftSymbols
  mapsTypes declaration membership := by
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨declaration, membership, rfl⟩)
  mapsTerms term membership := by
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨term, membership, rfl⟩)
  mapsEquations equation membership := by
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨equation, membership, rfl⟩)
  mapsRewrites rewrite membership := by
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨rewrite, membership, rfl⟩)

/-- Canonical structural inclusion of the right presentation. -/
def rightInclusion
    (compatible : Compatibility name leftSymbols rightSymbols left right) :
    StructuralMorphism right compatible.presentation where
  symbols := rightSymbols
  mapsTypes declaration membership := by
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨declaration, membership, rfl⟩)
  mapsTerms term membership := by
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨term, membership, rfl⟩)
  mapsEquations equation membership := by
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨equation, membership, rfl⟩)
  mapsRewrites rewrite membership := by
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨rewrite, membership, rfl⟩)

end Compatibility

#print axioms Compatibility.valid
#print axioms Compatibility.leftInclusion
#print axioms Compatibility.rightInclusion

end Mettapedia.GSLT.LanguageDef.StructuralCoproduct
