import Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted

/-!
# Binder alpha semantics at the LanguageDef carrier boundary

Authored patterns retain binder display names for diagnostics and export.
Object-language binding is carried by de Bruijn indices, and every admitted
open or closed `LanguageDef` term requires canonical empty display metadata.

Consequently alpha-equivalence is handled once, before semantic admission:
source-preserving patterns are quotiented by
`Pattern.eraseBinderMetadata`, while the admitted carrier is its canonical
section.  There is no additional alpha equation generator inside the GSLT;
on admitted terms alpha-equivalence is exactly equality.
-/

namespace Mettapedia.GSLT.LanguageDef.BinderAlphaSemantics

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Generic open semantic terms contain exactly one representative of each
alpha class. -/
theorem openPattern_alphaEquiv_iff_eq
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (left right : WellSorted.OpenPattern language free bound type) :
    Pattern.AlphaEquiv left.1 right.1 ↔ left = right := by
  constructor
  · intro equivalent
    apply Subtype.ext
    exact (Pattern.alphaEquiv_iff_eq_of_canonical
      left.2.2.1 right.2.2.1).mp equivalent
  · intro equality
    subst right
    rfl

/-- Generic closed semantic terms contain exactly one representative of each
alpha class. -/
theorem closedTerm_alphaEquiv_iff_eq
    {language : LanguageDef} {sort : LangSort language}
    (left right : WellSorted.ClosedTerm language sort) :
    Pattern.AlphaEquiv left.1 right.1 ↔ left = right := by
  constructor
  · intro equivalent
    apply Subtype.ext
    exact (Pattern.alphaEquiv_iff_eq_of_canonical
      left.2.2.2.1 right.2.2.2.1).mp equivalent
  · intro equality
    subst right
    rfl

/-- Adding an admitted reflection profile does not reintroduce binder display
names into an open semantic term. -/
theorem reflectiveOpenPattern_alphaEquiv_iff_eq
    {profile : ReflectionProfile} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr}
    (left right : ReflectiveWellSorted.OpenPattern profile language free bound type) :
    Pattern.AlphaEquiv left.1 right.1 ↔ left = right := by
  constructor
  · intro equivalent
    apply Subtype.ext
    exact (Pattern.alphaEquiv_iff_eq_of_canonical
      left.2.1.2.1 right.2.1.2.1).mp equivalent
  · intro equality
    subst right
    rfl

/-- Adding an admitted reflection profile does not reintroduce binder display
names into a closed semantic term. -/
theorem reflectiveClosedTerm_alphaEquiv_iff_eq
    {profile : ReflectionProfile} {language : LanguageDef}
    {sort : LangSort language}
    (left right : ReflectiveWellSorted.ClosedTerm profile language sort) :
    Pattern.AlphaEquiv left.1 right.1 ↔ left = right := by
  constructor
  · intro equivalent
    apply Subtype.ext
    exact (Pattern.alphaEquiv_iff_eq_of_canonical
      left.2.1.2.2.1 right.2.1.2.2.1).mp equivalent
  · intro equality
    subst right
    rfl

/-- The canonical alpha representative really has canonical binder metadata;
this is the executable admission precondition used by every semantic carrier. -/
theorem alphaRepresentative_hasCanonicalBinderMetadata
    (equivalenceClass : Quotient Pattern.alphaSetoid) :
    (Pattern.alphaRepresentative equivalenceClass).hasCanonicalBinderMetadata = true := by
  refine Quotient.inductionOn equivalenceClass ?_
  intro pattern
  exact Pattern.eraseBinderMetadata_hasCanonicalBinderMetadata pattern

end Mettapedia.GSLT.LanguageDef.BinderAlphaSemantics

#print axioms Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.alphaRepresentative_spec
#print axioms Mettapedia.GSLT.LanguageDef.BinderAlphaSemantics.openPattern_alphaEquiv_iff_eq
#print axioms Mettapedia.GSLT.LanguageDef.BinderAlphaSemantics.closedTerm_alphaEquiv_iff_eq
#print axioms Mettapedia.GSLT.LanguageDef.BinderAlphaSemantics.reflectiveOpenPattern_alphaEquiv_iff_eq
#print axioms Mettapedia.GSLT.LanguageDef.BinderAlphaSemantics.reflectiveClosedTerm_alphaEquiv_iff_eq
#print axioms Mettapedia.GSLT.LanguageDef.BinderAlphaSemantics.alphaRepresentative_hasCanonicalBinderMetadata
