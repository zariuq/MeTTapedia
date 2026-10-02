import Mettapedia.GSLT.LanguageDef.CostSemanticSection
import Mettapedia.GSLT.LanguageDef.CostAuthoredAtom
import Mettapedia.GSLT.LanguageDef.Cost.KeyObservation
import Mettapedia.CategoryTheory.WriterActionSlice

/-!
# Original source commitments on a retained compiler image

The existing static insertion covers terms certified to use the cut-derived
non-principal constructor fragment.  This module compiles those closed source
terms into the existing semantic Cost carrier, proves that same-colour erasure
of the initial compact result recovers the complete authored term, and retains
that source as an index while semantic normalization evolves the Cost tree.

The image contains semantic-equation descendants of its actual compiler
output.  It is not the carrier of arbitrary neutral Cost syntax.  Its source
observation is the original base's whole closed canonical key, independently
of account wrappers.  Recovering an original source from an arbitrary Cost
term, covering interaction principals, constructing origin-grafting open
substitution, and applying the next Cost layer remain separate obligations.
-/

open CategoryTheory CategoryTheory.Category

namespace Mettapedia.GSLT.LanguageDef.Cost.SourceIndexedSemanticImage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.CategoryTheory

set_option autoImplicit false

/-- The actual static insertion domain.  Principals whose continuation
positions are retyped cannot be admitted by this uniform constructor action. -/
abbrev CertifiedSource (source : CIGSLT) :=
  { term : source.CanonicalCarrier //
    WellSorted.HasTypeWithConstructors
      source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels)
      WellSorted.FreeTypeContext.empty [] term.1
      (.base source.theory.presentation.interactingLangSort.1) }

/-- The existing generated static sort corresponding to the source's
interacting sort. -/
def imageSort (source : CIGSLT) (color : CostStaticColor) :
    LangSort source.costWholeLanguage :=
  color.mapLangSort source source.theory.presentation.interactingLangSort

/-- Actual declaration-derived insertion, with transported reflection scope. -/
def insert (source : CIGSLT) (color : CostStaticColor)
    (term : CertifiedSource source) :
    ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage WellSorted.FreeTypeContext.empty []
      (imageSort source color) := by
  let core := term.1.toCore.mapCostStatic term.2 color
  refine ⟨core.1, core.2, ?_⟩
  exact reflectiveScopeSafeAt_mapCostStatic source color term.1.2.2
    core.2.2.2.2

theorem insert_pattern (source : CIGSLT) (color : CostStaticColor)
    (term : CertifiedSource source) :
    (insert source color term).1 = mapPattern (color.symbols source) term.1.1 := rfl

/-- Initial insertion is lossless at the complete authored pattern. -/
theorem eraseColor_insert (source : CIGSLT) (color : CostStaticColor)
    (term : CertifiedSource source) :
    CostAuthoredAtomKey.eraseColor color (insert source color term).1 = term.1.1 :=
  CostAuthoredAtomKey.eraseColor_reifyAt source color term.1.1

/-- Compile the inserted term using the existing retained compiler. -/
def compile (source : CIGSLT) (safe : CostStaticCanonicalPathSafe source)
    (color : CostStaticColor) (term : CertifiedSource source) :
    CostSemanticElabTerm source WellSorted.FreeTypeContext.empty []
      (imageSort source color) :=
  CostSemanticOpenElaboration.compileTerm source safe (insert source color term)

/-- This concrete compiler's compact output retains the complete source. -/
theorem eraseColor_compile (source : CIGSLT)
    (safe : CostStaticCanonicalPathSafe source) (color : CostStaticColor)
    (term : CertifiedSource source) :
    CostAuthoredAtomKey.eraseColor color (compile source safe color term).1.1 =
      term.1.1 :=
  eraseColor_insert source color term

/-- Literal initial compiler output uniquely determines its certified source.
No reflection property of arbitrary Cost equations is asserted here. -/
theorem compile_injective (source : CIGSLT)
    (safe : CostStaticCanonicalPathSafe source) (color : CostStaticColor) :
    Function.Injective (compile source safe color) := by
  intro first second equality
  apply Subtype.ext
  apply Subtype.ext
  have decoded := congrArg
    (fun term => CostAuthoredAtomKey.eraseColor color term.1.1) equality
  simpa only [eraseColor_compile] using decoded

/-- The retained source index is backed by membership in the actual semantic
equation class of its computed compiler output. -/
structure Image (source : CIGSLT) (safe : CostStaticCanonicalPathSafe source)
    (color : CostStaticColor) (authored : CertifiedSource source) where
  retained : CostSemanticElabTerm source WellSorted.FreeTypeContext.empty []
    (imageSort source color)
  compiledEquivalent :
    (CostSemanticOpenElaboration.equationSetoid source
      WellSorted.FreeTypeContext.empty [] (imageSort source color)).r
      retained (compile source safe color authored)

/-- Source-indexed semantic compiler image, retaining original source code. -/
abbrev Carrier (source : CIGSLT) (safe : CostStaticCanonicalPathSafe source)
    (color : CostStaticColor) :=
  Σ authored : CertifiedSource source, Image source safe color authored

/-- Insert an actual source term into its computed semantic compiler image. -/
def ofSource (source : CIGSLT) (safe : CostStaticCanonicalPathSafe source)
    (color : CostStaticColor) (term : CertifiedSource source) :
    Carrier source safe color :=
  ⟨term, { retained := compile source safe color term
           compiledEquivalent := Relation.EqvGen.refl _ }⟩

/-- Preserve the original index while normalizing the retained tree in place.
The new image-membership proof is derived from an actual semantic edge. -/
def normalize {source : CIGSLT} {safe : CostStaticCanonicalPathSafe source}
    {color : CostStaticColor} (term : Carrier source safe color) :
    Carrier source safe color :=
  ⟨term.1, {
    retained := CostSemanticOpenElaboration.normalizeTerm term.2.retained
    compiledEquivalent := Relation.EqvGen.trans _ _ _
      (CostSemanticOpenElaboration.normalizeTerm_related term.2.retained)
      term.2.compiledEquivalent }⟩

/-- The selected original whole-source key, computed in the fixed base. -/
def sourceKey {source : CIGSLT} {safe : CostStaticCanonicalPathSafe source}
    {color : CostStaticColor} (term : Carrier source safe color) :
    source.CanonicalKey :=
  source.canonicalKey term.1.1

/-- Actual in-place evolution leaves the original whole-source observation
unchanged.  It does not compute a key of the new Cost wrapper. -/
theorem sourceKey_normalize {source : CIGSLT}
    {safe : CostStaticCanonicalPathSafe source} {color : CostStaticColor}
    (term : Carrier source safe color) : sourceKey (normalize term) = sourceKey term := rfl

/-- Initial image keys are exactly the admitted original source equation
classes, even though compilation preserves their distinct literal syntax. -/
theorem sourceKey_ofSource_eq_iff (source : CIGSLT)
    (safe : CostStaticCanonicalPathSafe source) (color : CostStaticColor)
    (first second : CertifiedSource source) :
    sourceKey (ofSource source safe color first) =
        sourceKey (ofSource source safe color second) ↔
      source.canonicalEquationSetoid.r first.1 second.1 :=
  source.canonicalKey_eq_iff first.1 second.1

/-- The constructed carrier instantiates the chosen observation slice with
the original base's whole canonical key, rather than its skeleton inventory. -/
def observedImage (source : CIGSLT) (safe : CostStaticCanonicalPathSafe source)
    (color : CostStaticColor) : Over source.CanonicalKey :=
  Over.mk (TypeCat.ofHom (@sourceKey source safe color))

/-- The actual in-place normalizer is a map over the source observation. -/
def normalizeObservedImage (source : CIGSLT)
    (safe : CostStaticCanonicalPathSafe source) (color : CostStaticColor) :
    observedImage source safe color ⟶ observedImage source safe color :=
  Over.homMk (TypeCat.ofHom (@normalize source safe color)) (by
    apply ConcreteCategory.ext_apply
    intro term
    exact sourceKey_normalize (safe := safe) term)

/-- Install free semantic accounts on the constructed source-indexed image. -/
def accountImage (M : Type) [Monoid M] (source : CIGSLT)
    (safe : CostStaticCanonicalPathSafe source) (color : CostStaticColor) :
    Over (Action.trivial M source.CanonicalKey) :=
  (WriterActionSlice.install M source.CanonicalKey).obj (observedImage source safe color)

theorem accountImage_observation (M : Type) [Monoid M] (source : CIGSLT)
    (safe : CostStaticCanonicalPathSafe source) (color : CostStaticColor)
    (account : M) (term : Carrier source safe color) :
    (accountImage M source safe color).hom.hom (account, term) =
      source.canonicalKey term.1.1 := rfl

#print axioms insert
#print axioms eraseColor_compile
#print axioms compile_injective
#print axioms normalize
#print axioms sourceKey_ofSource_eq_iff
#print axioms normalizeObservedImage

end Mettapedia.GSLT.LanguageDef.Cost.SourceIndexedSemanticImage
