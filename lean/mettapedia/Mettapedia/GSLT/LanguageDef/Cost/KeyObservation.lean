import Mettapedia.GSLT.LanguageDef.CanonicalSectionKeys
import Mettapedia.GSLT.LanguageDef.ContinuedCategory
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# Canonical-class observations of continued theories

The existing continued-theory key carrier is the exact key of a setoid
section.  These comparisons make its equation and observation contracts
explicit, before any optional digest is applied.
-/

namespace Mettapedia.GSLT.LanguageDef

namespace ComputableReflectiveFiberSection

/-- Restrict a reflective section to one exact typed fibre. -/
def toSetoidSection {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (canonical : ComputableReflectiveFiberSection theory reflection)
    (free : WellSorted.FreeTypeContext) (bound : List Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr)
    (sort : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort
      theory.presentation.presentation.language) :
    ComputableSetoidSection
      (ReflectiveWellSorted.OpenTerm reflection.1
        theory.presentation.presentation.language free bound sort)
      (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        reflection.1 defaultBasePremises
        theory.presentation.presentation.language free bound (.base sort.1)) where
  normalize := canonical.normalize
  equivalent := canonical.equivalent
  complete := canonical.complete

end ComputableReflectiveFiberSection

namespace CIGSLT

/-- The actual equation setoid of the closed, quote-safe interacting fibre. -/
abbrev canonicalEquationSetoid (theory : CIGSLT) : Setoid theory.CanonicalCarrier :=
  ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
    theory.reflection.1 defaultBasePremises theory.theory.presentation.presentation.language
    WellSorted.FreeTypeContext.empty [] (.base theory.theory.presentation.interactingLangSort.1)

/-- The existing canonicalizer as a generic setoid section. -/
def canonicalSetoidSection (theory : CIGSLT) :
    ComputableSetoidSection theory.CanonicalCarrier theory.canonicalEquationSetoid :=
  theory.canonical.toSetoidSection WellSorted.FreeTypeContext.empty []
    theory.theory.presentation.interactingLangSort

/-- Compute a key in the existing continued-theory carrier. -/
def canonicalKey (theory : CIGSLT) (term : theory.CanonicalCarrier) : theory.CanonicalKey :=
  theory.canonicalSetoidSection.key term

/-- Canonical keys classify the actual admitted equation classes exactly. -/
theorem canonicalKey_eq_iff (theory : CIGSLT) (left right : theory.CanonicalCarrier) :
    theory.canonicalKey left = theory.canonicalKey right ↔
      theory.canonicalEquationSetoid.r left right :=
  theory.canonicalSetoidSection.key_eq_iff left right

/-- The source's canonical-section digest necessarily respects equations. -/
theorem canonicalDigest_eq_of_equivalent (theory : CIGSLT) {Digest : Type*}
    (digest : theory.CanonicalKey → Digest) {left right : theory.CanonicalCarrier}
    (equivalent : theory.canonicalEquationSetoid.r left right) :
    digest (theory.canonicalKey left) = digest (theory.canonicalKey right) :=
  theory.canonicalSetoidSection.digest_eq_of_equivalent digest equivalent

/-- Translation before key formation agrees with the existing key action. -/
theorem Morphism.canonicalKey_natural {source target : CIGSLT}
    (morphism : Morphism source target) (term : source.CanonicalCarrier) :
    morphism.canonicalKeyMap (source.canonicalKey term) =
      target.canonicalKey (morphism.mapCanonicalTerm term) := by
  apply Subtype.ext
  change target.canonical.normalize
      (morphism.mapCanonicalTerm (source.canonical.normalize term)) =
    target.canonical.normalize (morphism.mapCanonicalTerm term)
  rw [← morphism.mapsCanonical, target.canonical.normalize_idempotent]

/-- Strict continued arrows reflect, as well as preserve, canonical-class
equality.  General account-merging maps need a separate comparison. -/
theorem Morphism.canonicalEquation_iff {source target : CIGSLT}
    (morphism : Morphism source target) (left right : source.CanonicalCarrier) :
    target.canonicalEquationSetoid.r (morphism.mapCanonicalTerm left)
      (morphism.mapCanonicalTerm right) ↔
      source.canonicalEquationSetoid.r left right := by
  rw [← target.canonicalKey_eq_iff, ← source.canonicalKey_eq_iff,
    ← morphism.canonicalKey_natural, ← morphism.canonicalKey_natural]
  exact morphism.canonicalKeyMap_injective.eq_iff

/-- Exact canonical keys are a functorial observation of continued theories.
This functor is not asserted to determine an entire presentation morphism. -/
def canonicalKeyFunctor : CategoryTheory.Functor CIGSLT (Type) where
  obj := CanonicalKey
  map morphism := TypeCat.ofHom morphism.canonicalKeyMap
  map_id theory := by
    apply CategoryTheory.ConcreteCategory.ext_apply
    intro key
    exact Morphism.canonicalKeyMap_id theory key
  map_comp first second := by
    apply CategoryTheory.ConcreteCategory.ext_apply
    intro key
    exact Morphism.canonicalKeyMap_comp first second key

/-- The monad unit gives a section of multiplication on the actual canonical
keys.  Surjectivity uses the monad law; it is not an assumption on the keys. -/
theorem canonicalMultiplication_surjective
    (transformer : CategoryTheory.Monad CIGSLT) (theory : CIGSLT) :
    Function.Surjective (transformer.μ.app theory).canonicalKeyMap := by
  intro key
  refine ⟨(transformer.η.app (transformer.obj theory)).canonicalKeyMap key, ?_⟩
  have unitLaw := congrArg
    (fun morphism : CIGSLT.Morphism (transformer.obj theory) (transformer.obj theory) =>
      morphism.canonicalKeyMap key) (transformer.left_unit theory)
  change (Morphism.comp _ _).canonicalKeyMap key =
    (Morphism.id _).canonicalKeyMap key at unitLaw
  simpa only [Morphism.canonicalKeyMap_comp, Morphism.canonicalKeyMap_id] using unitLaw

/-- Every monad on the existing strict category has bijective multiplication
on canonical keys.  A proposed multiplication that merges distinct such keys
therefore needs a different arrow contract.  This does not claim that all
other observations, or the whole monad, are idempotent. -/
theorem canonicalMultiplication_bijective
    (transformer : CategoryTheory.Monad CIGSLT) (theory : CIGSLT) :
    Function.Bijective (transformer.μ.app theory).canonicalKeyMap :=
  ⟨(transformer.μ.app theory).canonicalKeyMap_injective,
    canonicalMultiplication_surjective transformer theory⟩

end CIGSLT
end Mettapedia.GSLT.LanguageDef
