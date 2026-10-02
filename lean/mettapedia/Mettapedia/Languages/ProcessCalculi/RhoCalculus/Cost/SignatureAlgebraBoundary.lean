import Mettapedia.GSLT.LanguageDef.Cost.KeyObservation
import Mettapedia.Languages.MeTTa.PrimeCandidates.SelectedCostLayerIterationBoundary

/-!
# The generated signature syntax does not impose the monoid unit law

Two closed signed zero programs in the selected first Cost layer distinguish
the signature unit from its binary product with itself after canonicalization.
Thus the monoid unit equation is not part of this generated equation theory.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SignatureAlgebraBoundary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.MeTTa.PrimeCandidates.SelectedCostLayerIterationBoundary
open LanguageDefContinuedInteraction

noncomputable section

abbrev source : CIGSLT := rhoSelectedCostLayerConfiguration.source

def unitSignature : Pattern := .apply costSignatureUnitConstructorName []

def productSignature : Pattern :=
  .apply costSignatureProductConstructorName [unitSignature, unitSignature]

def signedZero (signature : Pattern) : Pattern :=
  .apply costSignedConstructorName
    [.apply (costBaseConstructorName "PZero") [], signature]

theorem signedZero_unit_typed :
    HasType source.theory.presentation.presentation.language
      FreeTypeContext.empty [] (signedZero unitSignature)
      (.base costWrappedSortName) := by
  exact checkHasType_sound (by decide +kernel)

theorem signedZero_product_typed :
    HasType source.theory.presentation.presentation.language
      FreeTypeContext.empty [] (signedZero productSignature)
      (.base costWrappedSortName) := by
  exact checkHasType_sound (by decide +kernel)

def unitTerm : source.CanonicalCarrier := by
  refine ⟨signedZero unitSignature,
    ⟨⟨signedZero_unit_typed, rfl, rfl,
      signedZero_unit_typed.isWellScopedAt⟩, ?_⟩⟩
  intro declaration membership
  simp [signedZero, unitSignature, binderSafeAt, binderSafeListAt]

def productTerm : source.CanonicalCarrier := by
  refine ⟨signedZero productSignature,
    ⟨⟨signedZero_product_typed, rfl, rfl,
      signedZero_product_typed.isWellScopedAt⟩, ?_⟩⟩
  intro declaration membership
  simp [signedZero, productSignature, unitSignature, binderSafeAt, binderSafeListAt]

private def wrappedSort : LangSort rhoCIGSLT.costWholeLanguage :=
  ⟨costWrappedSortName, rhoCIGSLT.costWrappedSortName_mem_costWhole⟩

private def unitCompact :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] wrappedSort := unitTerm

private def productCompact :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] wrappedSort := productTerm

theorem unitTerm_normalized :
    (source.canonical.normalize unitTerm).1 = signedZero unitSignature := by
  change (rhoCostNormalizeOpenHereditarySupported unitCompact).1 = _
  rw [CostIterationObstruction.rhoCostNormalizeOpenHereditarySupported_eq_hereditary_on_closed]
  decide +kernel

theorem productTerm_normalized :
    (source.canonical.normalize productTerm).1 = signedZero productSignature := by
  change (rhoCostNormalizeOpenHereditarySupported productCompact).1 = _
  rw [CostIterationObstruction.rhoCostNormalizeOpenHereditarySupported_eq_hereditary_on_closed]
  decide +kernel

/-- The selected source section computes different canonical keys for the
two admitted signed programs. No injectivity assumption about raw syntax or
about a digest is used. -/
theorem signature_unit_product_keys_distinct :
    source.canonicalKey unitTerm ≠ source.canonicalKey productTerm := by
  intro same
  have patterns := congrArg (fun key : source.CanonicalKey => key.1.1) same
  change (source.canonical.normalize unitTerm).1 =
    (source.canonical.normalize productTerm).1 at patterns
  rw [unitTerm_normalized, productTerm_normalized] at patterns
  simp [signedZero, unitSignature, productSignature] at patterns

/-- In particular, adjoining only the signature constructors has not
identified multiplication by the unit with the original signature, even in
this closed admitted context. -/
theorem signature_unit_product_not_equivalent :
    ¬ source.canonicalEquationSetoid.r unitTerm productTerm := by
  intro equivalent
  exact signature_unit_product_keys_distinct
    ((source.canonicalKey_eq_iff unitTerm productTerm).mpr equivalent)

#print axioms signature_unit_product_keys_distinct
#print axioms signature_unit_product_not_equivalent

end

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SignatureAlgebraBoundary
