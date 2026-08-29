import Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareTypedConversion

/-!
# OSLF boundary for declaration-aware Prime typed conversion

The declaration-aware conversion calculus has a compositional intrinsic
semantics, so its generated OSLF native type is sound.  Its currently authored
generic rule image is deliberately smaller than Prime's intrinsic computation:
the checker contains reflexivity, while the native Pi calculus also constructs
typed beta conversion.

This module states that boundary exactly.  Reflexive formed typing reaches the
OSLF native type, every such reachability witness constructs intrinsic typed
conversion, and the existing nontrivial beta inhabitant proves that pointwise
exactness is impossible for the present rule set.  An untyped structural beta
receipt remains outside both the checked and intrinsic typed judgments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace DeclarationAwareConversionOSLFBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open DeclarationAwareTypedConversion

/-! ## Soundness of the current authored rule image -/

/-- The established proof-relevant conversion interpretation supplies the
semantic model of the generated OSLF reachability predicate. -/
noncomputable def conversionSoundModel :
    SoundModel typedConversionExtension.target
      (fun goal => Nonempty (PrimeConversionRootMeaning goal)) :=
  SoundModel.ofProofRelevant typedConversionSemanticExtension.targetSemantics

theorem oslf_sound (goal : Pattern)
    (satisfies :
      (gsltOSLF (proofSearchGSLT typedConversionExtension.target)).satisfies
        [goal] (derivableNativeType typedConversionExtension.target).pred) :
    Nonempty (PrimeConversionRootMeaning goal) :=
  conversionSoundModel.nativeTypeSound goal satisfies

/-- On a canonical conversion query, OSLF reachability constructs the exact
intrinsic typed-conversion fibre. -/
theorem oslf_implies_intrinsic (query : TypedConversionQuery)
    (satisfies :
      (gsltOSLF (proofSearchGSLT typedConversionExtension.target)).satisfies
        [encodeTypedConversionQuery query]
        (derivableNativeType typedConversionExtension.target).pred) :
    Nonempty (IntrinsicTypedConversion query) := by
  obtain ⟨meaning⟩ := oslf_sound (encodeTypedConversionQuery query) satisfies
  exact ⟨meaning.2 query rfl⟩

/-! ## Positive checked image -/

open DeclarationAwareTypedConversion.NativeExamples

/-- Complete formed typing crosses the authored reflexivity rule and reaches
the generated native type. -/
theorem simplePi_refl_oslf :
    (gsltOSLF (proofSearchGSLT typedConversionExtension.target)).satisfies
      [encodeTypedConversionQuery
        (TypedConversionQuery.refl
          DeclarationAwareFormedTyping.Examples.simplePiQuery)]
      (derivableNativeType typedConversionExtension.target).pred := by
  apply (satisfies_derivableNativeType_iff_derivation
    typedConversionExtension.target _).2
  obtain ⟨derivation, _erases⟩ :=
    G2_checkRaw_iff_exists_derivation_erases_to.mp simplePi_refl_checked
  exact ⟨derivation⟩

/-! ## Strict intrinsic capability and exactness obstruction -/

/-- Prime's native Pi calculus constructs a genuinely non-reflexive typed
beta conversion in the same intrinsic judgment family. -/
theorem beta_intrinsic : Nonempty (IntrinsicTypedConversion betaQuery) :=
  ⟨betaIntrinsic⟩

/-- The present authored proof-search calculus cannot derive that beta
inhabitant because its conversion rule image is diagonal. -/
theorem beta_not_oslf :
    ¬ (gsltOSLF (proofSearchGSLT typedConversionExtension.target)).satisfies
        [encodeTypedConversionQuery betaQuery]
        (derivableNativeType typedConversionExtension.target).pred := by
  rw [satisfies_derivableNativeType_iff_derivation]
  exact beta_has_no_checked_refl_derivation

/-- The complete heterogeneous semantic root is inhabited at the native beta
query.  Earlier judgment fibres are vacuous there by codec disjointness; the
conversion summand retains the actual typed beta path. -/
def betaRootSumMeaning :
    PrimeConversionRootSumMeaning (encodeTypedConversionQuery betaQuery) := by
  intro index equality
  rcases index with prior | query
  · exact False.elim (prior_conversion_images_disjoint prior betaQuery (by
      simpa [primeConversionRootCodec, sumOfDisjoint,
        typedConversionQueryCodec] using equality))
  · have same : query = betaQuery :=
      encodeTypedConversionQuery_injective (by
        simpa [primeConversionRootCodec, sumOfDisjoint,
          typedConversionQueryCodec] using equality)
    subst query
    exact betaIntrinsic

def betaRootMeaning :
    PrimeConversionRootMeaning (encodeTypedConversionQuery betaQuery) :=
  (primeConversionRootMeaning_equiv_sumFibre
    (encodeTypedConversionQuery betaQuery)).symm betaRootSumMeaning

/-- Therefore no pointwise exact model can identify the current generated
OSLF native type with the whole intrinsic Prime conversion meaning.  Adding
the missing operational conversion rules or explicitly retaining a strict
capability inclusion is a real language-design choice. -/
theorem no_exactModel_for_full_intrinsic_conversion :
    ¬ Nonempty
      (ExactModel typedConversionExtension.target
        (fun goal => Nonempty (PrimeConversionRootMeaning goal))) := by
  rintro ⟨model⟩
  exact beta_has_no_checked_refl_derivation
    (model.complete (encodeTypedConversionQuery betaQuery) ⟨betaRootMeaning⟩)

/-! ## Untyped computation does not mint typed meaning -/

/-- A raw structural beta receipt is insufficient: the ill-typed example
cannot reach the sound typed-conversion native type. -/
theorem illTypedBeta_not_oslf :
    ¬ (gsltOSLF (proofSearchGSLT typedConversionExtension.target)).satisfies
        [encodeTypedConversionQuery illTypedBetaQuery]
        (derivableNativeType typedConversionExtension.target).pred := by
  intro satisfies
  exact illTypedBetaQuery_has_no_intrinsic_conversion
    (oslf_implies_intrinsic illTypedBetaQuery satisfies)

#print axioms conversionSoundModel
#print axioms oslf_sound
#print axioms oslf_implies_intrinsic
#print axioms simplePi_refl_oslf
#print axioms beta_intrinsic
#print axioms beta_not_oslf
#print axioms betaRootMeaning
#print axioms no_exactModel_for_full_intrinsic_conversion
#print axioms illTypedBeta_not_oslf

end DeclarationAwareConversionOSLFBoundary
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
