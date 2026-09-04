import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclaredEquationStructuralAdmission
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SourceFactsOSLFSemantics
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareConversionOSLFBoundary

/-!
# Declared equation facts do not counterfeit typed computation

Every authored equation table now has a source-parametric structural
admission.  Its exact members reach the generated OSLF native type and reflect
back to source occurrences.  This layer remains conservative over Prime's
existing typed-conversion judgment, however, so authenticating equations does
not silently add object-language substitution or beta reduction.

The paired result below is the design boundary.  Declared facts are genuinely
operational, while Prime's existing intrinsic non-reflexive beta inhabitant
still lies strictly beyond the enlarged generic checker.  Closing that gap
requires either stronger authored conversion rules or an explicitly stronger
native capability; fact admission alone cannot decide between them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace DeclaredEquationConversionBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open AuthoredDeclarationSignature
open DeclaredEquationInference
open DeclaredEquationStructuralAdmission
open DeclarationAwareTypedConversion
open DeclarationAwareTypedConversion.NativeExamples

/-! ## Positive source-fact capability -/

/-- Every exact member of a source-parametric admitted equation table reaches
the enlarged OSLF native type. -/
theorem generated_equation_oslf
    (source : SourceDocument) (ordinal : Nat)
    (located : LocatedEquation (elaborate source))
    (member : generatedRule ordinal located ∈
      generatedRules (elaborate source)) :
    (gsltOSLF (proofSearchGSLT (structuralExtension source).target)).satisfies
      [encodeEquationClaim located.claim]
      (derivableNativeType (structuralExtension source).target).pred := by
  exact SourceFactsOSLFSemantics.Equation.generated_member_oslf
    (admitted source) ordinal located member

/-! ## Negative conversion-authority boundary -/

/-- Conservatively adjoining the authored equation judgment leaves the
non-reflexive beta query underivable.  The proof reflects the exact raw tree
back to the rooted typed-conversion presentation before applying its strict
capability obstruction. -/
theorem beta_not_derivable_after_declared_equations (source : SourceDocument) :
    ¬ Nonempty
      (Derivation (structuralExtension source).target
        (encodeTypedConversionQuery betaQuery)) := by
  rintro ⟨derivation⟩
  have targetAccepted := checkRaw_erase derivation
  have baseAccepted :=
    (typed_conversion_checkRaw_iff source betaQuery derivation.erase).mp
      targetAccepted
  obtain ⟨reflected, _erasure⟩ :=
    G2_checkRaw_iff_exists_derivation_erases_to.mp baseAccepted
  exact beta_has_no_checked_refl_derivation ⟨reflected⟩

/-- The same obstruction stated at the generated OSLF observation boundary. -/
theorem beta_not_oslf_after_declared_equations (source : SourceDocument) :
    ¬ (gsltOSLF
        (proofSearchGSLT (structuralExtension source).target)).satisfies
      [encodeTypedConversionQuery betaQuery]
      (derivableNativeType (structuralExtension source).target).pred := by
  rw [satisfies_derivableNativeType_iff_derivation]
  exact beta_not_derivable_after_declared_equations source

/-- Source authentication and intrinsic computation therefore remain strict,
independent capabilities after every structurally admitted equation table. -/
theorem intrinsic_beta_strict_after_declared_equations
    (source : SourceDocument) :
    Nonempty (IntrinsicTypedConversion betaQuery) ∧
      ¬ (gsltOSLF
          (proofSearchGSLT (structuralExtension source).target)).satisfies
        [encodeTypedConversionQuery betaQuery]
        (derivableNativeType (structuralExtension source).target).pred :=
  ⟨⟨betaIntrinsic⟩, beta_not_oslf_after_declared_equations source⟩

#print axioms generated_equation_oslf
#print axioms beta_not_derivable_after_declared_equations
#print axioms beta_not_oslf_after_declared_equations
#print axioms intrinsic_beta_strict_after_declared_equations

end DeclaredEquationConversionBoundary
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
