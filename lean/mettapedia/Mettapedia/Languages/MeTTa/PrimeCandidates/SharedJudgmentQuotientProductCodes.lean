import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientProducts
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientUniverses
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentUniverseTypeCoherence

/-!
# Actual shared Pi/Sigma code meanings

The supplied native input codes and qualified comprehension comparison
determine the actual generated code value in the same formed quotient CwF.
Native result admission, code coverage, decoded-family meaning, and the
independently qualified constructor operation meet at that fixed universe.

The full input clauses are retained, including arbitrary universe-stability
witnesses and qualified comparisons. No total based-J operation or full
native-model witness is assumed. Code equality is that of this syntactic
model, not a global rule for observing source syntax.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientProductCodes

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive SharedJudgmentFragment
open FormationSensitiveContextual SharedJudgmentQuotientInterpretation
open SharedJudgmentQuotientUniverses (operations)
open SharedJudgmentUniverseTypeCoherence

variable {assembly : Assembly}

theorem pi_code_meaning : PiCodeMeaning (data assembly) (operations assembly) := by
  intro stable n source domain codomain lower upper extendedFormed
    domainCode nativeCode comparison domainAdmitted codomainAdmitted
    domainMeaning codomainMeaning comparisonMeaning
  have admitted := pi_admitted domainAdmitted codomainAdmitted
  obtain ⟨resultCode, resultMeaning⟩ :=
    SharedJudgmentQuotientUniverses.code_total n source (.pi domain codomain)
      (.max lower upper) admitted
  have resultDecoded := SharedJudgmentQuotientUniverses.codes_decode n source
    (.pi domain codomain) (.max lower upper) resultCode admitted resultMeaning
  have familyMeaning := decoded_family_meaning (data assembly) (operations assembly)
    stable SharedJudgmentQuotientUniverses.codes_decode domainAdmitted codomainAdmitted
    domainCode nativeCode comparison domainMeaning codomainMeaning comparisonMeaning
  have productMeaning := SharedJudgmentQuotientProducts.pi_formation_meaning n source
    domain codomain _ (family_admitted_at_sorts domainAdmitted codomainAdmitted) familyMeaning
  have sameType := type_meaning_unique resultDecoded productMeaning
  have sameCode : resultCode = (operations assembly).piCode domainCode
      (codomainCode (data assembly) (operations assembly) stable domainCode nativeCode comparison) := by
    apply QuotientUniverses.decode_injective
    exact sameType.trans (QuotientUniverseProducts.decode_piCode domainCode
      (codomainCode (data assembly) (operations assembly) stable domainCode nativeCode comparison)).symm
  exact sameCode ▸ resultMeaning

theorem sigma_code_meaning : SigmaCodeMeaning (data assembly) (operations assembly) := by
  intro stable n source domain codomain lower upper extendedFormed
    domainCode nativeCode comparison domainAdmitted codomainAdmitted
    domainMeaning codomainMeaning comparisonMeaning
  have admitted := sigma_admitted domainAdmitted codomainAdmitted
  obtain ⟨resultCode, resultMeaning⟩ :=
    SharedJudgmentQuotientUniverses.code_total n source (.sigma domain codomain)
      (.max lower upper) admitted
  have resultDecoded := SharedJudgmentQuotientUniverses.codes_decode n source
    (.sigma domain codomain) (.max lower upper) resultCode admitted resultMeaning
  have familyMeaning := decoded_family_meaning (data assembly) (operations assembly)
    stable SharedJudgmentQuotientUniverses.codes_decode domainAdmitted codomainAdmitted
    domainCode nativeCode comparison domainMeaning codomainMeaning comparisonMeaning
  have sumMeaning := SharedJudgmentQuotientProducts.sigma_formation_meaning n source
    domain codomain _ (family_admitted_at_sorts domainAdmitted codomainAdmitted) familyMeaning
  have sameType := type_meaning_unique resultDecoded sumMeaning
  have sameCode : resultCode = (operations assembly).sigmaCode domainCode
      (codomainCode (data assembly) (operations assembly) stable domainCode nativeCode comparison) := by
    apply QuotientUniverses.decode_injective
    exact sameType.trans (QuotientUniverseProducts.decode_sigmaCode domainCode
      (codomainCode (data assembly) (operations assembly) stable domainCode nativeCode comparison)).symm
  exact sameCode ▸ resultMeaning

namespace Controls

open SharedJudgmentInterpretation (Context)
open SharedJudgmentTypeInterpretation (ContextComparison ComprehensionMeaning)
open QuotientProductRepresentation.Controls (mixedFamily)

noncomputable section

def extended : Context common 1 :=
  Context.snoc .nil NativeWireData.dataType (.sort Tower.zero) Common.wireType.formed (.sort _)

def domainCode : QuotientUniverses.Code ((data common).ctx .nil) Tower.zero :=
  QuotientProductRepresentation.codeOfType Tower.zero Common.wireType rfl

def nativeCode : QuotientUniverses.Code ((data common).ctx extended) (.succ Tower.zero) :=
  QuotientProductRepresentation.codeOfType (.succ Tower.zero) mixedFamily rfl

theorem domain_meaning :
    (data common).term .nil NativeWireData.dataType (sortTm Tower.zero)
      (QuotientUniverses.univ ((data common).ctx .nil) Tower.zero) domainCode :=
  SharedJudgmentQuotientUniverses.code_meaning (assembly := common) .nil Tower.zero
    NativeWireData.dataType Common.wireType.formed

theorem codomain_meaning :
    (data common).term extended mixedFamily.code (sortTm (.succ Tower.zero))
      (QuotientUniverses.univ ((data common).ctx extended) (.succ Tower.zero)) nativeCode :=
  SharedJudgmentQuotientUniverses.code_meaning extended (.succ Tower.zero)
    mixedFamily.code mixedFamily.formed

/-- Altering the decoded product meaning to the native universe is rejected
by the actual interpretation graph, not just by a raw-syntax inequality. -/
theorem mixed_pi_universe_rejected :
    ¬ (data common).ty .nil (.pi NativeWireData.dataType mixedFamily.code)
      (QuotientUniverses.univ ((data common).ctx .nil) Tower.zero) := by
  intro changed
  have actual := QuotientInterpretation.type_meaning Common.context
    (QuotientProducts.nativePi Common.wireType mixedFamily)
  have same := type_meaning_unique (assembly := common) (source := .nil) actual changed
  have boundary := OpaqueRelatorExtension.pi_conversion_boundary HOLNativeRelatorCompatibility.opacity
  exact boundary.headDisjoint ((QType.mk_eq_iff _ _).mp same)

theorem mixed_sigma_universe_rejected :
    ¬ (data common).ty .nil (.sigma NativeWireData.dataType mixedFamily.code)
      (QuotientUniverses.univ ((data common).ctx .nil) Tower.zero) := by
  intro changed
  have actual := QuotientInterpretation.type_meaning Common.context
    (QuotientProducts.nativeSigma Common.wireType mixedFamily)
  have same := type_meaning_unique (assembly := common) (source := .nil) actual changed
  have boundary := OpaqueRelatorExtension.sigma_conversion_boundary HOLNativeRelatorCompatibility.opacity
  exact boundary.headDisjoint ((QType.mk_eq_iff _ _).mp same)

/-- The same common assembly supplies a real qualified comparison and both
actual generated code meanings for `Data` and the higher-level family
`Id Data x x`. Neither generated code can have the altered universe meaning. -/
theorem mixed_dependent_codes :
    ∃ comparison : ContextComparison (QuotientCwf.cwf common.rules)
        ((data common).ctx extended)
        (QuotientCwf.ext ((data common).ctx .nil) (QuotientUniverses.decode domainCode)),
      ComprehensionMeaning (data common) .nil NativeWireData.dataType extended.formed
        (QuotientUniverses.decode domainCode) comparison ∧
      let familyCode := codomainCode (data common) (operations common)
        SharedJudgmentQuotientUniverses.universe_substitution domainCode nativeCode comparison
      let product := QuotientUniverseProducts.piCode domainCode familyCode
      let sum := QuotientUniverseProducts.sigmaCode domainCode familyCode
      (data common).term .nil (.pi NativeWireData.dataType mixedFamily.code)
        (sortTm (.max Tower.zero (.succ Tower.zero)))
        (QuotientUniverses.univ ((data common).ctx .nil) (.max Tower.zero (.succ Tower.zero))) product ∧
      (data common).term .nil (.sigma NativeWireData.dataType mixedFamily.code)
        (sortTm (.max Tower.zero (.succ Tower.zero)))
        (QuotientUniverses.univ ((data common).ctx .nil) (.max Tower.zero (.succ Tower.zero))) sum ∧
      QuotientUniverses.decode product ≠ QuotientUniverses.univ ((data common).ctx .nil) Tower.zero ∧
      QuotientUniverses.decode sum ≠ QuotientUniverses.univ ((data common).ctx .nil) Tower.zero := by
  have domainAdmitted := Common.wireType.judgment
  have codomainAdmitted := mixedFamily.judgment
  have domainDecoded := SharedJudgmentQuotientUniverses.codes_decode 0 .nil
    NativeWireData.dataType Tower.zero domainCode domainAdmitted domain_meaning
  obtain ⟨comparison, comparisonMeaning⟩ := comprehension_coverage 0 .nil
    NativeWireData.dataType (.sort Tower.zero) (QuotientUniverses.decode domainCode)
    domainAdmitted (.sort _) domainDecoded
  have productMeaning := pi_code_meaning SharedJudgmentQuotientUniverses.universe_substitution
    0 .nil NativeWireData.dataType mixedFamily.code Tower.zero (.succ Tower.zero)
    domainCode nativeCode comparison domainAdmitted codomainAdmitted
    domain_meaning codomain_meaning comparisonMeaning
  have sumMeaning := sigma_code_meaning SharedJudgmentQuotientUniverses.universe_substitution
    0 .nil NativeWireData.dataType mixedFamily.code Tower.zero (.succ Tower.zero)
    domainCode nativeCode comparison domainAdmitted codomainAdmitted
    domain_meaning codomain_meaning comparisonMeaning
  refine ⟨comparison, comparisonMeaning, productMeaning, sumMeaning, ?_, ?_⟩
  · intro changed
    have meaning := SharedJudgmentQuotientUniverses.codes_decode 0 .nil
      (.pi NativeWireData.dataType mixedFamily.code) (.max Tower.zero (.succ Tower.zero)) _
      (pi_admitted (assembly := common) domainAdmitted codomainAdmitted) productMeaning
    exact mixed_pi_universe_rejected (changed ▸ meaning)
  · intro changed
    have meaning := SharedJudgmentQuotientUniverses.codes_decode 0 .nil
      (.sigma NativeWireData.dataType mixedFamily.code) (.max Tower.zero (.succ Tower.zero)) _
      (sigma_admitted (assembly := common) domainAdmitted codomainAdmitted) sumMeaning
    exact mixed_sigma_universe_rejected (changed ▸ meaning)

end
end Controls

#print axioms pi_code_meaning
#print axioms sigma_code_meaning
#print axioms Controls.mixed_dependent_codes
#print axioms Controls.mixed_pi_universe_rejected
#print axioms Controls.mixed_sigma_universe_rejected

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientProductCodes
