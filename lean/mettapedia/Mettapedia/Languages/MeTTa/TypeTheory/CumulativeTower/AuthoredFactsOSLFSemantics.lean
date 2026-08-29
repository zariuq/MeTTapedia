import Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredConstantInference
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredEquationInference

/-!
# OSLF semantics of admitted authored facts

Authored constants and equations generate zero-premise rules only after their
source deltas pass the ordinary validated-extension boundary.  The source
inference modules already prove both directions needed at that boundary:
every generated table member has an accepted raw artifact, and every accepted
canonical fact reconstructs its exact source occurrence.

This module transports those results through calculus proof search into the
generated OSLF native type.  Reachability is therefore neither an unauthenticated
fact store nor a second source semantics: positive facts come from the admitted
inventory, and absence of source evidence is a generic negative criterion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace AuthoredFactsOSLFSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open AuthoredDeclarationSignature

/-! ## Authored constants -/

namespace Constant

open AuthoredConstantInference

/-- Every OSLF-reachable canonical constant fact reconstructs the active
first occurrence, its source position, and its displayed type. -/
theorem oslf_reflects_source
    {source : SourceDocument} (admitted : AdmittedFacts source)
    (claim : ConstantClaim)
    (satisfies :
      (gsltOSLF (proofSearchGSLT admitted.extension.target)).satisfies
        [encodeConstantClaim claim]
        (derivableNativeType admitted.extension.target).pred) :
    Nonempty (ConstantEvidence (elaborate source) claim) := by
  obtain ⟨derivation⟩ :=
    (satisfies_derivableNativeType_iff_derivation
      admitted.extension.target (encodeConstantClaim claim)).mp satisfies
  exact checkRaw_reflects_active_source admitted (checkRaw_erase derivation)

/-- Every exact member of the admitted generated table reaches the OSLF
native type through its canonical one-node derivation. -/
theorem generated_member_oslf
    {source : SourceDocument} (admitted : AdmittedFacts source)
    (ordinal : Nat) (active : ActiveConstant (elaborate source))
    (member : generatedRule ordinal active ∈
      generatedRules (elaborate source)) :
    (gsltOSLF (proofSearchGSLT admitted.extension.target)).satisfies
      [encodeConstantClaim active.claim]
      (derivableNativeType admitted.extension.target).pred := by
  apply (satisfies_derivableNativeType_iff_derivation
    admitted.extension.target _).2
  obtain ⟨derivation, _erases⟩ :=
    G2_checkRaw_iff_exists_derivation_erases_to.mp
      (admitted_generatedRule_raw_accepted admitted ordinal active member)
  exact ⟨derivation⟩

/-- A canonical constant claim with no authored source evidence cannot be
manufactured by OSLF proof search. -/
theorem not_oslf_of_no_sourceEvidence
    {source : SourceDocument} (admitted : AdmittedFacts source)
    (claim : ConstantClaim)
    (absent : ¬ Nonempty (ConstantEvidence (elaborate source) claim)) :
    ¬ (gsltOSLF (proofSearchGSLT admitted.extension.target)).satisfies
        [encodeConstantClaim claim]
        (derivableNativeType admitted.extension.target).pred := by
  intro satisfies
  exact absent (oslf_reflects_source admitted claim satisfies)

end Constant

/-! ## Authored equations -/

namespace Equation

open AuthoredEquationInference

/-- Every OSLF-reachable canonical equation fact reconstructs its exact
source declaration and both authored positions. -/
theorem oslf_reflects_source
    {source : SourceDocument} (admitted : AdmittedFacts source)
    (claim : EquationClaim)
    (satisfies :
      (gsltOSLF (proofSearchGSLT admitted.extension.target)).satisfies
        [encodeEquationClaim claim]
        (derivableNativeType admitted.extension.target).pred) :
    Nonempty (EquationEvidence (elaborate source) claim) := by
  obtain ⟨derivation⟩ :=
    (satisfies_derivableNativeType_iff_derivation
      admitted.extension.target (encodeEquationClaim claim)).mp satisfies
  exact checkRaw_reflects_equation_source admitted (checkRaw_erase derivation)

/-- Every exact admitted equation-table member reaches the OSLF native type
through its canonical one-node derivation. -/
theorem generated_member_oslf
    {source : SourceDocument} (admitted : AdmittedFacts source)
    (ordinal : Nat) (located : LocatedEquation (elaborate source))
    (member : generatedRule ordinal located ∈
      generatedRules (elaborate source)) :
    (gsltOSLF (proofSearchGSLT admitted.extension.target)).satisfies
      [encodeEquationClaim located.claim]
      (derivableNativeType admitted.extension.target).pred := by
  apply (satisfies_derivableNativeType_iff_derivation
    admitted.extension.target _).2
  obtain ⟨derivation, _erases⟩ :=
    G2_checkRaw_iff_exists_derivation_erases_to.mp
      (admitted_generatedRule_raw_accepted admitted ordinal located member)
  exact ⟨derivation⟩

/-- A canonical equation claim with no exact source path cannot be
manufactured by OSLF proof search. -/
theorem not_oslf_of_no_sourceEvidence
    {source : SourceDocument} (admitted : AdmittedFacts source)
    (claim : EquationClaim)
    (absent : ¬ Nonempty (EquationEvidence (elaborate source) claim)) :
    ¬ (gsltOSLF (proofSearchGSLT admitted.extension.target)).satisfies
        [encodeEquationClaim claim]
        (derivableNativeType admitted.extension.target).pred := by
  intro satisfies
  exact absent (oslf_reflects_source admitted claim satisfies)

end Equation

#print axioms Constant.oslf_reflects_source
#print axioms Constant.generated_member_oslf
#print axioms Constant.not_oslf_of_no_sourceEvidence
#print axioms Equation.oslf_reflects_source
#print axioms Equation.generated_member_oslf
#print axioms Equation.not_oslf_of_no_sourceEvidence

end AuthoredFactsOSLFSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
