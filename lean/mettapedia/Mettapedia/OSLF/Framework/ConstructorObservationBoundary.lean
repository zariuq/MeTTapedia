import Mettapedia.GSLT.LanguageDef.IdentityComputationCalibration
import Mettapedia.OSLF.Framework.LanguagePresheafSharing

/-!
# Constructor presheaves do not determine authored identity computation

The native presheaf construction is language-dependent, but its constructor
category sees only sorts and unary crossings. The identity-computation
calibration supplies two authored presentations with the same constructor
data and different J-iota computation. This file tests exactly which
language-dependent native layer retains that distinction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.ConstructorObservationBoundary

open Mettapedia.GSLT.LanguageDef.IdentityComputationCalibration
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.LanguagePresheafSharing
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine

/-- The two presentations have the same sorts and unary-crossing input to
the constructor category. This does not identify their operational theories. -/
theorem withoutJ_withJ_same_constructor_inputs :
    withoutJ.types = withJ.types ∧
      unaryCrossings withoutJ = unaryCrossings withJ := by
  decide +kernel

/-- The proper J-iota redex is a real step of the operational presheaf
lambda theory, witnessed by the same authored rule and engine. -/
theorem withJ_native_iota :
    (languageOperationalLambdaTheory withJ).rewriteRel
      (constantProgramEndomorphism withJ properRedex)
      (constantProgramEndomorphism withJ base) := by
  apply languageOperationalLambdaTheoryUsing_constant_rewrite_of_exec
    RelationEnv.empty withJ (⟨"Tm", by decide⟩ : LangSort withJ)
  refine ⟨1, ?_⟩
  decide +kernel

/-- With the same constructor input but no authored J rule, that rewrite
is absent from the operational presheaf lambda theory. -/
theorem withoutJ_native_iota_absent :
    ¬ (languageOperationalLambdaTheory withoutJ).rewriteRel
      (constantProgramEndomorphism withoutJ properRedex)
      (constantProgramEndomorphism withoutJ base) := by
  intro native
  have semantic := (languageOperationalLambdaTheoryUsing_constant_rewrite_iff
    RelationEnv.empty withoutJ (⟨"Tm", by decide⟩ : LangSort withoutJ)
    properRedex base).mp native
  have primitive := (langSemanticReduces_iff_langReduces_of_equation_free
    (by decide +kernel) properRedex base).mp semantic
  exact (not_step_of_matchPatternForRule_eq_nil
    (base := engineBasePremises RelationEnv.empty)
    (lang := withoutJ) (source := properRedex) (target := base)
    (by
      intro rule member
      change rule ∈ ([] : List Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule) at member
      cases member)) primitive

/-- Selective identity computation remains selective after passing through
the language's operational presheaf theory. -/
theorem withJ_native_rejects_other_proof :
    ¬ (languageOperationalLambdaTheory withJ).rewriteRel
      (constantProgramEndomorphism withJ wrongProofRedex)
      (constantProgramEndomorphism withJ base) := by
  intro native
  have semantic := (languageOperationalLambdaTheoryUsing_constant_rewrite_iff
    RelationEnv.empty withJ (⟨"Tm", by decide⟩ : LangSort withJ)
    wrongProofRedex base).mp native
  have primitive := (langSemanticReduces_iff_langReduces_of_equation_free
    (by decide +kernel) wrongProofRedex base).mp semantic
  exact (not_step_of_matchPatternForRule_eq_nil
    (base := engineBasePremises RelationEnv.empty)
    (lang := withJ) (source := wrongProofRedex) (target := base)
    (by
      intro rule member
      let rule0 := withJ.rewrites[0]
      have single : withJ.rewrites = [rule0] := rfl
      rw [single] at member
      have equal : rule = rule0 := by simpa using member
      subst rule
      decide +kernel)) primitive

/-- An overbroad J rule is also visible to the operational presheaf
construction, despite sharing the same constructor-category input. -/
theorem malformedJ_native_accepts_other_proof :
    (languageOperationalLambdaTheory malformedJ).rewriteRel
      (constantProgramEndomorphism malformedJ wrongProofRedex)
      (constantProgramEndomorphism malformedJ base) := by
  apply languageOperationalLambdaTheoryUsing_constant_rewrite_of_exec
    RelationEnv.empty malformedJ (⟨"Tm", by decide⟩ : LangSort malformedJ)
  refine ⟨1, ?_⟩
  decide +kernel

end Mettapedia.OSLF.Framework.ConstructorObservationBoundary
