import Mettapedia.OSLF.Framework.LanguagePresheafSharing
import Mettapedia.OSLF.Framework.WMCalculusEncoding
import Mettapedia.OSLF.Framework.WMCalculusContextEncoding

/-!
# Typed WM steps in the shared operational presheaf lambda theory

The existing language-dependent operational lambda theory uses the same
internal OSLF reduction subfunctor as the authored `LanguageDef`. On constant
generalized programs, and only after fixing a real sort of the language, its
rewrite relation reflects the authored semantic one-step relation. Combined
with WM's typed encoding adequacy, this yields a biconditional on the image
of typed WM terms. The fixed presheaf sort here is `State` for every WM sort;
this is an exact operational-support comparison, not a sort-preserving
interpretation of the three-sorted WM syntax. It does not give a sorted
multi-argument categorical action or a free classifying universal property;
the four typed constructors are declared separately in the authored grammar.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusNativeOperationalSharing

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.LanguagePresheafSharing
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The core WM LanguageDef has an authored State sort and four typed
constructors. This chosen presheaf sort is still fixed to State. -/
def wmStateSort : LangSort wmCoreLanguageDef := ⟨"State", by decide⟩

/-- The typed one-step WM relation is exactly reduction of its encoded
constant programs in the existing operational presheaf lambda theory.
The restriction to typed images is essential: arbitrary raw patterns of
the LanguageDef need not decode as sorted WM terms. -/
theorem wmStep_iff_nativeOperationalRewrite {s : WMSort}
    (source target : WMTerm s) :
    WMStep source target ↔
      (languageOperationalLambdaTheory wmCoreLanguageDef).rewriteRel
        (constantProgramEndomorphism wmCoreLanguageDef (encodeWM source))
        (constantProgramEndomorphism wmCoreLanguageDef (encodeWM target)) := by
  exact (wmStep_iff source target).trans
    (languageOperationalLambdaTheoryUsing_constant_rewrite_iff
      Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
      wmCoreLanguageDef wmStateSort (encodeWM source) (encodeWM target)).symm

/-- The authored contextual presentation retains the same State sort after
adding congruence rules. -/
def wmContextStateSort :
    LangSort (wmExtVertexLanguageDefWithCong wmExtVertexMinimal) :=
  ⟨"State", by decide⟩

/-- Contextual WM computation also enters the existing operational
presheaf lambda theory exactly on encoded typed terms. This is the
step relation used by contextual subject reduction, not merely the
root-rule relation of the smaller core presentation. -/
theorem wmContextStep_iff_nativeOperationalRewrite {s : WMSort}
    (source target : WMTerm s) :
    Mettapedia.OSLF.Framework.WMCalculusContextEncoding.WMContextStep
      source target ↔
      (languageOperationalLambdaTheory
        (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)).rewriteRel
        (constantProgramEndomorphism
          (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
          (encodeWM source))
        (constantProgramEndomorphism
          (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
          (encodeWM target)) := by
  exact (Mettapedia.OSLF.Framework.WMCalculusContextEncoding.wmContextStep_iff
      source target).trans
    (languageOperationalLambdaTheoryUsing_constant_rewrite_iff
      Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
      (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      wmContextStateSort (encodeWM source) (encodeWM target)).symm

/-- A concrete typed WM step inhabits the operational lambda theory's
rewrite relation, so the biconditional is not merely about empty support. -/
theorem combineZero_nativeOperationalRewrite :
    (languageOperationalLambdaTheory wmCoreLanguageDef).rewriteRel
      (constantProgramEndomorphism wmCoreLanguageDef
        (encodeWM (WMTerm.combine WMTerm.zero WMTerm.zero)))
      (constantProgramEndomorphism wmCoreLanguageDef
        (encodeWM WMTerm.zero)) :=
  (wmStep_iff_nativeOperationalRewrite
    (WMTerm.combine WMTerm.zero WMTerm.zero) WMTerm.zero).mp
      (.combine_zero WMTerm.zero)

/-- An evidence-sorted WM term never encodes to a bare free variable. -/
theorem evidence_encoding_not_bare_variable
    (term : WMTerm .evidence) (variableName : String) :
    encodeWM term ≠ .fvar variableName := by
  cases term <;> simp [encodeWM, pExtract, pCombine, pEvidenceZero]

/-- The raw pattern language contains a Combine term whose left argument
cannot come from any evidence-sorted WM term. This witnesses why the
operational biconditional above is stated only on the typed image. -/
theorem raw_combine_outside_typed_evidence_image :
    ¬ ∃ term : WMTerm .evidence,
      encodeWM term = pCombine (.fvar "x") pEvidenceZero := by
  rintro ⟨term, encoded⟩
  cases term with
  | extract _ _ =>
      simp [encodeWM, pExtract, pCombine] at encoded
  | combine left _ =>
      have leftEncoded : encodeWM left = .fvar "x" :=
        (pCombine_injective encoded).1
      exact evidence_encoding_not_bare_variable left "x" leftEncoded
  | zero =>
      simp [encodeWM, pEvidenceZero, pCombine] at encoded

end Mettapedia.OSLF.Framework.WMCalculusNativeOperationalSharing
