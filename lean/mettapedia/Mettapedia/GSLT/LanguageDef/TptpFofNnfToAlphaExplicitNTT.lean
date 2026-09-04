import Mettapedia.GSLT.LanguageDef.TptpFofNnfToAlphaExplicitLanguageDef
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.StructuralModal.Formula

/-!
# OSLF native types for the NNF-to-alpha presentation transform

This modal theory is derived from the validated authored transformation.  It
does not add a naming algorithm: the exact execution theorem in the source
module already identifies the unique alpha-explicit result with the
independent semantic labeller.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofNnfToAlphaExplicitNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.StructuralModal
open Mettapedia.GSLT.LanguageDef.TptpFofNnfToAlphaExplicitLanguageDef

theorem resolved_variable_crossing :
    ("tptp-fof-resolved:term-variable", "TptpResolvedFof:Index",
      "TptpResolvedFof:Term") ∈ unaryCrossings language := by
  decide

theorem result_constructor_is_exact :
    ("tptp-fof-alpha-label:result", 4) ∈
      RewriteValidationCertificate.constructorSignatures language := by
  decide

theorem invented_crossing_is_absent :
    ("tptp-fof-alpha-label:invented", "NNFFormula",
      "TptpFofAlpha:Formula") ∉ unaryCrossings language := by
  decide

def alphaLabelingOSLF := langOSLF language "TptpFofAlpha:LabelingResult"

theorem alpha_labeling_galois :
    GaloisConnection (langDiamond language) (langBox language) :=
  langGalois language

noncomputable def nestedSource : Pattern :=
  TptpFofNnfLanguageDef.encodeFormula
    TptpFofAlphaExplicitNnf.Canary.nestedSource

noncomputable def nestedTarget : Pattern :=
  TptpFofAlphaExplicitNnfLanguageDef.encodeFormula
    (TptpFofAlphaExplicitNnf.label
      TptpFofAlphaExplicitNnf.Canary.nestedSource)

noncomputable def nestedRequest : Pattern :=
  request nestedSource
    (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId 0)

noncomputable def nestedResult : Pattern :=
  result nestedSource
    (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId 0)
    nestedTarget
    (TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId 2)

def nestedCompletionType : Formula :=
  .diamond (.headed "tptp-fof-alpha-label:result"
    [.top, .top, .top, .top])

theorem nested_step_exact :
    rewriteAt (engineBasePremises RelationEnv.empty) language
        (formulaHeight TptpFofAlphaExplicitNnf.Canary.nestedSource)
        nestedRequest = [nestedResult] := by
  simpa [nestedSource, nestedTarget, nestedRequest, nestedResult] using
    Canary.nested_execution_is_exact

theorem nested_inhabits_derived_native_type :
    satisfies language nestedCompletionType nestedRequest := by
  have executable : nestedResult ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language
        (formulaHeight TptpFofAlphaExplicitNnf.Canary.nestedSource)
        nestedRequest := by
    rw [nested_step_exact]
    simp
  have reduction : langReduces language nestedRequest nestedResult :=
    (langReducesUsing_iff_execUsing RelationEnv.empty language _ _).2
      ⟨formulaHeight TptpFofAlphaExplicitNnf.Canary.nestedSource, executable⟩
  refine ⟨⟨(nestedRequest, nestedResult), reduction⟩, rfl, ?_⟩
  refine ⟨[
    nestedSource,
    TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId 0,
    nestedTarget,
    TptpFofAlphaExplicitNnfLanguageDef.encodeBinderId 2], rfl, ?_⟩
  simp [satisfiesAllOver, satisfiesOver]

#print axioms resolved_variable_crossing
#print axioms result_constructor_is_exact
#print axioms invented_crossing_is_absent
#print axioms alpha_labeling_galois
#print axioms nested_step_exact
#print axioms nested_inhabits_derived_native_type

end Mettapedia.GSLT.LanguageDef.TptpFofNnfToAlphaExplicitNTT
