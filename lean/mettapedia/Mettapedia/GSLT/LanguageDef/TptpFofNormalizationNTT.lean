import Mettapedia.GSLT.LanguageDef.TptpFofNormalizationLanguageDef
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.StructuralModal.Formula

/-!
# OSLF native types for the FOF normalization GSLT

The generated modal theory consumes the validated authored language.  The
positive example below is not a second normalizer: it derives a native type
from the same contextual step whose exact semantic implementation is proved
in `TptpFofNormalizationLanguageDef`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofNormalizationNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.StructuralModal
open Mettapedia.GSLT.LanguageDef.TptpFofNormalizationLanguageDef

theorem positive_request_crossing :
    ("tptp-fof-normalize:positive", "ResolvedFormula", "NNFFormula") ∈
      unaryCrossings language := by
  decide

theorem target_conjunction_constructor :
    ("tptp-fof-nnf:and", 2) ∈
      RewriteValidationCertificate.constructorSignatures language := by
  decide

theorem no_term_to_nnf_crossing :
    ("tptp-fof-normalize:invented", "Term", "NNFFormula") ∉
      unaryCrossings language := by
  decide

def normalizationOSLF := langOSLF language "NNFFormula"

theorem normalization_galois :
    GaloisConnection (langDiamond language) (langBox language) :=
  langGalois language

private def relation (name : String) : Pattern := a name
private def arguments : Pattern := a "tptp-fof-resolved:terms-nil"

def demoFormula : FormulaPattern :=
  .not (.implies (.predicate (relation "demo:p") arguments)
    (.predicate (relation "demo:q") arguments))

def demoSource : Pattern := request true demoFormula.source

def demoTarget : Pattern :=
  targetAnd
    (targetPositive (relation "demo:p") arguments)
    (targetNegative (relation "demo:q") arguments)

theorem demo_step_exact :
    rewriteAt (engineBasePremises RelationEnv.empty) language
        demoFormula.height demoSource = [demoTarget] := by
  simpa [demoFormula, demoSource, demoTarget, FormulaPattern.normalize,
    FormulaPattern.source, relation, arguments] using
    FormulaPattern.rewriteAt_exact demoFormula true demoFormula.height
      (by rfl)

def demoCompletionType : Formula :=
  .diamond (.headed "tptp-fof-nnf:and" [
    .headed "tptp-fof-nnf:positive" [.top, .top],
    .headed "tptp-fof-nnf:negative" [.top, .top]])

theorem demo_inhabits_derived_native_type :
    satisfies language demoCompletionType demoSource := by
  have executable : demoTarget ∈
      rewriteAt (engineBasePremises RelationEnv.empty) language
        demoFormula.height demoSource := by
    rw [demo_step_exact]
    simp
  have reduction : langReduces language demoSource demoTarget :=
    (langReducesUsing_iff_execUsing RelationEnv.empty language _ _).2
      ⟨demoFormula.height, executable⟩
  refine ⟨⟨(demoSource, demoTarget), reduction⟩, rfl, ?_⟩
  refine ⟨[
    targetPositive (relation "demo:p") arguments,
    targetNegative (relation "demo:q") arguments], rfl, ?_⟩
  constructor
  · refine ⟨[relation "demo:p", arguments], rfl, ?_⟩
    simp [satisfiesAllOver, satisfiesOver]
  · constructor
    · refine ⟨[relation "demo:q", arguments], rfl, ?_⟩
      simp [satisfiesAllOver, satisfiesOver]
    · trivial

#print axioms positive_request_crossing
#print axioms target_conjunction_constructor
#print axioms no_term_to_nnf_crossing
#print axioms normalization_galois
#print axioms demo_step_exact
#print axioms demo_inhabits_derived_native_type

end Mettapedia.GSLT.LanguageDef.TptpFofNormalizationNTT
