import Mettapedia.GSLT.LanguageDef.BiformTheory
import Mettapedia.TypeTheory.ProofRelevantPathContextFunctor

/-!
# Dependent operational contexts of biform theories

The proof-relevant operational model of a biform theory generates a free path
context.  This composite is the precise bridge from theory translations to
dependent families indexed by retained operational histories.

The logical and authority projections remain separate: a theorem translation
does not determine how occurrence evidence is transported.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BiformDependentContext

open _root_.CategoryTheory
open scoped _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.BiformTheory
open Mettapedia.TypeTheory.ProofRelevantPathContextFunctor

universe uSignature uHom uSentence uTerm

variable {Signature : Type uSignature}
  [CategoryTheory.Category.{uHom} Signature]
  {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}

/-- Project a biform theory to its proof-relevant operational system and then
form the free category of finite occurrence histories. -/
def evidenceContext :
    BiformTheory.{uSignature, uHom, uSentence, uTerm} institution ⥤
      Cat.{uTerm, uTerm} :=
  BiformTheory.operationalProjection ⋙
    evidenceContextFunctor

#print axioms evidenceContext

end Mettapedia.GSLT.LanguageDef.BiformDependentContext
