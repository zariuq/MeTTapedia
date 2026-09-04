import Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory

/-!
# Extensionality for semantic NIK theory translations

Semantic translations contain data maps together with propositional scope and
meaning obligations.  Equality therefore depends only on the data maps.  This
lemma is the semantic counterpart of the existing extensionality theorem for
exact authority translations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory.TheoryTranslation

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe uKind uSignature uClaim

variable {SourceKind TargetKind : Type uKind}
    {source : TheoryFamily.{uSignature, uKind, uClaim} SourceKind}
    {target : TheoryFamily.{uSignature, uKind, uClaim} TargetKind}

/-- Semantic theory translations are determined by their transported data;
the commuting and preservation fields are propositions. -/
theorem ext_data
    {f g : NIKHeterogeneousTheory.TheoryTranslation source target}
    (kindEqual : forall kind, f.mapKind kind = g.mapKind kind)
    (signatureEqual : forall signature,
      f.mapSignature signature = g.mapSignature signature)
    (claimEqual : forall kind claim,
      HEq (f.mapClaim kind claim) (g.mapClaim kind claim)) :
    f = g := by
  cases f with
  | mk fKind fSignature fSignatureCommutes fClaim fScopePreserved
      fMeaningPreserved =>
    cases g with
    | mk gKind gSignature gSignatureCommutes gClaim gScopePreserved
        gMeaningPreserved =>
      simp only at kindEqual signatureEqual claimEqual
      have kindFunctionEqual : fKind = gKind := funext kindEqual
      subst kindFunctionEqual
      have signatureFunctionEqual : fSignature = gSignature :=
        funext signatureEqual
      subst signatureFunctionEqual
      have claimFunctionEqual : fClaim = gClaim :=
        funext fun kind => funext fun claim =>
          eq_of_heq (claimEqual kind claim)
      subst claimFunctionEqual
      rfl

end Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory.TheoryTranslation
