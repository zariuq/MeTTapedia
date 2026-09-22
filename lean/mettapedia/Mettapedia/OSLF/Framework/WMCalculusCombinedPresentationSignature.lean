import Mettapedia.GSLT.LanguageDef.BindingSignatureSameTerms
import Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralPresentation

/-!
# Intrinsic signature transport between the two combined WM presentations

The directed and structural-equation combined WM languages have exactly the
same authored constructor list. They differ in their equation and rewrite
inventories, so this file transports only their binding signatures, intrinsic
terms, and simultaneous substitution. Operational or equation transport must
be proved separately at the corresponding relation.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCombinedPresentationSignature

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralPresentation
open Mettapedia.OSLF.Framework.WMCalculusStructuralPresentation
open Mettapedia.OSLF.Framework.WMCalculusContextClosure

set_option autoImplicit false

theorem same_authored_constructors :
    (wmExtVertexLanguageDefGuarded combinedVertex).terms =
      combinedStructuralLanguageDef.terms := rfl

/-- The same constructor signature is not an operational identification:
directed evidence commutation is a rewrite in one presentation and only an
equation in the other. -/
theorem same_signature_different_directed_rule :
    ruleCombineComm ∈
        (wmExtVertexLanguageDefGuarded combinedVertex).rewrites ∧
      ruleCombineComm ∉ combinedStructuralLanguageDef.rewrites := by
  constructor
  · change ruleCombineComm ∈ coreRules ++ [ruleOverlapExtract] ++
      [ruleForgetOutsideGuarded, ruleForgetIdempotent]
    simp [coreRules]
  · intro member
    have named : ruleCombineComm.name ∈
        combinedStructuralLanguageDef.rewrites.map RewriteRule.name :=
      List.mem_map.mpr ⟨ruleCombineComm, member, rfl⟩
    have notNamed : ruleCombineComm.name ∉
        combinedStructuralLanguageDef.rewrites.map RewriteRule.name := by
      decide +kernel
    exact notNamed named

/-- A strict map of intrinsic signatures, not a structural language
morphism: it does not pretend that directed commutation is a target rewrite. -/
def directedToStructural :
    SigMor
      (signatureOf (wmExtVertexLanguageDefGuarded combinedVertex))
      (signatureOf combinedStructuralLanguageDef) :=
  signatureSameTerms same_authored_constructors

def structuralToDirected :
    SigMor (signatureOf combinedStructuralLanguageDef)
      (signatureOf (wmExtVertexLanguageDefGuarded combinedVertex)) :=
  signatureSameTerms same_authored_constructors.symm

/-- Changing the presentation and changing it back loses no operator, even
though the two rewrite systems are not being identified. -/
theorem directed_operator_roundtrip {sort : TypeExpr}
    (operator : (signatureOf (wmExtVertexLanguageDefGuarded combinedVertex)).Op sort) :
    structuralToDirected.opMap (directedToStructural.opMap operator) =
      operator :=
  Operator.ofSameTerms_symm same_authored_constructors operator

theorem directed_signature_roundtrip :
    directedToStructural.comp structuralToDirected =
      SigMor.ident (signatureOf (wmExtVertexLanguageDefGuarded combinedVertex)) :=
  signatureSameTerms_comp_ident same_authored_constructors

/-- The two WM presentations have the same intrinsic term carrier even though
one directs evidence commutation and the other makes it structural. -/
theorem directed_term_roundtrip
    {Γ : Ctx (signatureOf (wmExtVertexLanguageDefGuarded combinedVertex))}
    {sort : TypeExpr}
    (term : Term (signatureOf (wmExtVertexLanguageDefGuarded combinedVertex))
      Γ sort) :
    transportSameTerms same_authored_constructors.symm
      (transportSameTerms same_authored_constructors term) = term :=
  transportSameTerms_symm same_authored_constructors term

theorem structural_term_roundtrip
    {Γ : Ctx (signatureOf combinedStructuralLanguageDef)}
    {sort : TypeExpr}
    (term : Term (signatureOf combinedStructuralLanguageDef) Γ sort) :
    transportSameTerms same_authored_constructors
      (transportSameTerms same_authored_constructors.symm term) = term :=
  transportSameTerms_symm same_authored_constructors.symm term

/-- Presentation transport commutes with the *existing* generic simultaneous
substitution action, including the generic binding representation forms. -/
theorem transportTerm_bind
    {Γ Δ : Ctx (signatureOf (wmExtVertexLanguageDefGuarded combinedVertex))}
    (sigma : Sub (signatureOf (wmExtVertexLanguageDefGuarded combinedVertex)) Γ Δ)
    {sort : TypeExpr}
    (term : Term (signatureOf (wmExtVertexLanguageDefGuarded combinedVertex))
      Γ sort) :
    transportSameTerms same_authored_constructors (bind sigma term) =
      bind (fun sort position => transportSameTerms same_authored_constructors
        (sigma sort position))
        (transportSameTerms same_authored_constructors term) :=
  transportSameTerms_bind same_authored_constructors sigma term

#print axioms same_authored_constructors
#print axioms same_signature_different_directed_rule
#print axioms directedToStructural
#print axioms directed_operator_roundtrip
#print axioms directed_signature_roundtrip
#print axioms directed_term_roundtrip
#print axioms structural_term_roundtrip
#print axioms transportTerm_bind

end Mettapedia.OSLF.Framework.WMCalculusCombinedPresentationSignature
