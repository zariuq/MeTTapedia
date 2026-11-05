import Mettapedia.Logic.HOL.VectorTabulationGuard
import Mettapedia.Logic.HOL.UniversalArgumentProofs

/-!
# Uniform retained assembly of bounded function membership

The point proof is supplied under every typed substitution. Universal
introduction and its proof-fragment property are established before a
particular element predicate is substituted into the construction.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.BoundedFunctionEvidence
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  (signature : IndexedVectorPredicate.Signature Const)
  (predicate : Term Const Γ (signature.element ⇒ .prop))
  (length : Term Const Γ signature.number) (array : Term Const Γ (signature.number ⇒ signature.element))

def body : ArgumentBody Const Γ [signature.number] := fun images fields =>
  .imp (.app (.app (weakenCtx _ (SuccessorOrder.less signature.successor)) fields.1) (HOL.subst images length))
    (.app (HOL.subst images predicate) (.app (HOL.subst images array) fields.1))

theorem body_natural : NaturalBody (body signature predicate length array) := by
  intro Ω Ψ earlier later fields
  simp only [body,HOL.subst,subst_weakenCtx,HOL.subst_comp,substituteArguments]
  rfl

variable {Δ : List (Formula Const Γ)}

@[irreducible] def introduce
    (branch : ArgumentProof Δ [signature.number] (body signature predicate length array)) :
    ProofSyntax Const Δ (VectorTabulation.Shifted.bounded signature predicate length array) := by
  apply ProofSyntax.castIndices rfl ?_ (forallArguments_intro _ _ branch)
  have shifted {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (fun index => Term.var (.vs index)) term = weaken (σ := signature.number) term :=
    subst_ofRename Rename.weaken term
  simp only [forallArguments,bindHead,body,Subst.id,VectorTabulation.Shifted.bounded,shifted]

theorem introduce_free
    (branch : ArgumentProof Δ [signature.number] (body signature predicate length array))
    (free : ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) fields,
      (branch images fields).FunctionExtensionalityFree) :
    (introduce signature predicate length array branch).FunctionExtensionalityFree := by
  unfold introduce
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact forallArguments_intro_free _ _ branch free

#print axioms introduce_free
end Mettapedia.Logic.HOL.BoundedFunctionEvidence
