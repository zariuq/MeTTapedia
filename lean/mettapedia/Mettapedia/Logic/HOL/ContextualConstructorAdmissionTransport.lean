import Mettapedia.Logic.HOL.ContextualConstructorAdmission

/-!
# Typed transport and shape extraction for constructor admission

Substitution acts on the actual admission program. Its retained beta proof
recovers the original shape at arbitrary target-context arguments, keeping
the supplied admission proof and all of its hypothesis occurrences.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  (signature : Contextual Const Γ)

theorem constructorAdmission_subst (images : Subst Const Γ Ξ) :
    HOL.subst images signature.constructorAdmission = (signature.subst images).constructorAdmission := by
  rw [constructorAdmission,abstractArguments_subst _ _ _ signature.admissionBody_natural]
  apply congrArg (abstractArguments [signature.number,signature.payload,signature.number ⇒ signature.space])
  funext Ω later arguments
  simp only [admissionBody,shapeAt,paddingConditions,Contextual.subst,HOL.subst_comp]
  rfl

def admissionShape {assumptions : List (Formula Const Γ)}
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      signature.constructorAdmission tag payload children)) :
    ProofSyntax Const assumptions (signature.shapeAt tag payload) :=
  .andEL (.impE (.eqPropEL (signature.constructorAdmission_at tag payload children)) present)

theorem admissionShape_free {assumptions : List (Formula Const Γ)}
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      signature.constructorAdmission tag payload children)) (presentFree : present.FunctionExtensionalityFree) :
    (signature.admissionShape tag payload children present).FunctionExtensionalityFree :=
  ⟨signature.constructorAdmission_at_free tag payload children,presentFree⟩

def admissionShapeSubst (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (tag : Term Const Ξ signature.number) (payload : Term Const Ξ signature.payload)
    (children : Term Const Ξ (signature.number ⇒ signature.space))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      (HOL.subst images signature.constructorAdmission) tag payload children)) :
    ProofSyntax Const assumptions (.app (.app (HOL.subst images signature.validShape) tag) payload) :=
  .andEL (.impE (.eqPropEL ((signature.subst images).constructorAdmission_at tag payload children))
    (ProofSyntax.castIndices rfl (congrArg
      (fun domain => GuardedConstructorProjections.admitted domain tag payload children)
      (signature.constructorAdmission_subst images)) present))

theorem admissionShapeSubst_free (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (tag : Term Const Ξ signature.number) (payload : Term Const Ξ signature.payload)
    (children : Term Const Ξ (signature.number ⇒ signature.space))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      (HOL.subst images signature.constructorAdmission) tag payload children))
    (presentFree : present.FunctionExtensionalityFree) :
    (signature.admissionShapeSubst images tag payload children present).FunctionExtensionalityFree :=
  ⟨(signature.subst images).constructorAdmission_at_free tag payload children,
    (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr presentFree⟩

#print axioms constructorAdmission_subst
#print axioms admissionShape
#print axioms admissionShape_free
#print axioms admissionShapeSubst
#print axioms admissionShapeSubst_free
end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
