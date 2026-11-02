import Mettapedia.Logic.HOL.IndexedChildHypotheses
import Mettapedia.Logic.HOL.FiniteConstructorGuardProofs
import Mettapedia.Logic.HOL.GuardedConstructorProjectionProofs

/-!
# Constructor admission from original shape and child obligations

The admission predicate retains the actual source shape guard and every
inactive-slot padding obligation. The complete original child condition
supplies its padding part without weakening or replacing the active-child
obligations in the source proof. Guarded projection recovery can consume this
predicate once its uniqueness law is independently established.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    (signature : Contextual Const Γ)

def paddingConditions (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) : Formula Const Γ :=
  .all (.imp (.not (.app (.app (weaken signature.active) (weaken payload)) (.var .vz)))
    (.eq (.app (weaken children) (.var .vz)) (weaken signature.bottom)))

@[simp] theorem subst_paddingConditions (substitution : Subst Const Γ Ξ)
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space)) :
    HOL.subst substitution (signature.paddingConditions payload children) =
      (signature.subst substitution).paddingConditions (HOL.subst substitution payload) (HOL.subst substitution children) := by
  simp [paddingConditions,Contextual.subst,HOL.subst,subst_weaken,Subst.lift]

def admissionBody : ArgumentBody Const Γ [signature.number,signature.payload,signature.number ⇒ signature.space] :=
  fun substitution arguments =>
    .and ((signature.subst substitution).shapeAt arguments.1 arguments.2.1)
      ((signature.subst substitution).paddingConditions arguments.2.1 arguments.2.2.1)

theorem admissionBody_natural : NaturalBody signature.admissionBody := by
  intro Δ Ξ earlier later arguments
  simp [admissionBody,shapeAt,paddingConditions,Contextual.subst,HOL.subst,subst_weaken,Subst.lift,subst_comp,
    substituteArguments]
  exact ⟨rfl,rfl,rfl⟩

private theorem subst_identity_arguments {type : Ty Base} (term : Term Const Γ type) :
    HOL.subst (fun {σ} (index : Var Γ σ) => Term.var index) term = term := subst_id term

def constructorAdmission : Term Const Γ
    (GuardedConstructorProjections.Admission signature.number signature.payload (signature.number ⇒ signature.space)) :=
  abstractArguments [signature.number,signature.payload,signature.number ⇒ signature.space] signature.admissionBody

variable {assumptions : List (Formula Const Γ)}

def constructorAdmission_at (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) :
    ProofSyntax Const assumptions (.eq
      (GuardedConstructorProjections.admitted signature.constructorAdmission tag payload children)
      (.and (signature.shapeAt tag payload) (signature.paddingConditions payload children))) := by
  have beta := abstractArguments_beta (assumptions := assumptions)
    [signature.number,signature.payload,signature.number ⇒ signature.space]
    signature.admissionBody signature.admissionBody_natural (tag,payload,children,PUnit.unit)
  apply ProofSyntax.castIndices rfl ?_ beta
  simp only [admissionBody,shapeAt,paddingConditions,Contextual.subst,subst_identity_arguments]
  rfl

def padding_of_children (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (conditions : ProofSyntax Const assumptions (signature.childConditions predicate payload children)) :
    ProofSyntax Const assumptions (signature.paddingConditions payload children) := by
  apply ProofSyntax.allI
  let shifted : Contextual Const (signature.number :: Γ) := signature.subst (Subst.ofRename Rename.weaken)
  have supplied : ProofSyntax Const (weakenHyps assumptions)
      (shifted.childConditions (weaken predicate) (weaken payload) (weaken children)) := by
    apply ProofSyntax.castIndices rfl ?_ (PredicateFixedPoint.weakenProof conditions)
    simpa only [shifted,subst_ofRename,weaken] using
      signature.subst_childConditions (Subst.ofRename Rename.weaken) predicate payload children
  apply ProofSyntax.castIndices rfl ?_
    (.andER (shifted.childConditions_at (weaken predicate) (weaken payload) (weaken children) (.var .vz) supplied))
  simp only [shifted,Contextual.subst,subst_ofRename,weaken]

def admission_from_children (predicate : Term Const Γ (signature.space ⇒ .prop))
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (shape : ProofSyntax Const assumptions (signature.shapeAt tag payload))
    (conditions : ProofSyntax Const assumptions (signature.childConditions predicate payload children)) :
    ProofSyntax Const assumptions (GuardedConstructorProjections.admitted signature.constructorAdmission tag payload children) :=
  .impE (.eqPropER (signature.constructorAdmission_at tag payload children))
    (.andI shape (signature.padding_of_children predicate payload children conditions))

theorem constructorAdmission_at_free (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) :
    (signature.constructorAdmission_at (assumptions := assumptions) tag payload children).FunctionExtensionalityFree := by
  unfold constructorAdmission_at
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

theorem padding_of_children_free (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (conditions : ProofSyntax Const assumptions (signature.childConditions predicate payload children))
    (free : conditions.FunctionExtensionalityFree) :
    (signature.padding_of_children predicate payload children conditions).FunctionExtensionalityFree := by
  unfold padding_of_children
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply childConditions_at_free
  simpa only [PredicateFixedPoint.weakenProof,ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_rename] using free

theorem admission_from_children_free (predicate : Term Const Γ (signature.space ⇒ .prop))
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (shape : ProofSyntax Const assumptions (signature.shapeAt tag payload))
    (conditions : ProofSyntax Const assumptions (signature.childConditions predicate payload children))
    (shapeFree : shape.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree) :
    (signature.admission_from_children predicate tag payload children shape conditions).FunctionExtensionalityFree :=
  ⟨signature.constructorAdmission_at_free tag payload children,shapeFree,
    signature.padding_of_children_free predicate payload children conditions conditionsFree⟩

#print axioms admission_from_children_free
end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
