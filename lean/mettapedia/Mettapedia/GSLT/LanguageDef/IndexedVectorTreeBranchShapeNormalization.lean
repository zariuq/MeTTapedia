import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeBranchActivity
import Mettapedia.Logic.HOL.FiniteConstructorPayloadMapComputations

/-!
# The admitted branch shape field equals its original zero code

The length remains independent of the shape field. Its original admission
proof supplies the shape equality; retained constructor-data congruence then
normalizes only that field. No occurrence, length or child array is changed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeBranchShapeNormalization
open Mettapedia.Logic Mettapedia.Logic.HOL
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {N A E : Ty Base}
  (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
  (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
  (zero one : ClosedTerm Const N) (tags : Nat → Term Const Γ N)
  {Δ : List (Formula Const Γ)}

@[irreducible] def shape (n q : Term Const Γ N)
    (admitted : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers zero one tags n q)) :
    ProofSyntax Const Δ (.eq q (weakenCtx Γ zero)) := by
  have compiled : ProofSyntax Const Δ (applyArguments [N,N]
      (IndexedVectorTreeStoredFieldGuards.compiledConditions given source numbers zero one
        ⟨1,by change 1 < 2; decide⟩) (n,q,PUnit.unit)) := by
    apply ProofSyntax.castIndices rfl ?_ admitted
    exact congrArg (fun condition => applyArguments [N,N] condition (n,q,PUnit.unit))
      (IndexedVectorTreeStoredFieldGuards.allowed_eq given source numbers zero one tags ⟨1,by change 1 < 2; decide⟩)
  exact .andEL (.andER (IndexedVectorTreeStoredFieldGuards.branchRead given source numbers zero one n q compiled))

theorem shape_free (n q : Term Const Γ N)
    (admitted : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers zero one tags n q))
    (free : admitted.FunctionExtensionalityFree) :
    (shape given source numbers zero one tags n q admitted).FunctionExtensionalityFree := by
  unfold shape
  apply IndexedVectorTreeStoredFieldGuards.branchRead_free
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

private def fieldEqualities (n q : Term Const Γ N)
    (equal : ProofSyntax Const Δ (.eq q (weakenCtx Γ zero))) :
    ∀ {type} (index : Var [N,N] type), ProofSyntax Const Δ
      (.eq (argumentAt index (n,q,PUnit.unit)) (argumentAt index (n,weakenCtx Γ zero,PUnit.unit)))
  | _, .vz => .eqRefl n
  | _, .vs .vz => equal
  | _, .vs (.vs index) => nomatch index

@[irreducible] def payload (n q : Term Const Γ N)
    (admitted : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers zero one tags n q)) :
    ProofSyntax Const Δ (.eq
      (IndexedVectorTreeBranchActivity.payload given source numbers zero one tags n q)
      (IndexedVectorTreeBranchActivity.payload given source numbers zero one tags n (weakenCtx Γ zero))) :=
  encode_congr (VectorTreeFieldEmbedding.storedSignature N E) ⟨1,by change 1 < 2; decide⟩
    (n,q,PUnit.unit) (n,weakenCtx Γ zero,PUnit.unit)
    (fieldEqualities zero n q (shape given source numbers zero one tags n q admitted))

theorem payload_free (n q : Term Const Γ N)
    (admitted : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers zero one tags n q))
    (free : admitted.FunctionExtensionalityFree) :
    (payload given source numbers zero one tags n q admitted).FunctionExtensionalityFree := by
  unfold payload
  apply encode_congr_free
  intro type index
  cases index with
  | vz => trivial
  | vs index => cases index with
    | vz => exact shape_free given source numbers zero one tags n q admitted free
    | vs index => cases index

#print axioms shape_free
#print axioms payload_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeBranchShapeNormalization
