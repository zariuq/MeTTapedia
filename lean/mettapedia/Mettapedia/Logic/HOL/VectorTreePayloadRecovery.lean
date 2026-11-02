import Mettapedia.Logic.HOL.VectorTreePayloadMaps

/-!
# Guarded recovery for the complete solved/branch payload programs

The answer row keeps the direct image of its source predicate. The branch
row keeps its supplied two-field condition. Recovery is derived field by
field and then lifted through the existing constructor-data guard; no
inverse on arbitrary payload functions is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.VectorTreePayloadMaps
open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {N A E : Ty Base} {Δ : List (Formula Const Γ)}

def conditions (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (predicate : Term Const Γ (A ⇒ .prop)) (branch : Term Const Γ (handlerType [N,N])) :
    ConstructorDataPredicates.Conditions Const Γ (VectorTreeFieldEmbedding.storedSignature N E)
  | ⟨0,_⟩ => given.predicate predicate
  | ⟨1,_⟩ => branch

theorem conditions_subst (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (predicate : Term Const Γ (A ⇒ .prop)) (branch : Term Const Γ (handlerType [N,N]))
    (images : Subst Const Γ Ξ) (index : Fin (VectorTreeFieldEmbedding.storedSignature N E).length) :
    HOL.subst images (conditions given predicate branch index) =
      conditions (given.substitute images) (HOL.subst images predicate) (HOL.subst images branch) index := by
  rcases index with ⟨index,bound⟩
  match index with
  | 0 => exact given.predicate_subst images predicate
  | 1 => rfl

private theorem leftInverse_subst {source target : Ty Base}
    (encode : Term Const Γ (source ⇒ target)) (decode : Term Const Γ (target ⇒ source))
    (images : Subst Const Γ Ξ) :
    HOL.subst images (ConstructorFieldRepresentation.leftInverse encode decode) =
      ConstructorFieldRepresentation.leftInverse (HOL.subst images encode) (HOL.subst images decode) := by
  simp only [ConstructorFieldRepresentation.leftInverse,HOL.subst,subst_weaken,Subst.lift]

def rowRoundtrip (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (predicate : Term Const Γ (A ⇒ .prop)) (branch : Term Const Γ (handlerType [N,N]))
    (law : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode))
    (index : Fin (VectorTreeFieldEmbedding.storedSignature N E).length)
    (arguments : Arguments Const Γ ((VectorTreeFieldEmbedding.storedSignature N E).get index))
    (member : ProofSyntax Const Δ (applyArguments _ (conditions given predicate branch index) arguments))
    {type : Ty Base} (field : Var ((VectorTreeFieldEmbedding.storedSignature N E).get index) type) :
    ProofSyntax Const Δ (.eq
      (argumentAt field (InventoryMaps.returnedArguments (lower given) (raise given) index arguments))
      (argumentAt field arguments)) := by
  rcases index with ⟨index,bound⟩
  match index with
  | 0 =>
      cases field with
      | vz =>
          exact ConstructorPredicateRepresentation.recover _ _ _ arguments.1 law member
      | vs impossible => nomatch impossible
  | 1 =>
      change ProofSyntax Const Δ (.eq
        (argumentAt field ((FieldMaps.identity [N,N]).apply ((FieldMaps.identity [N,N]).apply arguments)))
        (argumentAt field arguments))
      exact .eqTrans (FieldMaps.identity_at [N,N] _ field) (FieldMaps.identity_at [N,N] arguments field)

theorem rowRoundtrip_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (predicate : Term Const Γ (A ⇒ .prop)) (branch : Term Const Γ (handlerType [N,N]))
    (law : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode))
    (index : Fin (VectorTreeFieldEmbedding.storedSignature N E).length)
    (arguments : Arguments Const Γ ((VectorTreeFieldEmbedding.storedSignature N E).get index))
    (member : ProofSyntax Const Δ (applyArguments _ (conditions given predicate branch index) arguments))
    {type : Ty Base} (field : Var ((VectorTreeFieldEmbedding.storedSignature N E).get index) type)
    (lawFree : law.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (rowRoundtrip given predicate branch law index arguments member field).FunctionExtensionalityFree := by
  rcases index with ⟨index,bound⟩
  match index with
  | 0 =>
      cases field with
      | vz =>
          exact ConstructorPredicateRepresentation.recover_free _ _ _ _ _ _ lawFree memberFree
      | vs impossible => nomatch impossible
  | 1 => exact ⟨FieldMaps.identity_at_free _ _ _,FieldMaps.identity_at_free _ _ _⟩

def rowRecovery (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (predicate : Term Const Γ (A ⇒ .prop)) (branch : Term Const Γ (handlerType [N,N]))
    (law : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode)) :
    InventoryMaps.RowRecovery Δ (lower given) (raise given) (conditions given predicate branch) := by
  intro Ξ images assumptions transport index arguments member type field
  have currentLaw : ProofSyntax Const assumptions
      (ConstructorFieldRepresentation.leftInverse (given.substitute images).encode (given.substitute images).decode) :=
    .castIndices rfl (by rw [leftInverse_subst,given.encode_subst,given.decode_subst])
      (ProofSyntax.mono transport (law.subst images))
  have present : ProofSyntax Const assumptions (applyArguments _
      (conditions (given.substitute images) (HOL.subst images predicate) (HOL.subst images branch) index) arguments) :=
    .castIndices rfl (congrArg (fun condition => applyArguments _ condition arguments)
      (conditions_subst given predicate branch images index)) member
  exact .castIndices rfl (by rw [lower_subst,raise_subst])
    (rowRoundtrip (given.substitute images) (HOL.subst images predicate) (HOL.subst images branch)
      currentLaw index arguments present field)

theorem rowRecovery_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (predicate : Term Const Γ (A ⇒ .prop)) (branch : Term Const Γ (handlerType [N,N]))
    (law : ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse given.encode given.decode))
    (lawFree : law.FunctionExtensionalityFree) : InventoryMaps.RowRecovery.Free (rowRecovery given predicate branch law) := by
  intro Ξ images assumptions transport index arguments member memberFree type field
  unfold rowRecovery
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply rowRoundtrip_free
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr
        ((ProofSyntax.functionExtensionalityFree_subst _ _).mpr lawFree))
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr memberFree

def recover (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (predicate : Term Const Γ (A ⇒ .prop)) (branch : Term Const Γ (handlerType [N,N]))
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective given.raw))
    (payload : Term Const Γ (payloadType (VectorTreeFieldEmbedding.storedSignature N E)))
    (present : ProofSyntax Const Δ (ConstructorDataPredicates.guard _ (conditions given predicate branch) payload)) :
    ProofSyntax Const Δ (.eq (.app (raiseProgram given) (.app (lowerProgram given) payload)) payload) :=
  .eqTrans (.eqAppArg (raiseProgram given) ((lower given).program_beta payload))
    (.eqTrans ((raise given).program_beta ((lower given).mapPayload payload))
      (InventoryMaps.guardedRoundtrip (lower given) (raise given) (conditions given predicate branch)
        (rowRecovery given predicate branch (given.roundtripLaw payloadChoice fieldChoice injectivity)) payload present))

theorem recover_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (predicate : Term Const Γ (A ⇒ .prop)) (branch : Term Const Γ (handlerType [N,N]))
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective given.raw))
    (payload : Term Const Γ (payloadType (VectorTreeFieldEmbedding.storedSignature N E)))
    (present : ProofSyntax Const Δ (ConstructorDataPredicates.guard _ (conditions given predicate branch) payload))
    (payloadFree : payloadChoice.FunctionExtensionalityFree) (fieldFree : fieldChoice.FunctionExtensionalityFree)
    (constructorFree : injectivity.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (recover given predicate branch payloadChoice fieldChoice injectivity payload present).FunctionExtensionalityFree := by
  exact ⟨InventoryMaps.program_beta_free _ _,InventoryMaps.program_beta_free _ _,
    InventoryMaps.guardedRoundtrip_free _ _ _ _ _ _
      (rowRecovery_free _ _ _ _ (given.roundtripLaw_free _ _ _ payloadFree fieldFree constructorFree)) presentFree⟩

#print axioms rowRecovery
#print axioms rowRecovery_free
#print axioms recover
#print axioms recover_free
end Mettapedia.Logic.HOL.VectorTreePayloadMaps
