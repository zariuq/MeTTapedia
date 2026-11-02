import Mettapedia.Logic.HOL.FiniteConstructorPayloadMapComputations

/-!
# Typed function programs for finite payload maps

The program abstracts the original payload transformation. Its retained beta
proof computes exactly the original map, and typed substitution commutes with
the construction. No inverse or new representation condition is added.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding.InventoryMaps
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ Ω : Ctx Base}
  {source target : List (List (Ty Base))} {Δ : List (Formula Const Γ)}

theorem subst_comp (maps : InventoryMaps Const Γ source target)
    (first : Subst Const Γ Ξ) (later : Subst Const Ξ Ω) :
    (maps.subst first).subst later = maps.subst (Subst.comp later first) := by
  induction maps with
  | nil => rfl
  | cons row rest previous =>
      exact congrArg₂ InventoryMaps.cons (row.subst_comp first later) previous

theorem subst_identity (maps : InventoryMaps Const Γ source target) :
    maps.subst (fun {type} (index : Var Γ type) => Term.var index) = maps := by
  induction maps with
  | nil => rfl
  | cons row rest previous => exact congrArg₂ InventoryMaps.cons row.subst_identity previous

def program (maps : InventoryMaps Const Γ source target) :
    Term Const Γ (payloadType source ⇒ payloadType target) :=
  .lam ((maps.subst (Subst.ofRename Rename.weaken)).mapPayload (.var .vz))

theorem program_subst (maps : InventoryMaps Const Γ source target) (images : Subst Const Γ Ξ) :
    HOL.subst images maps.program = (maps.subst images).program := by
  simp only [program,HOL.subst,mapPayload_subst,subst_weaken,Subst.lift]

private theorem instantiate_body (maps : InventoryMaps Const Γ source target)
    (payload : Term Const Γ (payloadType source)) :
    instantiate payload ((maps.subst (Subst.ofRename Rename.weaken)).mapPayload (.var .vz)) =
      maps.mapPayload payload := by
  rw [instantiate,mapPayload_subst,subst_comp]
  have same : (Subst.comp (Subst.single payload) (Subst.ofRename Rename.weaken) : Subst Const Γ Γ) =
      (fun {type} (index : Var Γ type) => Term.var index) := by
    funext type index
    rfl
  rw [same,subst_identity]
  rfl

def program_beta (maps : InventoryMaps Const Γ source target)
    (payload : Term Const Γ (payloadType source)) :
    ProofSyntax Const Δ (.eq (.app maps.program payload) (maps.mapPayload payload)) :=
  ProofSyntax.castIndices rfl (congrArg (Term.eq _) (instantiate_body maps payload))
    (.beta payload ((maps.subst (Subst.ofRename Rename.weaken)).mapPayload (.var .vz)))

theorem program_beta_free (maps : InventoryMaps Const Γ source target)
    (payload : Term Const Γ (payloadType source)) :
    (maps.program_beta (Δ := Δ) payload).FunctionExtensionalityFree := by
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

#print axioms program_subst
#print axioms program_beta
#print axioms program_beta_free
end Mettapedia.Logic.HOL.FiniteConstructorEncoding.InventoryMaps

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding.FieldMaps
open CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {Δ : List (Formula Const Γ)}

def projectionBody (fields : List (Ty Base)) {type : Ty Base} (index : Var fields type) :
    FieldBody Const Γ fields type := fun _ arguments => argumentAt index arguments

theorem projectionBody_natural (fields : List (Ty Base)) {type : Ty Base} (index : Var fields type) :
    NaturalFieldBody (projectionBody (Const := Const) (Γ := Γ) fields index) := by
  intro Ξ Ω first later arguments
  exact argumentAt_subst later index arguments

def identity (fields : List (Ty Base)) : FieldMaps Const Γ fields fields where
  output index := abstractFields fields (projectionBody fields index)

theorem identity_subst (fields : List (Ty Base)) (images : Subst Const Γ Ξ) :
    (identity (Const := Const) (Γ := Γ) fields).subst images = identity fields := by
  apply congrArg FieldMaps.mk
  funext type index
  dsimp only [FieldMaps.subst,identity]
  rw [abstractFields_subst _ _ _ (projectionBody_natural fields index)]
  rfl

def identity_at (fields : List (Ty Base)) (arguments : Arguments Const Γ fields)
    {type : Ty Base} (index : Var fields type) :
    ProofSyntax Const Δ (.eq (argumentAt index ((identity fields).apply arguments)) (argumentAt index arguments)) := by
  apply ProofSyntax.castIndices rfl ?_
    (abstractFields_beta fields (projectionBody fields index) (projectionBody_natural fields index) arguments)
  exact congrArg (fun value => Term.eq value (argumentAt index arguments))
    (argumentAt_apply (identity fields) arguments index).symm

theorem identity_at_free (fields : List (Ty Base)) (arguments : Arguments Const Γ fields)
    {type : Ty Base} (index : Var fields type) :
    (identity_at (Δ := Δ) fields arguments index).FunctionExtensionalityFree := by
  unfold identity_at
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (abstractFields_beta_free _ _ _ _)

#print axioms identity_at
#print axioms identity_at_free
end Mettapedia.Logic.HOL.FiniteConstructorEncoding.FieldMaps
