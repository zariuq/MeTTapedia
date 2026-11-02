import Mettapedia.Logic.HOL.FiniteConstructorFieldMaps
import Mettapedia.Logic.HOL.FiniteConstructorReadout

/-!
# Constructor-occurrence preserving maps between finite payload signatures

Each source occurrence has one target occurrence at the same ordinal and an
actual whole-row field program. Duplicate rows remain distinct occurrences.
The payload map abstracts the target handlers and precomposes each with its
row program. No inverse on arbitrary payload functions is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding
universe u v
variable {Base : Type u}

inductive InventoryMaps (Const : Ty Base → Type v) (Γ : Ctx Base) :
    List (List (Ty Base)) → List (List (Ty Base)) → Type (max u v) where
  | nil : InventoryMaps Const Γ [] []
  | cons {source target : List (Ty Base)} {sources targets : List (List (Ty Base))}
      (row : FieldMaps Const Γ source target) (rest : InventoryMaps Const Γ sources targets) :
      InventoryMaps Const Γ (source :: sources) (target :: targets)

namespace InventoryMaps
variable {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {source target : List (List (Ty Base))} {Δ : List (Formula Const Γ)}

def subst (images : Subst Const Γ Ξ) : {source target : List (List (Ty Base))} →
    InventoryMaps Const Γ source target → InventoryMaps Const Ξ source target
  | _,_,.nil => .nil
  | _,_,.cons row rest => .cons (row.subst images) (rest.subst images)

theorem length_eq (maps : InventoryMaps Const Γ source target) : source.length = target.length := by
  induction maps with
  | nil => rfl
  | cons row rest previous => exact congrArg Nat.succ previous

def occurrence (maps : InventoryMaps Const Γ source target) (index : Fin source.length) : Fin target.length :=
  ⟨index.val,maps.length_eq ▸ index.isLt⟩

@[simp] theorem occurrence_val (maps : InventoryMaps Const Γ source target) (index : Fin source.length) :
    (maps.occurrence index).val = index.val := rfl

def row : {source target : List (List (Ty Base))} → (maps : InventoryMaps Const Γ source target) →
    (index : Fin source.length) → FieldMaps Const Γ (source.get index) (target.get (maps.occurrence index))
  | _,_,.nil,index => Fin.elim0 index
  | _,_,.cons current _,⟨0,_⟩ => current
  | _,_,.cons _ rest,⟨index + 1,bound⟩ => rest.row ⟨index,Nat.lt_of_succ_lt_succ bound⟩

theorem occurrence_subst (maps : InventoryMaps Const Γ source target) (images : Subst Const Γ Ξ)
    (index : Fin source.length) : (maps.subst images).occurrence index = maps.occurrence index := by
  apply Fin.ext
  rfl

theorem row_subst (maps : InventoryMaps Const Γ source target) (images : Subst Const Γ Ξ)
    (index : Fin source.length) : (maps.subst images).row index = (maps.row index).subst images := by
  induction maps with
  | nil => exact Fin.elim0 index
  | cons current rest previous =>
      rcases index with ⟨index,bound⟩
      cases index with
      | zero => rfl
      | succ index => exact previous ⟨index,Nat.lt_of_succ_lt_succ bound⟩

theorem subst_weaken {type : Ty Base} (maps : InventoryMaps Const Γ source target)
    (images : Subst Const Γ Ξ) :
    (maps.subst (Subst.ofRename (Rename.weaken (σ := type)))).subst (Subst.lift images) =
      (maps.subst images).subst (Subst.ofRename Rename.weaken) := by
  induction maps with
  | nil => rfl
  | cons current rest previous =>
      exact congrArg₂ InventoryMaps.cons (current.subst_weaken images) previous

def mapPayload : {Γ : Ctx Base} → {source target : List (List (Ty Base))} → InventoryMaps Const Γ source target →
    Term Const Γ (payloadType source) → Term Const Γ (payloadType target)
  | _,_,_,.nil,payload => payload
  | _,_,_,.cons current rest,payload =>
      .lam ((rest.subst (Subst.ofRename Rename.weaken)).mapPayload
        (.app (weaken payload) ((current.subst (Subst.ofRename Rename.weaken)).precompose (.var .vz))))
termination_by _ source _ _ _ => source.length

theorem mapPayload_subst (maps : InventoryMaps Const Γ source target)
    (payload : Term Const Γ (payloadType source)) (images : Subst Const Γ Ξ) :
    HOL.subst images (maps.mapPayload payload) = (maps.subst images).mapPayload (HOL.subst images payload) := by
  induction source generalizing Γ Ξ target with
  | nil => cases maps; simp only [mapPayload,subst]
  | cons fields rest previous =>
      cases maps with
      | cons current remaining =>
          simp only [mapPayload,HOL.subst,previous,FieldMaps.precompose_subst,subst_weaken,
            FieldMaps.subst_weaken,subst]
          rw [HOL.subst_weaken]
          rfl

def mapPayload_congr : {Γ : Ctx Base} → {source target : List (List (Ty Base))} →
    {Δ : List (Formula Const Γ)} → (maps : InventoryMaps Const Γ source target) →
    (first second : Term Const Γ (payloadType source)) →
    ProofSyntax Const Δ (.eq first second) →
    ProofSyntax Const Δ (.eq (maps.mapPayload first) (maps.mapPayload second))
  | _,_,_,_,.nil,first,second,same =>
      ProofSyntax.castIndices rfl (by simp only [mapPayload]) same
  | _,_,_,_,.cons current remaining,first,second,same =>
      ProofSyntax.castIndices rfl (by simp only [mapPayload,HOL.weaken])
        (.eqLam (mapPayload_congr (remaining.subst (Subst.ofRename Rename.weaken)) _ _
          (.eqApp ((current.subst (Subst.ofRename Rename.weaken)).precompose (.var .vz)) (same.rename Rename.weaken))))
termination_by _ source _ _ _ _ _ _ => source.length

theorem mapPayload_congr_free (maps : InventoryMaps Const Γ source target)
    (first second : Term Const Γ (payloadType source))
    (same : ProofSyntax Const Δ (.eq first second)) (free : same.FunctionExtensionalityFree) :
    (maps.mapPayload_congr first second same).FunctionExtensionalityFree := by
  induction source generalizing Γ target with
  | nil =>
      cases maps
      simpa only [mapPayload_congr,ProofSyntax.functionExtensionalityFree_castIndices] using free
  | cons fields rest previous =>
      cases maps with
      | cons current remaining =>
          simpa only [mapPayload_congr,ProofSyntax.functionExtensionalityFree_castIndices,
            ProofSyntax.FunctionExtensionalityFree] using
            previous (remaining.subst (Subst.ofRename Rename.weaken)) _ _
              (.eqApp ((current.subst (Subst.ofRename Rename.weaken)).precompose (.var .vz)) (same.rename Rename.weaken))
              ((ProofSyntax.functionExtensionalityFree_rename _ _).mpr free)

#print axioms mapPayload_subst
#print axioms mapPayload_congr_free
end InventoryMaps
end Mettapedia.Logic.HOL.FiniteConstructorEncoding
