import Mettapedia.Logic.HOL.VectorTreeFieldEmbedding
import Mettapedia.Logic.HOL.FiniteConstructorPayloadPrograms
import Mettapedia.Logic.HOL.FiniteConstructorPayloadRetraction

/-!
# Payload maps over the complete solved/branch inventory

Only the unary answer field changes carrier. Both numeric branch fields and
both constructor ordinals are retained. The maps are actual curried programs,
not inverses supplied for an ambient payload function space.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.VectorTreePayloadMaps
open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {N A E : Ty Base}

def unary {source target : Ty Base} (function : Term Const Γ (source ⇒ target)) :
    FieldMaps Const Γ [source] [target] where
  output index := match index with
    | .vz => function
    | .vs impossible => nomatch impossible

theorem unary_subst {source target : Ty Base} (function : Term Const Γ (source ⇒ target))
    (images : Subst Const Γ Ξ) :
    (unary function).subst images = unary (subst images function) := by
  apply congrArg FieldMaps.mk
  funext type index
  cases index with
  | vz => rfl
  | vs impossible => nomatch impossible

def lower (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E) :
    InventoryMaps Const Γ (VectorTreeFieldEmbedding.storedSignature N E) (VectorTreeFieldEmbedding.rawSignature N A) :=
  .cons (unary given.decode) (.cons (FieldMaps.identity [N,N]) .nil)

def raise (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E) :
    InventoryMaps Const Γ (VectorTreeFieldEmbedding.rawSignature N A) (VectorTreeFieldEmbedding.storedSignature N E) :=
  .cons (unary given.encode) (.cons (FieldMaps.identity [N,N]) .nil)

theorem lower_subst (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E) (images : Subst Const Γ Ξ) :
    (lower given).subst images = lower (given.substitute images) := by
  simp only [lower,InventoryMaps.subst,unary_subst,FieldMaps.identity_subst,
    VectorTreeFieldEmbedding.Inputs.decode_subst]

theorem raise_subst (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E) (images : Subst Const Γ Ξ) :
    (raise given).subst images = raise (given.substitute images) := by
  simp only [raise,InventoryMaps.subst,unary_subst,FieldMaps.identity_subst,
    VectorTreeFieldEmbedding.Inputs.encode_subst]

def lowerProgram (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E) :=
  (lower given).program

def raiseProgram (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E) :=
  (raise given).program

theorem lowerProgram_subst (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E) (images : Subst Const Γ Ξ) :
    subst images (lowerProgram given) = lowerProgram (given.substitute images) := by
  rw [lowerProgram,InventoryMaps.program_subst,lower_subst]
  rfl

theorem raiseProgram_subst (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E) (images : Subst Const Γ Ξ) :
    subst images (raiseProgram given) = raiseProgram (given.substitute images) := by
  rw [raiseProgram,InventoryMaps.program_subst,raise_subst]
  rfl

#print axioms lower_subst
#print axioms raise_subst
#print axioms lowerProgram_subst
#print axioms raiseProgram_subst
end Mettapedia.Logic.HOL.VectorTreePayloadMaps
