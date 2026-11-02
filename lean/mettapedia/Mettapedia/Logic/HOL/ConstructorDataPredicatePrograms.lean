import Mettapedia.Logic.HOL.ConstructorDataPredicates

/-!
# Retained introduction at an identified constructor payload

The original payload need not be syntactically an encoding. Its actual
encoding equation and the selected row's field proof introduce the original
guard directly, retaining both pieces of evidence and the occurrence index.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.ConstructorDataPredicates
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {signature : List (List (Ty Base))} {Δ : List (Formula Const Γ)}

def introduceAt (conditions : Conditions Const Γ signature)
    (payload : Term Const Γ (payloadType signature)) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence))
    (allowed : ProofSyntax Const Δ (applyArguments _ (conditions occurrence) arguments))
    (same : ProofSyntax Const Δ (.eq payload (encode signature occurrence arguments))) :
    ProofSyntax Const Δ (guard signature conditions payload) := by
  let formulas := List.ofFn (fun selected => restrictedGuard signature selected (conditions selected) payload)
  let selected : Fin formulas.length := ⟨occurrence.val,by simpa only [formulas,List.length_ofFn] using occurrence.isLt⟩
  apply any_introAt formulas selected
  have branch : ProofSyntax Const Δ (restrictedGuard signature occurrence (conditions occurrence) payload) :=
    existsArguments_intro _ (restrictedPredicate signature occurrence (conditions occurrence) payload) arguments
      (.impE (.eqPropER (restrictedPredicate_beta signature occurrence (conditions occurrence) payload arguments))
        (.andI allowed same))
  exact .castIndices rfl (by simp only [formulas,selected,List.get_eq_getElem,List.getElem_ofFn]) branch

theorem introduceAt_free (conditions : Conditions Const Γ signature)
    (payload : Term Const Γ (payloadType signature)) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence))
    (allowed : ProofSyntax Const Δ (applyArguments _ (conditions occurrence) arguments))
    (same : ProofSyntax Const Δ (.eq payload (encode signature occurrence arguments)))
    (allowedFree : allowed.FunctionExtensionalityFree) (sameFree : same.FunctionExtensionalityFree) :
    (introduceAt conditions payload occurrence arguments allowed same).FunctionExtensionalityFree := by
  unfold introduceAt
  apply any_introAt_free
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply existsArguments_intro_free
  exact ⟨restrictedPredicate_beta_free _ _ _ _ _,allowedFree,sameFree⟩

#print axioms introduceAt
#print axioms introduceAt_free
end Mettapedia.Logic.HOL.ConstructorDataPredicates
