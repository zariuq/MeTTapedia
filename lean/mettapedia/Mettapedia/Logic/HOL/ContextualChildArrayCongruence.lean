import Mettapedia.Logic.HOL.ContextualRecursiveSpaceProofs
import Mettapedia.Logic.HOL.ConstantExpansionProofsFree

/-!
# Pointwise congruence of complete child contracts

A retained equality at every original slot transports the whole child
condition: the active edge and predicate obligations, and the inactive bottom
padding equation. The proof compares observations at each slot and then
closes that same slot binder. It introduces neither eta nor whole-function
equality, and makes no assertion about a parent's arbitrary value observer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  (signature : Contextual Const Γ) {Δ : List (Formula Const Γ)}

@[irreducible] def childConditions_array_eq (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload)
    (first second : Term Const Γ (signature.number ⇒ signature.space))
    (pointwise : ProofSyntax Const Δ
      (.all (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz))))) :
    ProofSyntax Const Δ (.eq (signature.childConditions predicate payload first)
      (signature.childConditions predicate payload second)) :=
  let same := ContextualTrinity.instantiateFresh (pointwise.rename Rename.weaken)
  ContextualTrinity.allCongr
    (ProofSyntax.andCongr
      (ProofSyntax.impCongr (.eqRefl _)
        (ProofSyntax.andCongr (.eqAppArg _ same) (.eqAppArg _ same)))
      (ProofSyntax.impCongr (.eqRefl _) (ProofSyntax.eqCongr same (.eqRefl _))))

theorem childConditions_array_eq_free (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload)
    (first second : Term Const Γ (signature.number ⇒ signature.space))
    (pointwise : ProofSyntax Const Δ
      (.all (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz)))))
    (free : pointwise.FunctionExtensionalityFree) :
    (signature.childConditions_array_eq predicate payload first second pointwise).FunctionExtensionalityFree := by
  have sameFree := (ContextualTrinity.instantiateFresh_free _).mpr
    ((ProofSyntax.functionExtensionalityFree_rename _ _).mpr free)
  unfold childConditions_array_eq
  simp only [ContextualTrinity.allCongr_free,ProofSyntax.andCongr_free,ProofSyntax.impCongr_free,
    ProofSyntax.eqCongr_free,ProofSyntax.FunctionExtensionalityFree]
  exact ⟨⟨True.intro,⟨sameFree,sameFree⟩⟩,⟨True.intro,⟨sameFree,True.intro⟩⟩⟩

#print axioms childConditions_array_eq
#print axioms childConditions_array_eq_free

end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
