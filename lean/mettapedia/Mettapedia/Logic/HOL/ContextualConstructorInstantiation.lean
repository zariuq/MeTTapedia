import Mettapedia.Logic.HOL.ContextualRecursiveSpaceProofs

/-!
# Instantiating a constructor's three retained scope variables

The tag, payload and child array replace their original bound variables.
Ambient variables follow the supplied substitution. Every constructor-frame
substitution factors through this construction without an injectivity premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    (signature : Contextual Const Γ)
    (images : Subst Const Γ Ξ)
    (tag : Term Const Ξ signature.number) (payload : Term Const Ξ signature.payload)
    (children : Term Const Ξ (signature.number ⇒ signature.space))

def constructorSubstitution : Subst Const signature.constructorContext Ξ :=
  Subst.cons children (Subst.cons payload (Subst.cons tag images))

theorem constructorSubstitution_ambient {type : Ty Base} (term : Term Const Γ type) :
    HOL.subst (signature.constructorSubstitution images tag payload children)
      (HOL.rename signature.constructorRenaming term) = HOL.subst images term := by
  rw [HOL.subst_rename]
  exact HOL.subst_ext (fun _ => rfl) term

theorem constructorSubstitution_weaken {type : Ty Base} (term : Term Const Γ type) :
    HOL.subst (signature.constructorSubstitution images tag payload children)
      (weaken (weaken (weaken term))) = HOL.subst images term := by
  rw [← signature.rename_constructorRenaming term]
  exact signature.constructorSubstitution_ambient images tag payload children term

theorem constructorScope_instantiate :
    signature.constructorScope.subst (signature.constructorSubstitution images tag payload children) = signature.subst images := by
  apply eq_of_fields
    (first := signature.constructorScope.subst (signature.constructorSubstitution images tag payload children))
    (second := signature.subst images) rfl rfl rfl
  all_goals
    apply heq_of_eq
    change HOL.subst (signature.constructorSubstitution images tag payload children)
      (HOL.subst (Subst.ofRename signature.constructorRenaming) _) = _
    rw [subst_ofRename, signature.constructorSubstitution_ambient]
    rfl

theorem constructorSubstitution_factor (whole : Subst Const signature.constructorContext Ξ) :
    @Eq (Subst Const signature.constructorContext Ξ)
      (signature.constructorSubstitution (fun entry => whole (signature.constructorRenaming entry))
        (whole (.vs (.vs .vz))) (whole (.vs .vz)) (whole .vz)) whole := by
  funext type entry
  cases entry with
  | vz => rfl
  | vs entry => cases entry with
    | vz => rfl
    | vs entry => cases entry with
      | vz => rfl
      | vs entry => rfl

#print axioms constructorSubstitution_ambient
#print axioms constructorScope_instantiate

end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
