import Mettapedia.Logic.HOL.IndexedChildHypotheses
import Mettapedia.Logic.HOL.ConstantExpansionProofsFree

/-!
# Membership observations of active array positions

The original child condition entails membership at every active slot.
This projection retains the original activity predicate and array; it does
not recover edge or padding evidence in the reverse direction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ActiveArrayMembership
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {number element : Ty Base} {Δ : List (Formula Const Γ)}

def condition (predicate : Term Const Γ (element ⇒ .prop))
    (active : Term Const Γ (number ⇒ .prop)) (array : Term Const Γ (number ⇒ element)) : Formula Const Γ :=
  .all (.imp (.app (weaken active) (.var .vz))
    (.app (weaken predicate) (.app (weaken array) (.var .vz))))

@[simp] theorem condition_subst (images : Subst Const Γ Ξ)
    (predicate : Term Const Γ (element ⇒ .prop)) (active : Term Const Γ (number ⇒ .prop))
    (array : Term Const Γ (number ⇒ element)) :
    HOL.subst images (condition predicate active array) =
      condition (HOL.subst images predicate) (HOL.subst images active) (HOL.subst images array) := by
  simp only [condition, HOL.subst, subst_weaken, Subst.lift]

@[simp] theorem condition_rename (rho : Rename Base Γ Ξ)
    (predicate : Term Const Γ (element ⇒ .prop)) (active : Term Const Γ (number ⇒ .prop))
    (array : Term Const Γ (number ⇒ element)) :
    HOL.rename rho (condition predicate active array) =
      condition (HOL.rename rho predicate) (HOL.rename rho active) (HOL.rename rho array) := by
  simpa only [subst_ofRename] using condition_subst (Subst.ofRename rho) predicate active array

def atSlot (predicate : Term Const Γ (element ⇒ .prop)) (active : Term Const Γ (number ⇒ .prop))
    (array : Term Const Γ (number ⇒ element)) (slot : Term Const Γ number)
    (given : ProofSyntax Const Δ (condition predicate active array))
    (present : ProofSyntax Const Δ (.app active slot)) :
    ProofSyntax Const Δ (.app predicate (.app array slot)) := by
  have implication : ProofSyntax Const Δ (.imp (.app active slot) (.app predicate (.app array slot))) :=
    ProofSyntax.castIndices rfl (by
      simp only [instantiate, HOL.subst, Subst.single, PredicateFixedPoint.subst_single_weaken])
      (.allE slot given)
  exact .impE implication present

theorem atSlot_free (predicate : Term Const Γ (element ⇒ .prop)) (active : Term Const Γ (number ⇒ .prop))
    (array : Term Const Γ (number ⇒ element)) (slot : Term Const Γ number)
    (given : ProofSyntax Const Δ (condition predicate active array))
    (present : ProofSyntax Const Δ (.app active slot))
    (givenFree : given.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (atSlot predicate active array slot given present).FunctionExtensionalityFree := by
  simpa only [atSlot, ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.FunctionExtensionalityFree]
    using And.intro givenFree presentFree

def fromChildConditions (signature : RecursiveSpacePredicate.Contextual Const Γ)
    (predicate : Term Const Γ (signature.space ⇒ .prop)) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (given : ProofSyntax Const Δ (signature.childConditions predicate payload children)) :
    ProofSyntax Const Δ (condition predicate (.app signature.active payload) children) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  exact .andER (.impE (.andEL ((ContextualTrinity.instantiateFresh (given.rename Rename.weaken)).prepend _)) (.hyp 0))

theorem fromChildConditions_free (signature : RecursiveSpacePredicate.Contextual Const Γ)
    (predicate : Term Const Γ (signature.space ⇒ .prop)) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (given : ProofSyntax Const Δ (signature.childConditions predicate payload children))
    (free : given.FunctionExtensionalityFree) :
    (fromChildConditions signature predicate payload children given).FunctionExtensionalityFree := by
  unfold fromChildConditions
  refine ⟨?_, True.intro⟩
  apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
  apply (ContextualTrinity.instantiateFresh_free _).mpr
  exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr free

#print axioms fromChildConditions_free

end Mettapedia.Logic.HOL.ActiveArrayMembership
