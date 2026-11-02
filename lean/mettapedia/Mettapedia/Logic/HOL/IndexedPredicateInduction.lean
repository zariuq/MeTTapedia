import Mettapedia.Logic.HOL.PredicateFixedPointInduction

/-!
# Guarded induction with an explicit index-dependent motive

A unary least predicate can support an indexed motive when a separate root
relation supplies each index. The lifted motive quantifies over all such
indices; eliminating it uses the actual root proof. The layer-closure premise
remains explicit and is not replaced by an unindexed property.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedPredicateInduction
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {index space : Ty Base} {assumptions : List (Formula Const Γ)}

def lift (root property : Term Const Γ (space ⇒ index ⇒ .prop)) : Term Const Γ (space ⇒ .prop) :=
  .lam (.all (.imp
    (.app (.app (weaken (weaken root)) (.var (.vs .vz))) (.var .vz))
    (.app (.app (weaken (weaken property)) (.var (.vs .vz))) (.var .vz))))

@[simp] theorem subst_lift (theta : Subst Const Γ Ξ)
    (root property : Term Const Γ (space ⇒ index ⇒ .prop)) :
    HOL.subst theta (lift root property) = lift (HOL.subst theta root) (HOL.subst theta property) := by
  simp [lift, HOL.subst, subst_weaken, Subst.lift, Rename.weaken]

@[simp] theorem rename_lift (theta : Rename Base Γ Ξ)
    (root property : Term Const Γ (space ⇒ index ⇒ .prop)) :
    HOL.rename theta (lift root property) = lift (HOL.rename theta root) (HOL.rename theta property) := by
  simpa only [subst_ofRename] using subst_lift (Subst.ofRename theta) root property

def lift_beta (root property : Term Const Γ (space ⇒ index ⇒ .prop)) (point : Term Const Γ space) :
    ProofSyntax Const assumptions (.eq (.app (lift root property) point)
      (.all (.imp (.app (.app (weaken root) (weaken point)) (.var .vz))
        (.app (.app (weaken property) (weaken point)) (.var .vz))))) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta point
    (.all (.imp (.app (.app (weaken (weaken root)) (.var (.vs .vz))) (.var .vz))
      (.app (.app (weaken (weaken property)) (.var (.vs .vz))) (.var .vz)))))
  simp [lift, instantiate, HOL.subst, subst_weaken, Subst.single, Subst.lift]
  rfl

def eliminate (root property : Term Const Γ (space ⇒ index ⇒ .prop))
    (point : Term Const Γ space) (target : Term Const Γ index)
    (lifted : ProofSyntax Const assumptions (.app (lift root property) point))
    (rootProof : ProofSyntax Const assumptions (.app (.app root point) target)) :
    ProofSyntax Const assumptions (.app (.app property point) target) := by
  have every := ProofSyntax.impE (ProofSyntax.eqPropEL (lift_beta root property point)) lifted
  have specialized := ProofSyntax.allE target every
  apply ProofSyntax.impE (ProofSyntax.castIndices rfl ?_ specialized) rootProof
  simp only [instantiate, HOL.subst, PredicateFixedPoint.subst_single_weaken, Subst.single]

@[irreducible] def induction (operator : Term Const Γ (PredicateFixedPoint.Operator space))
    (root property : Term Const Γ (space ⇒ index ⇒ .prop))
    (point : Term Const Γ space) (target : Term Const Γ index)
    (order : ProofSyntax Const assumptions (PredicateFixedPoint.monotone operator))
    (step : ProofSyntax Const assumptions (PredicateFixedPoint.included
      (.app operator (PredicateFixedPoint.intersection (PredicateFixedPoint.least operator) (lift root property)))
      (lift root property)))
    (member : ProofSyntax Const assumptions (.app (PredicateFixedPoint.least operator) point))
    (rootProof : ProofSyntax Const assumptions (.app (.app root point) target)) :
    ProofSyntax Const assumptions (.app (.app property point) target) :=
  eliminate root property point target
    (PredicateFixedPoint.guarded_induction operator (lift root property) point order step member) rootProof

theorem lift_beta_free (root property : Term Const Γ (space ⇒ index ⇒ .prop)) (point : Term Const Γ space) :
    (lift_beta (assumptions := assumptions) root property point).FunctionExtensionalityFree := by
  unfold lift_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

theorem eliminate_free (root property : Term Const Γ (space ⇒ index ⇒ .prop))
    (point : Term Const Γ space) (target : Term Const Γ index)
    (lifted : ProofSyntax Const assumptions (.app (lift root property) point))
    (rootProof : ProofSyntax Const assumptions (.app (.app root point) target))
    (liftedFree : lifted.FunctionExtensionalityFree) (rootFree : rootProof.FunctionExtensionalityFree) :
    (eliminate root property point target lifted rootProof).FunctionExtensionalityFree := by
  unfold eliminate
  exact ⟨(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    ⟨lift_beta_free root property point, liftedFree⟩, rootFree⟩

theorem induction_free (operator : Term Const Γ (PredicateFixedPoint.Operator space))
    (root property : Term Const Γ (space ⇒ index ⇒ .prop))
    (point : Term Const Γ space) (target : Term Const Γ index)
    (order : ProofSyntax Const assumptions (PredicateFixedPoint.monotone operator))
    (step : ProofSyntax Const assumptions (PredicateFixedPoint.included
      (.app operator (PredicateFixedPoint.intersection (PredicateFixedPoint.least operator) (lift root property)))
      (lift root property)))
    (member : ProofSyntax Const assumptions (.app (PredicateFixedPoint.least operator) point))
    (rootProof : ProofSyntax Const assumptions (.app (.app root point) target))
    (orderFree : order.FunctionExtensionalityFree) (stepFree : step.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) (rootFree : rootProof.FunctionExtensionalityFree) :
    (induction operator root property point target order step member rootProof).FunctionExtensionalityFree := by
  unfold induction
  exact eliminate_free _ _ _ _ _ _
    (PredicateFixedPoint.guarded_induction_free _ _ _ _ _ _ orderFree stepFree memberFree) rootFree

#print axioms induction
#print axioms induction_free

end Mettapedia.Logic.HOL.IndexedPredicateInduction
