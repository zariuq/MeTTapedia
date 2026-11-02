import Mettapedia.Logic.HOL.IndexedPredicateInduction
import Mettapedia.Logic.HOL.ContextualRecursiveSpaceProofs

/-!
# Indexed child hypotheses from the actual guarded condition

Specialization retains both active-child obligations and inactive padding.
At an active slot, the strengthened predicate supplies least membership and
the motive at every proved root index. Selecting an index still requires its
actual root proof; no uniqueness or functionality is inferred.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (signature : Contextual Const Γ) {assumptions : List (Formula Const Γ)}

def childConditions_at (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (slot : Term Const Γ signature.number)
    (conditions : ProofSyntax Const assumptions (signature.childConditions predicate payload children)) :
    ProofSyntax Const assumptions
      (.and
        (.imp (.app (.app signature.active payload) slot)
          (.and (.app (.app (.app signature.validEdge payload) slot) (.app children slot))
            (.app predicate (.app children slot))))
        (.imp (.not (.app (.app signature.active payload) slot))
          (.eq (.app children slot) signature.bottom))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE slot conditions)
  simp only [instantiate, HOL.subst, Subst.single,
    PredicateFixedPoint.subst_single_weaken]

theorem childConditions_at_free (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (slot : Term Const Γ signature.number)
    (conditions : ProofSyntax Const assumptions (signature.childConditions predicate payload children))
    (free : conditions.FunctionExtensionalityFree) :
    (signature.childConditions_at predicate payload children slot conditions).FunctionExtensionalityFree := by
  unfold childConditions_at
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact free

def indexedChildHypothesis {index : Ty Base}
    (root property : Term Const Γ (signature.space ⇒ index ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (slot : Term Const Γ signature.number) (target : Term Const Γ index)
    (conditions : ProofSyntax Const assumptions (signature.childConditions
      (PredicateFixedPoint.intersection signature.least (IndexedPredicateInduction.lift root property)) payload children))
    (active : ProofSyntax Const assumptions (.app (.app signature.active payload) slot))
    (rootProof : ProofSyntax Const assumptions (.app (.app root (.app children slot)) target)) :
    ProofSyntax Const assumptions
      (.and (.app (.app (signature.memberProgram root) (.app children slot)) target)
        (.app (.app property (.app children slot)) target)) := by
  let atSlot := signature.childConditions_at
    (PredicateFixedPoint.intersection signature.least (IndexedPredicateInduction.lift root property))
    payload children slot conditions
  let present := ProofSyntax.andER (ProofSyntax.impE (ProofSyntax.andEL atSlot) active)
  let invariant := ProofSyntax.impE (ProofSyntax.eqPropEL
    (PredicateFixedPoint.intersection_beta signature.least (IndexedPredicateInduction.lift root property)
      (.app children slot))) present
  exact .andI
    (.impE (.eqPropER (signature.member_beta root (.app children slot) target))
      (.andI (.andEL invariant) rootProof))
    (IndexedPredicateInduction.eliminate root property (.app children slot) target (.andER invariant) rootProof)

theorem indexedChildHypothesis_free {index : Ty Base}
    (root property : Term Const Γ (signature.space ⇒ index ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (slot : Term Const Γ signature.number) (target : Term Const Γ index)
    (conditions : ProofSyntax Const assumptions (signature.childConditions
      (PredicateFixedPoint.intersection signature.least (IndexedPredicateInduction.lift root property)) payload children))
    (active : ProofSyntax Const assumptions (.app (.app signature.active payload) slot))
    (rootProof : ProofSyntax Const assumptions (.app (.app root (.app children slot)) target))
    (conditionsFree : conditions.FunctionExtensionalityFree) (activeFree : active.FunctionExtensionalityFree)
    (rootFree : rootProof.FunctionExtensionalityFree) :
    (signature.indexedChildHypothesis root property payload children slot target conditions active rootProof).FunctionExtensionalityFree := by
  unfold indexedChildHypothesis
  have supplied := signature.childConditions_at_free _ payload children slot conditions conditionsFree
  have invariantFree : (ProofSyntax.impE (ProofSyntax.eqPropEL
      (PredicateFixedPoint.intersection_beta signature.least (IndexedPredicateInduction.lift root property)
        (.app children slot)))
      (ProofSyntax.andER (ProofSyntax.impE (ProofSyntax.andEL
        (signature.childConditions_at _ payload children slot conditions)) active))).FunctionExtensionalityFree :=
    ⟨PredicateFixedPoint.intersection_beta_free _ _ _, ⟨supplied, activeFree⟩⟩
  refine ⟨⟨signature.member_beta_free _ _ _, ⟨invariantFree, rootFree⟩⟩, ?_⟩
  exact IndexedPredicateInduction.eliminate_free _ _ _ _ _ _ invariantFree rootFree

#print axioms childConditions_at_free
#print axioms indexedChildHypothesis_free

end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
