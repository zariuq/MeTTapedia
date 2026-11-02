import Mettapedia.Logic.HOL.IndexedChildHypotheses

/-!
# Guarded child components before choosing an index witness

The active obligation yields its edge, least membership and lifted motive.
This generic decomposition keeps the concrete datatype's fixed-point syntax
out of proofs about how these three pieces are assembled.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (signature : Contextual Const Γ) {index : Ty Base}
    (root property : Term Const Γ (signature.space ⇒ index ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (slot : Term Const Γ signature.number) {assumptions : List (Formula Const Γ)}

def childComponents
    (conditions : ProofSyntax Const assumptions (signature.childConditions
      (PredicateFixedPoint.intersection signature.least (IndexedPredicateInduction.lift root property)) payload children))
    (active : ProofSyntax Const assumptions (.app (.app signature.active payload) slot)) :
    ProofSyntax Const assumptions
      (.and (.app (.app (.app signature.validEdge payload) slot) (.app children slot))
        (.and (.app signature.least (.app children slot))
          (.app (IndexedPredicateInduction.lift root property) (.app children slot)))) := by
  let present := ProofSyntax.impE (ProofSyntax.andEL (signature.childConditions_at
    (PredicateFixedPoint.intersection signature.least (IndexedPredicateInduction.lift root property))
    payload children slot conditions)) active
  exact .andI (.andEL present)
    (.impE (.eqPropEL (PredicateFixedPoint.intersection_beta signature.least
      (IndexedPredicateInduction.lift root property) (.app children slot))) (.andER present))

theorem childComponents_free
    (conditions : ProofSyntax Const assumptions (signature.childConditions
      (PredicateFixedPoint.intersection signature.least (IndexedPredicateInduction.lift root property)) payload children))
    (active : ProofSyntax Const assumptions (.app (.app signature.active payload) slot))
    (conditionsFree : conditions.FunctionExtensionalityFree) (activeFree : active.FunctionExtensionalityFree) :
    (signature.childComponents root property payload children slot conditions active).FunctionExtensionalityFree := by
  unfold childComponents
  have atFree := signature.childConditions_at_free _ payload children slot conditions conditionsFree
  exact ⟨⟨atFree, activeFree⟩, ⟨PredicateFixedPoint.intersection_beta_free _ _ _, ⟨atFree, activeFree⟩⟩⟩

#print axioms childComponents_free

end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
