import Mettapedia.Logic.HOL.IndexedChildHypotheses
import Mettapedia.Logic.HOL.PredicateFixedPointInduction
import Mettapedia.Logic.HOL.ConstantExpansionProofsFree

/-!
# Changing a child predicate through a proved inclusion

The original activity, edges, child values and inactive padding are retained.
Only the active member proof is transported through the supplied predicate
inclusion, under the same fresh slot and hypothesis occurrences.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  (signature : Contextual Const Γ) {Δ : List (Formula Const Γ)}

@[irreducible] def childConditions_mono (first second : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (included : ProofSyntax Const Δ (PredicateFixedPoint.included first second))
    (conditions : ProofSyntax Const Δ (signature.childConditions first payload children)) :
    ProofSyntax Const Δ (signature.childConditions second payload children) := by
  apply ProofSyntax.allI
  let child : Term Const (signature.number :: Γ) signature.space := .app (weaken children) (.var .vz)
  let active : Formula Const (signature.number :: Γ) := .app (.app (weaken signature.active) (weaken payload)) (.var .vz)
  let original := ContextualTrinity.instantiateFresh (conditions.rename Rename.weaken)
  let moved : ProofSyntax Const (weakenHyps (σ := signature.number) Δ)
      (PredicateFixedPoint.included (weaken first) (weaken second)) :=
    .castIndices rfl (PredicateFixedPoint.rename_included Rename.weaken first second) (included.rename Rename.weaken)
  let atChild : ProofSyntax Const (weakenHyps (σ := signature.number) Δ)
      (.imp (.app (weaken first) child) (.app (weaken second) child)) :=
    .castIndices rfl (PredicateFixedPoint.instantiate_included child (weaken first) (weaken second)) (.allE child moved)
  refine .andI (.impI (.andI ?_ ?_)) (.andER original)
  · exact .andEL (.impE (.andEL (original.prepend active)) (.hyp 0))
  · exact .impE (atChild.prepend active) (.andER (.impE (.andEL (original.prepend active)) (.hyp 0)))

theorem childConditions_mono_free (first second : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (included : ProofSyntax Const Δ (PredicateFixedPoint.included first second))
    (conditions : ProofSyntax Const Δ (signature.childConditions first payload children))
    (includedFree : included.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree) :
    (signature.childConditions_mono first second payload children included conditions).FunctionExtensionalityFree := by
  have originalFree := (ContextualTrinity.instantiateFresh_free _).mpr
    ((ProofSyntax.functionExtensionalityFree_rename _ _).mpr conditionsFree)
  unfold childConditions_mono
  refine ⟨⟨?_,?_,?_⟩,originalFree⟩
  · exact ⟨(ProofSyntax.functionExtensionalityFree_mono _ _).mpr originalFree,True.intro⟩
  · apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr includedFree
  · exact ⟨(ProofSyntax.functionExtensionalityFree_mono _ _).mpr originalFree,True.intro⟩

#print axioms childConditions_mono
#print axioms childConditions_mono_free
end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
