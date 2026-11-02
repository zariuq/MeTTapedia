import Mettapedia.Logic.HOL.ConstructorEdgeIntroduction
import Mettapedia.Logic.HOL.ConstructorRootSection
import Mettapedia.Logic.HOL.IndexedVectorPredicateMonotonicity

/-!
# Edges and membership from a joint child predicate

A supplied position guard and membership in the intersection of an element
predicate with the original root-index section concern the same child and
index. Their combination retains both the edge and element-membership facts.
No array implementation, index functionality or constructor injectivity is
assumed by this assembly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
open FiniteConstructorEncoding PredicateFixedPoint
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors)
    {space : Ty Base}
    (construct : Term Const Γ
      (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))
    {Δ : List (Formula Const Γ)}

def edgeAndMembership (elements : Term Const Γ (space ⇒ .prop))
    (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) (index : Term Const Γ constructors.index)
    (position : ProofSyntax Const Δ (positions.childGuard payload slot index))
    (member : ProofSyntax Const Δ (.app (intersection elements (constructors.rootAt construct index)) child)) :
    ProofSyntax Const Δ (.and (.app (.app (.app (positions.edgeProgram construct) payload) slot) child)
      (.app elements child)) :=
  let joined := ProofSyntax.impE (.eqPropEL (intersection_beta elements (constructors.rootAt construct index) child)) member
  .andI (positions.edgeProgramFromIndex construct payload slot child index position
    (constructors.rootAt_elim construct index child (.andER joined))) (.andEL joined)

theorem edgeAndMembership_free (elements : Term Const Γ (space ⇒ .prop))
    (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) (index : Term Const Γ constructors.index)
    (position : ProofSyntax Const Δ (positions.childGuard payload slot index))
    (member : ProofSyntax Const Δ (.app (intersection elements (constructors.rootAt construct index)) child))
    (positionFree : position.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (positions.edgeAndMembership construct elements payload slot child index position member).FunctionExtensionalityFree := by
  unfold edgeAndMembership
  have joinedFree := And.intro (intersection_beta_free (Δ := Δ) elements (constructors.rootAt construct index) child) memberFree
  exact ⟨positions.edgeProgramFromIndex_free _ _ _ _ _ _ _ positionFree
    (constructors.rootAt_elim_free _ _ _ _ joinedFree),joinedFree⟩

#print axioms edgeAndMembership_free
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
