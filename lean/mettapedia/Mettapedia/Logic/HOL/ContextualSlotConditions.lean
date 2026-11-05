import Mettapedia.Logic.HOL.IndexedChildHypotheses

/-!
# Named child-condition bodies and retained slot specialization

The named formula retains both active edge/membership obligations and inactive
padding. Specialization and its proof-fragment property are established with
the contextual signature and predicate still arbitrary.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  (signature : Contextual Const Γ) {Δ : List (Formula Const Γ)}

def slotConditions (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (slot : Term Const Γ signature.number) : Formula Const Γ :=
  .and
    (.imp (.app (.app signature.active payload) slot)
      (.and (.app (.app (.app signature.validEdge payload) slot) (.app children slot))
        (.app predicate (.app children slot))))
    (.imp (.not (.app (.app signature.active payload) slot))
      (.eq (.app children slot) signature.bottom))

def slotEvidence (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (slot : Term Const Γ signature.number)
    (conditions : ProofSyntax Const Δ (signature.childConditions predicate payload children)) :
    ProofSyntax Const Δ (signature.slotConditions predicate payload children slot) :=
  signature.childConditions_at predicate payload children slot conditions

theorem slotEvidence_free (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (slot : Term Const Γ signature.number)
    (conditions : ProofSyntax Const Δ (signature.childConditions predicate payload children))
    (free : conditions.FunctionExtensionalityFree) :
    (signature.slotEvidence predicate payload children slot conditions).FunctionExtensionalityFree :=
  signature.childConditions_at_free predicate payload children slot conditions free

#print axioms slotEvidence_free
end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
