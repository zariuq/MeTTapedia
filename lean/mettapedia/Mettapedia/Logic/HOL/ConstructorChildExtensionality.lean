import Mettapedia.Logic.HOL.ContextualRecursiveSpaceProofs
import Mettapedia.Logic.HOL.FunctionExtensionalityEtaExpansion
import Mettapedia.Logic.HOL.CurriedExistentialElimination

/-!
# Parent observations under eta-licensed child-array equality

A pointwise reconstruction becomes equality of constructor values only
through the explicit eta-derived rule. Transport of an arbitrary parent
predicate retains that same license. These particular proof programs are
outside the existing eta/function-extensionality-free fragment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  (signature : Contextual Const Γ) {Δ : List (Formula Const Γ)}
  (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
  (first second : Term Const Γ (signature.number ⇒ signature.space))
  (pointwise : ProofSyntax Const Δ (.all (.eq (.app (weaken first) (.var .vz))
    (.app (weaken second) (.var .vz)))))

def constructorViaEta : ProofSyntax Const Δ
    (.eq (signature.constructValue tag payload first) (signature.constructValue tag payload second)) :=
  .eqAppArg (.app (.app signature.construct tag) payload) (ProofSyntax.funExtViaEta pointwise)

theorem constructorViaEta_not_free :
    ¬ (constructorViaEta signature tag payload first second pointwise).FunctionExtensionalityFree :=
  ProofSyntax.funExtViaEta_not_free pointwise

def parentViaEta (predicate : Term Const Γ (signature.space ⇒ .prop))
    (present : ProofSyntax Const Δ (.app predicate (signature.constructValue tag payload first))) :
    ProofSyntax Const Δ (.app predicate (signature.constructValue tag payload second)) :=
  .impE (.eqPropEL (.eqAppArg predicate (constructorViaEta signature tag payload first second pointwise))) present

theorem parentViaEta_not_free (predicate : Term Const Γ (signature.space ⇒ .prop))
    (present : ProofSyntax Const Δ (.app predicate (signature.constructValue tag payload first))) :
    ¬ (parentViaEta signature tag payload first second pointwise predicate present).FunctionExtensionalityFree := by
  intro free
  exact constructorViaEta_not_free signature tag payload first second pointwise free.1

def motiveExists {evidence : Ty Base} (motive : Term Const Γ (signature.space ⇒ evidence ⇒ .prop)) :
    Term Const Γ (signature.space ⇒ .prop) :=
  .lam (CurriedPredicates.existsValue [] (.app (weaken motive) (.var .vz)))

def motiveExists_apply {evidence : Ty Base} (motive : Term Const Γ (signature.space ⇒ evidence ⇒ .prop))
    (value : Term Const Γ signature.space) : ProofSyntax Const Δ
    (.eq (.app (motiveExists signature motive) value) (CurriedPredicates.existsValue [] (.app motive value))) := by
  apply ProofSyntax.castIndices rfl ?_
    (.beta value (CurriedPredicates.existsValue [] (.app (weaken motive) (.var .vz))))
  simp only [motiveExists,instantiate,CurriedPredicates.existsValue_subst,HOL.subst,Subst.single,
    PredicateFixedPoint.subst_single_weaken]

def parentExistsViaEta {evidence : Ty Base} (motive : Term Const Γ (signature.space ⇒ evidence ⇒ .prop))
    (present : ProofSyntax Const Δ
      (CurriedPredicates.existsValue [] (.app motive (signature.constructValue tag payload first)))) :
    ProofSyntax Const Δ (CurriedPredicates.existsValue [] (.app motive (signature.constructValue tag payload second))) :=
  .impE (.eqPropEL (motiveExists_apply signature motive (signature.constructValue tag payload second)))
    (parentViaEta signature tag payload first second pointwise (motiveExists signature motive)
      (.impE (.eqPropER (motiveExists_apply signature motive (signature.constructValue tag payload first))) present))

theorem parentExistsViaEta_not_free {evidence : Ty Base} (motive : Term Const Γ (signature.space ⇒ evidence ⇒ .prop))
    (present : ProofSyntax Const Δ
      (CurriedPredicates.existsValue [] (.app motive (signature.constructValue tag payload first)))) :
    ¬ (parentExistsViaEta signature tag payload first second pointwise motive present).FunctionExtensionalityFree := by
  intro free
  exact parentViaEta_not_free signature tag payload first second pointwise _ _ free.2

#print axioms constructorViaEta
#print axioms constructorViaEta_not_free
#print axioms parentViaEta_not_free
#print axioms parentExistsViaEta_not_free
end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
