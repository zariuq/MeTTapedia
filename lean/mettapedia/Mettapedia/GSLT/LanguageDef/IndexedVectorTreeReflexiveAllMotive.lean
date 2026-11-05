import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeAllFromChildren

/-!
# Value-dependent reflexive evidence for an indexed induction motive

The witness for each element is that element itself. Original child values
are retained, with no fixed evidence value or proof-irrelevance principle.
The inclusion can strengthen an independently proved child contract through
child-predicate monotonicity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeReflexiveAllMotive
open Mettapedia.Logic Mettapedia.Logic.HOL
open FiniteConstructorEncoding CurriedPredicates PredicateFixedPoint
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {E : Ty Base}
  {Δ : List (Formula Const Γ)}

def motive : Term Const Γ (E ⇒ E ⇒ .prop) := .lam (.lam (.eq (.var (.vs .vz)) (.var .vz)))

@[simp] theorem motive_subst (images : Subst Const Γ Ξ) : HOL.subst images (motive (E := E)) = motive := rfl

theorem motive_rename (rho : Rename Base Γ Ξ) : HOL.rename rho (motive (Const := Const) (E := E)) = motive := rfl

@[irreducible] def motive_beta (point witness : Term Const Γ E) :
    ProofSyntax Const Δ (.eq (.app (.app motive point) witness) (.eq point witness)) := by
  apply ProofSyntax.castIndices rfl ?_ (CurriedGuardProgramProofs.beta2 (.eq (.var (.vs .vz)) (.var .vz)) point witness)
  simp only [motive,instantiate,HOL.subst,Subst.lift,Subst.single]
  rw [← weaken,PredicateFixedPoint.subst_single_weaken]

theorem motive_beta_free (point witness : Term Const Γ E) : (motive_beta (Δ := Δ) point witness).FunctionExtensionalityFree := by
  unfold motive_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

@[irreducible] def witnessed (point : Term Const Γ E) : ProofSyntax Const Δ (existsValue [] (.app motive point)) :=
  existsValue_intro [] (.app motive point) PUnit.unit point
    (.impE (.eqPropER (motive_beta point point)) (.eqRefl point))

theorem witnessed_free (point : Term Const Γ E) : (witnessed (Δ := Δ) point).FunctionExtensionalityFree := by
  unfold witnessed
  exact existsValue_intro_free _ _ _ _ _ ⟨motive_beta_free _ _,True.intro⟩

def property : Term Const Γ (E ⇒ .prop ⇒ .prop) := IndexedVectorTreeNativeAllFromChildren.indexedMotive motive

theorem property_rename (rho : Rename Base Γ Ξ) : HOL.rename rho (property (Const := Const) (E := E)) = property := by
  change HOL.rename rho (IndexedVectorTreeNativeAllFromChildren.indexedMotive motive) = _
  rw [← subst_ofRename,IndexedVectorTreeNativeAllFromChildren.indexedMotive_subst,motive_subst]
  rfl

@[irreducible] def propertyAt (point : Term Const Γ E) (index : Term Const Γ .prop) :
    ProofSyntax Const Δ (.app (.app property point) index) :=
  .impE (.eqPropER (IndexedVectorTreeNativeAllFromChildren.indexedMotive_beta motive point index)) (witnessed point)

theorem propertyAt_free (point : Term Const Γ E) (index : Term Const Γ .prop) :
    (propertyAt (Δ := Δ) point index).FunctionExtensionalityFree := by
  unfold propertyAt
  exact ⟨IndexedVectorTreeNativeAllFromChildren.indexedMotive_beta_free _ _ _,witnessed_free _⟩

theorem lift_rename (root : Term Const Γ (E ⇒ .prop ⇒ .prop)) (rho : Rename Base Γ Ξ) :
    HOL.rename rho (IndexedPredicateInduction.lift root property) =
      IndexedPredicateInduction.lift (HOL.rename rho root) property := by
  rw [IndexedPredicateInduction.rename_lift,property_rename]

@[irreducible] def liftAt (root : Term Const Γ (E ⇒ .prop ⇒ .prop)) (point : Term Const Γ E) :
    ProofSyntax Const Δ (.app (IndexedPredicateInduction.lift root property) point) := by
  apply ProofSyntax.impE (.eqPropER (IndexedPredicateInduction.lift_beta root property point))
  refine .allI (.impI ?_)
  apply ProofSyntax.castIndices rfl ?_ (propertyAt (weaken point) (.var .vz))
  simp only [weaken,property_rename]

theorem liftAt_free (root : Term Const Γ (E ⇒ .prop ⇒ .prop)) (point : Term Const Γ E) :
    (liftAt (Δ := Δ) root point).FunctionExtensionalityFree := by
  unfold liftAt
  refine ⟨IndexedPredicateInduction.lift_beta_free _ _ _,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact propertyAt_free _ _

@[irreducible] def inclusion (least : Term Const Γ (E ⇒ .prop)) (root : Term Const Γ (E ⇒ .prop ⇒ .prop)) :
    ProofSyntax Const Δ (included least (intersection least (IndexedPredicateInduction.lift root property))) := by
  refine .allI (.impI ?_)
  let antecedent := Term.app (weaken least) (.var .vz)
  have joined : ProofSyntax Const (antecedent :: weakenHyps Δ)
      (.app (intersection (weaken least) (IndexedPredicateInduction.lift (weaken root) property)) (.var .vz)) :=
    .impE (.eqPropER (intersection_beta (weaken least) (IndexedPredicateInduction.lift (weaken root) property) (.var .vz)))
      (.andI (.hyp 0) (liftAt (weaken root) (.var .vz)))
  apply ProofSyntax.castIndices rfl ?_ joined
  simp only [weaken,rename_intersection,lift_rename]

theorem inclusion_free (least : Term Const Γ (E ⇒ .prop)) (root : Term Const Γ (E ⇒ .prop ⇒ .prop)) :
    (inclusion (Δ := Δ) least root).FunctionExtensionalityFree := by
  unfold inclusion
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨intersection_beta_free _ _ _,True.intro,liftAt_free _ _⟩

#print axioms witnessed_free
#print axioms inclusion_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeReflexiveAllMotive
